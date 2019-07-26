#include <iostream>

#include "llvm/Bitcode/BitcodeReader.h"
#include "llvm/ExecutionEngine/SectionMemoryManager.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Mangler.h"
#include "llvm/Support/SmallVectorMemoryBuffer.h"
#include "llvm/Support/TargetRegistry.h"
#include "llvm/Target/TargetMachine.h"

#include "clang/Frontend/CompilerInstance.h"
#include "clang/CodeGen/CodeGenAction.h"

using namespace std::chrono;
using namespace llvm;

/**
 * This creates a target machine for the current process by looking up
 * the target in the TargetRegistry.
 */
llvm::TargetMachine* mkTargetMachine(const llvm::Target* tgtPtr, const std::string& procTriple) {

    TargetOptions options;
    // JHx note: Not sure if we need these, but ORC sets them.
    options.EmulatedTLS = true;
    options.ExplicitEmulatedTLS = true;

    Optional<Reloc::Model> RM;
    Optional<CodeModel::Model> CM;
    CodeGenOpt::Level optLevel = CodeGenOpt::None;

    TargetMachine * tm = tgtPtr->createTargetMachine(procTriple, "", "", options, RM, CM, optLevel, true);
    if (!tm) {
	std::cerr << "Could not make target machine." << std::endl;
	exit(-1);
    }
    return tm;
}

// Exit with an error message.
static
void exitWithError(llvm::Error e) __attribute__((noreturn));

void exitWithError(llvm::Error e) {
    std::string msg;
    handleAllErrors(std::move(e), [&](llvm::ErrorInfoBase &eib) {
        msg = eib.message();
    });
    std::cerr << "Error: " << msg << std::endl;
    exit(-1);
}

static
std::unique_ptr<llvm::Module>
compile(llvm::LLVMContext* ctx,
	const char *const * args,
	const char *const * argEnd) {


    IntrusiveRefCntPtr<clang::DiagnosticIDs > diags(new clang::DiagnosticIDs());
    IntrusiveRefCntPtr<clang::DiagnosticOptions > diagOpts(new clang::DiagnosticOptions());

    clang::DiagnosticsEngine diagEngine(diags, diagOpts);

    std::shared_ptr<clang::CompilerInvocation> invocation(new clang::CompilerInvocation());
    clang::CompilerInvocation::CreateFromArgs(*invocation, args, argEnd, diagEngine);

    // Create the compiler instance
    clang::CompilerInstance instance;
    instance.setInvocation(invocation);

    instance.createDiagnostics();
    if (!instance.hasDiagnostics()) {
	std::cerr << "Compiled diagnostics failed" << std::endl;
	exit(-1);
    }

    // Generate LLVM using the compiler.
    clang::EmitLLVMOnlyAction act(ctx);
    if (!instance.ExecuteAction(act)) {
	std::cerr << "Action failed!" << std::endl;
	exit(-1);
    }
    return act.takeModule();
}

static
std::unique_ptr<llvm::Module> compileC(llvm::LLVMContext* ctx, const char* path) {
    const char * args[] = { path };
    const char *const * argEnd = args + sizeof(args) / sizeof(args[0]);
    return compile(ctx, args, argEnd);
}

static
std::unique_ptr<llvm::Module> compileCPP(llvm::LLVMContext* ctx, const char* path) {
    const char * args[] = { path, "-stdlib=libc++" };
    const char *const * argEnd = args + sizeof(args) / sizeof(args[0]);
    return compile(ctx, args, argEnd);
}

using sym_map = std::unordered_map<std::string, JITEvaluatedSymbol>;

/** Strip the global prefix from a symbol. */
std::string stripGlobalPrefix(char globalPrefix, const StringRef& internName) {
    const char* nmPtr = internName.begin();
    size_t nmSize = internName.size();

    if (globalPrefix) {
	if (*nmPtr != globalPrefix) {
	    std::cerr << "Unexpected name " << std::string(nmPtr, nmSize) << std::endl;
	    exit(-1);
	}
	nmPtr++; --nmSize;
    }

    return std::string(nmPtr, nmSize);
}

using moduleFn = std::unique_ptr<llvm::Module>(llvm::LLVMContext* ctx, const char* path);

// This provides the main interface to the JIT.
// It eagerly
class jit_linker : private llvm::JITSymbolResolver {

public:
    jit_linker(const llvm::Target* tgtPtr, const std::string& procTriple)
	: tm(mkTargetMachine(tgtPtr, procTriple)),
	  globalPrefix(tm->createDataLayout().getGlobalPrefix()),
	  memMgrs() {
    }

    // Load an object file from a file, and link it in.
    void addObjectFile(const char* path) {
	llvm::ErrorOr<std::unique_ptr<MemoryBuffer>> MBOrErr = MemoryBuffer::getFile(path);
	if (!MBOrErr)  {
	    printf("Could not open %s\n", path);
	    exit(-1);
	}
	addObjBuffer(std::move(MBOrErr.get()));
    }

    // Load a LLVM module using the given function, compile, and link it in.
    void addModule(const char* path, moduleFn f) {
	auto ctx = std::make_unique<LLVMContext>();
	auto m = f(ctx.get(), path);

	// Compile LLVM module to
	SmallVector<char, 0> ObjBufferSV;
	{
	    raw_svector_ostream ObjStream(ObjBufferSV);

	    legacy::PassManager PM;
	    MCContext *Ctx;
	    if (tm->addPassesToEmitMC(PM, Ctx, ObjStream)) {
		llvm_unreachable("Target does not support MC emission.");
	    }
	    PM.run(*m);
	}

	auto objBuffer = std::make_unique<SmallVectorMemoryBuffer>(std::move(ObjBufferSV));

	addObjBuffer(std::move(objBuffer));
    }

    JITEvaluatedSymbol lookup(const std::string& nm) {
	auto i = symMap.find(nm);
	if (i == symMap.end()) {
	    std::cerr << "Failed to find " << nm << std::endl;
	    exit(-1);
	}
	return i->second;
    }
private:
    /// A target machine value for compiling LLVM to machine code.
    std::unique_ptr<llvm::TargetMachine> tm;

    /// Prefix to append to symbol names (or 0 for no prefix)
    char globalPrefix;

    /// Holds memory managers created so far.
    std::vector<std::unique_ptr<llvm::SectionMemoryManager>> memMgrs;

    /// Map from symbol names to sets.
    sym_map symMap;

    Expected<LookupSet> getResponsibilitySet(const LookupSet& symbols) override {
	// This is called with the common and weak symbols in the binary, and we
	// should return the ones we want the loader to load.
	//
	// My current assumption is that Lean will not generate any
	// common or weak symbols, and so we should just error if the
	// binary contains them.
	if (symbols.size() != 0) {
	    std::cerr << "Unexpected common/weak symbols in binary." << std::endl;
	    exit(-1);
	}
	return LookupSet();
    }


    void lookup(const llvm::JITSymbolResolver::LookupSet &symbols,
		llvm::JITSymbolResolver::OnResolvedFunction onResolved) override {
	std::map< StringRef, JITEvaluatedSymbol > result;

	for (const StringRef& internName : symbols) {
	    std::string nm = stripGlobalPrefix(globalPrefix, internName);

	    auto i = symMap.find(nm);
	    if (i == symMap.end()) {
		std::cerr << "Failed to find " << nm << std::endl;
		exit(-1);
	    }
	    result.insert(std::make_pair(internName, i->second));
	}
	onResolved(std::move(result));
    }


    void addObjBuffer(std::unique_ptr<MemoryBuffer> objBuffer) {
	auto obj = object::ObjectFile::createObjectFile(*objBuffer);

	if (!obj) {
	    exitWithError(obj.takeError());
	}


	std::unique_ptr< MemoryBuffer > underlyingBuffer;


	// Record a memory manager for this object.
	memMgrs.push_back(std::make_unique<SectionMemoryManager>());
	RuntimeDyld::MemoryManager& memMgr  = *memMgrs.back();

	// Create classes for loading
	//eager_resolver resolver([this](auto s, auto on) {this->lookup(std::move(s), std::move(on));});
	RuntimeDyld rtDyld(memMgr, *this);

	// Load object
	std::unique_ptr<LoadedObjectInfo> Info = rtDyld.loadObject(**obj);

	// Check for error.
	if (rtDyld.hasError()) {
	    Error e = make_error<StringError>(rtDyld.getErrorString(), inconvertibleErrorCode());
	    exitWithError(std::move(e));
	}

	// Finalize and find new symbols
	rtDyld.finalizeWithMemoryManagerLocking();
	for (const std::pair<StringRef, JITEvaluatedSymbol>& kv : rtDyld.getSymbolTable()) {
	    std::string nm = stripGlobalPrefix(globalPrefix, kv.first);
	    auto r = symMap.insert(std::make_pair(nm, kv.second));
	    if (!r.second) {
		std::cerr << "Already inserted " << nm << std::endl;
		exit(-1);
	    }
	}
    }
};

typedef uint64_t (*add_fn)(uint64_t, uint64_t);
typedef uint64_t (*fib_fn)(uint64_t);

int main(int argc, const char** argv) {
    LLVMInitializeX86TargetInfo();
    LLVMInitializeX86TargetMC();
    LLVMInitializeX86Target();
    LLVMInitializeX86AsmPrinter();

    std::string procTriple = sys::getProcessTriple();

    std::string errMsg;
    const Target* tgtPtr = llvm::TargetRegistry::lookupTarget(procTriple, errMsg);
    if (!tgtPtr) {
	std::cerr << "Could not find target." << std::endl;
	exit(-1);
    }

    jit_linker jl(tgtPtr, procTriple);

    const auto begin = high_resolution_clock::now();

    //jl.addObjectFile("add.o");
    jl.addModule("add.cpp", compileCPP);
    jl.addModule("fib.c", compileC);

    auto fib = (fib_fn) jl.lookup("fib").getAddress();

    // Get time this took
    auto time = high_resolution_clock::now() - begin;

    // Invoke fib to make sure it works.
    for (uint64_t i = 0; i != 10; ++i) {
	printf("fib(%llu) = %llu\n", i, fib(i));
    }

    std::cout << "Elapsed time: " << duration<double, std::milli>(time).count() << ".\n";
    return 0;
}
