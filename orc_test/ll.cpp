
#include <iostream>

#include "llvm/Bitcode/BitcodeReader.h"
#include "llvm/ExecutionEngine/Orc/JITTargetMachineBuilder.h"
#include "llvm/ExecutionEngine/SectionMemoryManager.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Mangler.h"
#include "llvm/Support/SmallVectorMemoryBuffer.h"

#include "clang/Frontend/CompilerInstance.h"
#include "clang/CodeGen/CodeGenAction.h"

using namespace std::chrono;
using namespace llvm;

static
DataLayout getProcessDataLayout(llvm::orc::JITTargetMachineBuilder& jtmb) {

    auto TM = jtmb.createTargetMachine();
    if (!TM) {
	printf("!TM\n");
	Error e = TM.takeError();
	outs() << "Get datalayout error: " << e;
	exit(-1);
    }

    return DataLayout((*TM)->createDataLayout());
}

// Get the mangled name according to data layout.
static
std::string getMangledName(const DataLayout& DL, StringRef name) {
   std::string r;
   {
       raw_string_ostream MangledNameStream(r);
       Mangler::getNameWithPrefix(MangledNameStream, name, DL);
   }
   return r;
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
std::unique_ptr<MemoryBuffer> fromFile(const char* path) {
    llvm::ErrorOr<std::unique_ptr<MemoryBuffer>> MBOrErr = MemoryBuffer::getFile(path);

    if (!MBOrErr)  {
	printf("Could not open %s\n", path);
	exit(-1);
    }

    return std::move(MBOrErr.get());
}

static
std::unique_ptr<llvm::Module> getModule(LLVMContext* ctx, const char* path) {
    std::unique_ptr<MemoryBuffer> b = fromFile(path);

    Expected< std::unique_ptr< Module > > mr = parseBitcodeFile(b->getMemBufferRef(), *ctx);
    if (!mr) {
	printf("Loading module failed");
	exit(-1);
    }
    return std::move(*mr);
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
    std::unique_ptr< llvm::Module > modPtr = act.takeModule();
    return std::move(modPtr);
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

using sym_map = std::map<std::string, JITEvaluatedSymbol>;

class eager_resolver : public JITSymbolResolver {
    eager_resolver(eager_resolver&) = delete;
public:
    eager_resolver(sym_map& symMap) : symMap(symMap) {}

    void lookup(const LookupSet &symbols, OnResolvedFunction onResolved) override {
	std::map< StringRef, JITEvaluatedSymbol > result;

	for (auto internName : symbols) {
	    std::string nm(internName);

	    auto i = symMap.find(nm);
	    if (i == symMap.end()) {
		std::cerr << "Failed to find " << nm << std::endl;
		exit(-1);
	    }
	    result.insert(std::make_pair(internName, i->second));
	}
	onResolved(result);
    }

    Expected<LookupSet> getResponsibilitySet(const LookupSet& symbols) override {
	return symbols;
    }
private:
    sym_map& symMap;
};

typedef std::unique_ptr<llvm::Module> (*moduleFn)(llvm::LLVMContext* ctx, const char* path);

class jit_linker {
public:
    jit_linker()
	: jtmb(Triple(sys::getProcessTriple()))
	, dl(getProcessDataLayout(jtmb))
	, memMgrs() {
    }


    void addObjectFile(const char* path) {
	addObjBuffer(std::move(fromFile(path)));

    }

    void addModule(const char* path, moduleFn f) {
	auto ctx = std::make_unique<LLVMContext>();
	auto m = f(ctx.get(), path);


	auto TM = cantFail(jtmb.createTargetMachine());

	SmallVector<char, 0> ObjBufferSV;
	{
	    raw_svector_ostream ObjStream(ObjBufferSV);

	    legacy::PassManager PM;
	    MCContext *Ctx;
	    if (TM->addPassesToEmitMC(PM, Ctx, ObjStream))
		llvm_unreachable("Target does not support MC emission.");
	    PM.run(*m);
	}

	auto objBuffer = llvm::make_unique<SmallVectorMemoryBuffer>(std::move(ObjBufferSV));

	addObjBuffer(std::move(objBuffer));
    }

    JITEvaluatedSymbol lookup(const std::string& initName) {
	auto nm = getMangledName(dl, initName);

	auto i = symMap.find(nm);
	if (i == symMap.end()) {
	    std::cerr << "Failed to find " << nm << std::endl;
	    exit(-1);
	}
	return i->second;
    }


private:
    llvm::orc::JITTargetMachineBuilder jtmb;
    DataLayout dl;
    std::vector<std::unique_ptr<RuntimeDyld::MemoryManager>> memMgrs;

    sym_map symMap;

    void addObjBuffer(std::unique_ptr<MemoryBuffer> objBuffer) {
	auto obj = object::ObjectFile::createObjectFile(*objBuffer);

	if (!obj) {
	    exitWithError(obj.takeError());
	}


	std::unique_ptr< MemoryBuffer > underlyingBuffer;

	auto Tmp = std::make_unique<SectionMemoryManager>(); ;

	RuntimeDyld::MemoryManager* memMgr = nullptr;

	// Record a memory manager for this object.
	{
	    auto tmp = std::make_unique<SectionMemoryManager>();
	    memMgrs.push_back(std::move(tmp));
	    memMgr = memMgrs.back().get();
	}


	eager_resolver resolver(symMap);

	RuntimeDyld rtDyld(*memMgr, resolver);
	std::unique_ptr<LoadedObjectInfo> Info = rtDyld.loadObject(**obj);


	if (rtDyld.hasError()) {
	    Error e = make_error<StringError>(rtDyld.getErrorString(), inconvertibleErrorCode());
	    exitWithError(std::move(e));
	}

	rtDyld.finalizeWithMemoryManagerLocking();

	for (const std::pair<StringRef, JITEvaluatedSymbol>& kv : rtDyld.getSymbolTable()) {
	    std::string nm(kv.first);
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

    jit_linker jl;

    const auto begin = high_resolution_clock::now();

    //jl.addObjectFile("add.o");

    jl.addModule("add.cpp", compileCPP);
    jl.addModule("fib.c", compileC);

    JITEvaluatedSymbol sym = jl.lookup("fib");

    auto fib = (fib_fn) sym.getAddress();

    // Get time to add
    auto time = high_resolution_clock::now() - begin;

    for (uint64_t i = 0; i != 10; ++i) {
	printf("fib(%llu) = %llu\n", i, fib(i));
    }

    std::cout << "Elapsed time: " << duration<double, std::milli>(time).count() << ".\n";

    return 0;
}
