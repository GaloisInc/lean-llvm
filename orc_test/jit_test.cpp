#include <iostream>
#include <stdlib.h>

#include <llvm/ExecutionEngine/SectionMemoryManager.h>
#include <llvm/IR/LegacyPassManager.h>
#include <llvm/IR/Module.h>
#include <llvm/Support/SmallVectorMemoryBuffer.h>
#include <llvm/Support/TargetRegistry.h>
#include <llvm/Target/TargetMachine.h>

#include <clang/Basic/CodeGenOptions.h>
#include <clang/Basic/MemoryBufferCache.h>
#include <clang/CodeGen/ModuleBuilder.h>
#include <clang/Frontend/FrontendOptions.h>
#include <clang/Frontend/TextDiagnosticPrinter.h>
#include <clang/Frontend/Utils.h>
#include <clang/Lex/HeaderSearch.h>
#include <clang/Lex/HeaderSearchOptions.h>
#include <clang/Lex/Preprocessor.h>
#include <clang/Lex/PreprocessorOptions.h>
#include <clang/Parse/ParseAST.h>
#include <clang/Sema/Sema.h>
#include <clang/Serialization/PCHContainerOperations.h>

namespace {

/**
 * This creates a target machine for the current process by looking up
 * the target in the TargetRegistry.
 */
static
llvm::TargetMachine* mkTargetMachine(const llvm::Target* tgtPtr, const std::string& procTriple) {

    llvm::TargetOptions options;
    // JHx note: Not sure if we need these, but ORC sets them.
    options.EmulatedTLS = true;
    options.ExplicitEmulatedTLS = true;

    llvm::Optional<llvm::Reloc::Model> RM;
    llvm::Optional<llvm::CodeModel::Model> CM;
    llvm::CodeGenOpt::Level optLevel = llvm::CodeGenOpt::None;

    llvm::TargetMachine * tm = tgtPtr->createTargetMachine(procTriple, "", "", options, RM, CM, optLevel, true);
    if (!tm) {
	std::cerr << "Could not make target machine." << std::endl;
	exit(-1);
    }
    return tm;
}

/// Turn a LLVM error into a string error mesage.
static
std::string getErrorMsg(llvm::Error e) {
    std::string msg;
    llvm::handleAllErrors(std::move(e), [&](llvm::ErrorInfoBase &eib) {
					    msg = eib.message();
					});
    return msg;
}

}

/// Run clang on the file at the given path.
static
std::unique_ptr<llvm::Module>
runClang(llvm::LLVMContext* ctx,
         const char* path,
         bool isCXX) {

    // Set language options
    clang::LangOptions langOpts;
    auto headerSearchOptsPtr = std::make_shared<clang::HeaderSearchOptions>();
    if (isCXX) {
	langOpts.CPlusPlus = 1;
	headerSearchOptsPtr->UseLibcxx = 1;
    }


    // Options we do not change.
    auto  preprocessorOptsPtr = std::make_shared<clang::PreprocessorOptions>();
    clang::CodeGenOptions codeGenOpts;
    clang::FileSystemOptions fileSystemOpts;
    clang::FrontendOptions frontendOpts;

    // Create diagnostics with logging to log.
    std::string log;
    llvm::IntrusiveRefCntPtr<clang::DiagnosticOptions> diagnosticOpts(new clang::DiagnosticOptions());
    diagnosticOpts->ShowCarets = 0;
    llvm::raw_string_ostream s_log(log);
    clang::TextDiagnosticPrinter dc(s_log, diagnosticOpts.get(), false);

    llvm::IntrusiveRefCntPtr<clang::DiagnosticIDs> DiagID(new clang::DiagnosticIDs());
    clang::DiagnosticsEngine diagnostics(DiagID, diagnosticOpts);
    diagnostics.setClient(&dc, false);

    // Compilation target options
    auto targetOptionsPtr = std::make_shared<clang::TargetOptions>();
    targetOptionsPtr->Triple = llvm::sys::getProcessTriple();
    llvm::IntrusiveRefCntPtr<clang::TargetInfo> target =
        clang::TargetInfo::CreateTargetInfo(diagnostics, targetOptionsPtr);
    target->adjust(langOpts);


    // Create file system that is just backed by real file system.
    clang::FileManager fileMgr(fileSystemOpts, llvm::vfs::getRealFileSystem());

    // Create source manager
    clang::SourceManager sourceMgr(diagnostics, fileMgr);


    clang::MemoryBufferCache PCMCache;
    clang::TrivialModuleLoader ml;

    // Create the Preprocessor.
    clang::HeaderSearch headerInfo(headerSearchOptsPtr, sourceMgr, diagnostics, langOpts, target.get());
    clang::Preprocessor pp(preprocessorOptsPtr,
                           diagnostics,
                           langOpts,
                           sourceMgr,
                           PCMCache,
                           headerInfo,
                           ml,
                           nullptr, // IdentifierInfoLookup
                           false, // OwnsHeaderSearch
                           clang::TU_Complete);
    pp.Initialize(*target, nullptr);
    clang::RawPCHContainerReader reader;
    InitializePreprocessor(pp, *preprocessorOptsPtr, reader, frontendOpts);

    // Initialize the header search object.
    ApplyHeaderSearchOptions(headerInfo,
                             *headerSearchOptsPtr,
                             langOpts,
                             target->getTriple());

    // Inform the diagnostic client we are processing a source file.
    dc.BeginSourceFile(langOpts, &pp);

    // Initialize the main file entry.
    const clang::FileEntry *file = fileMgr.getFile(path, true);
    if (!file) {
	std::cerr << "Could not open " << path << std::endl;
	exit(-1);
    }

    sourceMgr.setMainFileID(sourceMgr.createFileID(file, clang::SourceLocation(), clang::SrcMgr::C_User));

    // Add a module declaration scope so that modules from -fmodule-map-file
    // arguments may shadow modules found implicitly in search paths.
    //headerInfo.getModuleMap().finishModuleDeclarationScope();
    pp.getBuiltinInfo().initializeBuiltins(pp.getIdentifierTable(), langOpts);

    clang::ASTContext astCtx(langOpts, sourceMgr,
                             pp.getIdentifierTable(),
                             pp.getSelectorTable(),
                             pp.getBuiltinInfo());
    astCtx.InitBuiltinTypes(*target, nullptr);

    std::unique_ptr<clang::CodeGenerator> consumer(
        CreateLLVMCodeGen(diagnostics, path,
                          *headerSearchOptsPtr,
                          *preprocessorOptsPtr,
                          codeGenOpts,
                          *ctx,
                          nullptr));
    consumer->Initialize(astCtx);

    clang::Sema sema(pp, astCtx, *consumer, clang::TU_Complete, nullptr);
    ParseAST(sema, false, false);

    // Inform the diagnostic client we are done with this source file.
    dc.EndSourceFile();
    // Inform the preprocessor we are done.
    pp.EndSourceFile();
    // Notify the diagnostic client that all files were processed.
    dc.finish();
    if (dc.getNumErrors() != 0) {
	std::cerr << "Error:" << log << std::endl;
	exit(-1);
    }
    //    return consumer.takeModule();
    return std::unique_ptr<llvm::Module>(consumer->ReleaseModule());
}

static
std::unique_ptr<llvm::Module> compileC(llvm::LLVMContext* ctx, const char* path) {
    return runClang(ctx, path, false);
}

static
std::unique_ptr<llvm::Module> compileCPP(llvm::LLVMContext* ctx, const char* path) {
    return runClang(ctx, path, true);
}

using sym_map = std::unordered_map<std::string, llvm::JITEvaluatedSymbol>;

/** Strip the global prefix from a symbol. */
static
std::string stripGlobalPrefix(char globalPrefix, const llvm::StringRef& internName) {
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
    std::string addObjectFile(const char* path) {
	llvm::ErrorOr<std::unique_ptr<llvm::MemoryBuffer>> MBOrErr = llvm::MemoryBuffer::getFile(path);
	if (!MBOrErr)  {
	    printf("Could not open %s\n", path);
	    exit(-1);
	}
	return addObjBuffer(std::move(MBOrErr.get()));
    }

    // Load a LLVM module using the given function, compile, and link it in.
    std::string addModule(const char* path, moduleFn f) {
	auto ctx = std::make_unique<llvm::LLVMContext>();
	auto m = f(ctx.get(), path);
	if (!m) {
	    return "Compilation failed.";
	}

	// Compile LLVM module to
        llvm::SmallVector<char, 0> ObjBufferSV;
	{
            llvm::raw_svector_ostream ObjStream(ObjBufferSV);

            llvm::legacy::PassManager PM;
            llvm::MCContext *Ctx;
	    if (tm->addPassesToEmitMC(PM, Ctx, ObjStream)) {
		llvm_unreachable("Target does not support MC emission.");
	    }
	    PM.run(*m);
	}

	auto objBuffer = std::make_unique<llvm::SmallVectorMemoryBuffer>(std::move(ObjBufferSV));

	return addObjBuffer(std::move(objBuffer));
    }

    llvm::JITEvaluatedSymbol lookup(const std::string& nm) {
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

    llvm::Expected<LookupSet> getResponsibilitySet(const LookupSet& symbols) override {
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
	std::map<llvm::StringRef, llvm::JITEvaluatedSymbol> result;

	for (const llvm::StringRef& internName : symbols) {
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


    std::string addObjBuffer(std::unique_ptr<llvm::MemoryBuffer> objBuffer) {
	auto obj = llvm::object::ObjectFile::createObjectFile(*objBuffer);
	if (!obj) {
	    return getErrorMsg(obj.takeError());
	}

	std::unique_ptr<llvm::MemoryBuffer> underlyingBuffer;


	// Record a memory manager for this object.
	memMgrs.push_back(std::make_unique<llvm::SectionMemoryManager>());
        llvm::RuntimeDyld::MemoryManager& memMgr  = *memMgrs.back();

	// Create classes for loading
	//eager_resolver resolver([this](auto s, auto on) {this->lookup(std::move(s), std::move(on));});
        llvm::RuntimeDyld rtDyld(memMgr, *this);

	// Load object
	std::unique_ptr<llvm::LoadedObjectInfo> Info = rtDyld.loadObject(**obj);

	// Check for error.
	if (rtDyld.hasError()) {
            llvm::Error e = llvm::make_error<llvm::StringError>(rtDyld.getErrorString(),
                                                                llvm::inconvertibleErrorCode());
	    return getErrorMsg(std::move(e));
	}

	// Finalize and find new symbols
	rtDyld.finalizeWithMemoryManagerLocking();
	auto symTab = rtDyld.getSymbolTable();
	auto end = symTab.end();
	for (auto i = symTab.begin(); i != end; ++i) {
	    std::string nm = stripGlobalPrefix(globalPrefix, i->first);
	    auto r = symMap.insert(std::make_pair(nm, i->second));
	    if (!r.second) {
		for (auto j = symTab.begin(); j != i; ++j) {
		    symMap.erase(j->first);
		}
		std::cerr << "Already inserted " << nm << std::endl;
		exit(-1);
	    }
	}
	return "";
    }
};

typedef uint64_t (*add_fn)(uint64_t, uint64_t);
typedef uint64_t (*fib_fn)(uint64_t);

void checkForError(std::string msg) {
    if (!msg.empty()) {
	std::cerr << msg << std::endl;
	exit(-1);
    }
}

int main(int argc, const char** argv) {
    LLVMInitializeX86TargetInfo();
    LLVMInitializeX86TargetMC();
    LLVMInitializeX86Target();
    LLVMInitializeX86AsmPrinter();

    std::string procTriple = llvm::sys::getProcessTriple();

    std::string errMsg;
    const llvm::Target* tgtPtr = llvm::TargetRegistry::lookupTarget(procTriple, errMsg);
    if (!tgtPtr) {
	std::cerr << "Could not find target: " << errMsg << std::endl;
	exit(-1);
    }

    jit_linker jl(tgtPtr, procTriple);

    const auto begin = std::chrono::high_resolution_clock::now();

    //jl.addObjectFile("add.o");
    checkForError(jl.addModule("add.cpp", compileCPP));
    checkForError(jl.addModule("fib.c", compileC));

    auto fib = (fib_fn) jl.lookup("fib").getAddress();

    // Get time this took
    auto time = std::chrono::high_resolution_clock::now() - begin;

    // Invoke fib to make sure it works.
    for (uint64_t i = 0; i != 10; ++i) {
	printf("fib(%llu) = %llu\n", i, fib(i));
    }

    std::cout << "Elapsed time: " << std::chrono::duration<double, std::milli>(time).count() << ".\n";
    return 0;
}
