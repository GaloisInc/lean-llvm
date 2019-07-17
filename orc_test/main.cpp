#include "llvm/ExecutionEngine/Orc/Core.h"
#include "llvm/ExecutionEngine/Orc/LLJIT.h"
#include "llvm/ExecutionEngine/SectionMemoryManager.h"

#include "llvm/Bitcode/BitcodeReader.h"
#include <iostream>

#include "clang/Frontend/CompilerInstance.h"
#include "clang/CodeGen/CodeGenAction.h"

using namespace std::chrono;
using namespace llvm;
using namespace orc;


std::unique_ptr<MemoryBuffer> fromFile(const char* path) {
    llvm::ErrorOr<std::unique_ptr<MemoryBuffer>> MBOrErr = MemoryBuffer::getFile(path);

    if (!MBOrErr)  {
	printf("Could not open %s\n", path);
	exit(-1);
    }

    return std::move(MBOrErr.get());
}

std::unique_ptr<llvm::Module> getModule(LLVMContext* ctx, const char* path) {
    std::unique_ptr<MemoryBuffer> b = fromFile(path);

    Expected< std::unique_ptr< Module > > mr = parseBitcodeFile(b->getMemBufferRef(), *ctx);
    if (!mr) {
	printf("Loading module failed");
	exit(-1);
    }
    return std::move(*mr);
}

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


std::unique_ptr<llvm::Module> compileC(llvm::LLVMContext* ctx, const char* path) {
    const char * args[] = { path };
    const char *const * argEnd = args + sizeof(args) / sizeof(args[0]);
    return compile(ctx, args, argEnd);
}

std::unique_ptr<llvm::Module> compileCPP(llvm::LLVMContext* ctx, const char* path) {
    const char * args[] = { path, "-stdlib=libc++" };
    const char *const * argEnd = args + sizeof(args) / sizeof(args[0]);
    return compile(ctx, args, argEnd);
}

typedef uint64_t (*add_fn)(uint64_t, uint64_t);

typedef uint64_t (*fib_fn)(uint64_t);

/*
JITEvaluatedSymbol getSym(ExecutionSession& es, MangleAndInterner& mangle, const std::string& nm) {
    Expected<JITEvaluatedSymbol> sym = es.lookup({&es.getMainJITDylib()}, mangle(nm));
    if (!sym) {
	printf("!sym\n");
	Error e = sym.takeError();
	outs() << "lookup error: " << e;
	exit(-1);
    }
    return *sym;
}

*/
/*
namespace llvm {

void DisableABIBreakingChecks

}
*/

typedef std::unique_ptr<llvm::Module> (*moduleFn)(llvm::LLVMContext* ctx, const char* path);

void addModule(IRLayer& compileLayer,
	       ThreadSafeContext& ctx,
	       const char* path,
	       moduleFn f) {
    auto m = f(ctx.getContext(), path);
    ExecutionSession& es = compileLayer.getExecutionSession();

    JITDylib& dylib = es.getMainJITDylib();
    auto e = compileLayer.add(dylib, ThreadSafeModule(std::move(m), ctx));
    if (e) {
	outs() << "Failed to add " << path << ": " << e;
	exit(-1);
    }
}

/* Load the file at the given path and at it to the main dynamic
   library in the object layer */
void addObjectFile(ObjectLayer& objectLayer, const char* path) {
    auto objBuffer = fromFile("add.o");
    JITDylib& dylib = objectLayer.getExecutionSession().getMainJITDylib();
    Error e = objectLayer.add(dylib, std::move(objBuffer));
    if (e) {
	fprintf(stderr, "Failed to add object file %s.\n", path);
	exit(-1);
    }
}

int main(int argc, const char** argv) {
    LLVMInitializeX86TargetInfo();
    LLVMInitializeX86TargetMC();
    LLVMInitializeX86Target();
    LLVMInitializeX86AsmPrinter();

    Triple triple(sys::getProcessTriple());

    JITTargetMachineBuilder jtmb(triple);

    auto TM = jtmb.createTargetMachine();
    if (!TM) {
	printf("!TM\n");
	Error e = TM.takeError();
	outs() << "Get datalayout error: " << e;
	exit(-1);
    }

    DataLayout dl((*TM)->createDataLayout());

    ExecutionSession es;

    RTDyldObjectLinkingLayer objectLayer(es, []() { return llvm::make_unique<SectionMemoryManager>(); });

    MangleAndInterner mangle(es, dl);

    ThreadSafeContext ctx = make_unique<LLVMContext>();

    //    es.getMainJITDylib().setGenerator(cantFail(DynamicLibrarySearchGenerator::GetForCurrentProcess(dl)));


    const auto begin = high_resolution_clock::now();

    //    addObjectFile(objectLayer, "add.o");

    IRCompileLayer compileLayer(es, objectLayer, ConcurrentIRCompiler(jtmb));
    //addModule(compileLayer, ctx, "fib.bc", getModule);
    addModule(compileLayer, ctx, "add.cpp", compileCPP);
    addModule(compileLayer, ctx, "fib.c", compileCPP);

    std::string nm = "fib";
    Expected<JITEvaluatedSymbol> sym = es.lookup({&es.getMainJITDylib()}, mangle(nm));
    if (!sym) {
	printf("!sym\n");
	Error e = sym.takeError();
	outs() << "lookup error: " << e;
	exit(-1);
    }

    auto fib = (fib_fn) sym->getAddress();
    auto r = fib(10);

    // Get time to add
    auto time = high_resolution_clock::now() - begin;


    for (uint64_t i = 0; i != 10; ++i) {
	printf("fib(%llu) = %llu\n", i, fib(i));
    }

    std::cout << "Elapsed time: " << duration<double, std::milli>(time).count() << ".\n";

    return 0;
}
