
#include "llvm_exports.h"

#include <lean/io.h>

#include <llvm/ExecutionEngine/Orc/CompileUtils.h>
#include <llvm/ExecutionEngine/Orc/ExecutionUtils.h>
#include <llvm/ExecutionEngine/Orc/IRCompileLayer.h>
#include <llvm/ExecutionEngine/Orc/RTDyldObjectLinkingLayer.h>
#include <llvm/ExecutionEngine/SectionMemoryManager.h>

#include <clang/CodeGen/CodeGenAction.h>
#include <clang/Frontend/CompilerInstance.h>

using namespace lean;

////////////////////////////////////////////////////////////////////////
// Compilation

static
std::unique_ptr<llvm::Module>
compileArgs(llvm::LLVMContext* ctx, b_obj_arg argArrayObj) {

    size_t argCnt = array_size(argArrayObj);

    // Copy arguments over
    const char* args[argCnt];
    auto argEnd = args + argCnt;
    {
	auto argObjPtr = array_cptr(argArrayObj);
	for (auto argStrPtr = args; argStrPtr != argEnd; ++argStrPtr, ++argObjPtr) {
	    *argStrPtr = lean::string_cstr(*argObjPtr);
	}
    }

    llvm::IntrusiveRefCntPtr<clang::DiagnosticIDs> diags(new clang::DiagnosticIDs());
    llvm::IntrusiveRefCntPtr<clang::DiagnosticOptions> diagOpts(new clang::DiagnosticOptions());

    clang::DiagnosticsEngine diagEngine(diags, diagOpts);

    std::shared_ptr<clang::CompilerInvocation> invocation(new clang::CompilerInvocation());
    clang::CompilerInvocation::CreateFromArgs(*invocation, args, argEnd, diagEngine);

    // Create the compiler instance
    clang::CompilerInstance instance;
    instance.setInvocation(invocation);

    // Create diagnostics.
    instance.createDiagnostics();
    lean_assert(instance.hasDiagnostics());

    // Generate LLVM module using clang.
    clang::EmitLLVMOnlyAction act(ctx);
    if (!instance.ExecuteAction(act)) {
	return 0;
    }
    return act.takeModule();
}

extern "C" {
obj_res lean_llvm_invokeClang(obj_arg ctxObj,
		    b_obj_arg argArrayObj,
		    lean::obj_arg r) {
    auto ctx = toLLVMContext(ctxObj);
    auto modPtr = compileArgs(ctx, argArrayObj);

    if (modPtr == 0) {
	dec_ref(ctxObj);
	return set_io_error(r, mk_string("Compilation failed"));
    }

    return set_io_result(r, allocModuleObj(ctxObj, std::move(modPtr)));
}
}

////////////////////////////////////////////////////////////////////////
// CompilerSession

/**
 * Provides access to an ORC JIT session.
 *
 * The LLVM API makes heavy use of mutable state, and uniquely owned objects that
 * are not clean Lean objects.  We avoid exposing this to Lean by having more code
 * in the C++ runtime.
 */
struct CompilerSession {

    llvm::orc::ExecutionSession es;
    llvm::orc::RTDyldObjectLinkingLayer objectLayer;
    llvm::orc::IRCompileLayer compileLayer;
    llvm::orc::MangleAndInterner mangle;

    // Context for LLVM modules.
    llvm::orc::ThreadSafeContext ctx;

    CompilerSession(const CompilerSession&) = delete;

    CompilerSession(llvm::orc::JITTargetMachineBuilder& jtmb,
		    llvm::DataLayout& dl)
	: es(),
	  objectLayer(es, []() { return std::make_unique<llvm::SectionMemoryManager>(); }),
	  compileLayer(es, objectLayer, llvm::orc::ConcurrentIRCompiler(jtmb)),
	  mangle(es, dl),
          ctx(std::make_unique<llvm::LLVMContext>()) {
    }
};

/** Get compiler session class. */
static
external_object_class* compilerSessionClass() {
    static external_object_class* c = registerDeleteClass<CompilerSession>();
    return c;
}

CompilerSession* getCompilerSession(b_obj_arg o) {
    lean_assert(external_class(o) == compilerSessionClass());
    return static_cast<CompilerSession*>(external_data(o));
}


extern "C" {
obj_res lean_llvm_newCompilerSession(b_obj_arg tripleObj, obj_arg r) {
    auto triple = getTriple(tripleObj);
    llvm::orc::JITTargetMachineBuilder jtmb(*triple);

    auto tm = jtmb.createTargetMachine();
    if (!tm) {
	return set_io_error(r, errorMsgObj(tm.takeError()));
    }

    llvm::DataLayout dl((*tm)->createDataLayout());


    auto csession = new CompilerSession(jtmb, dl);

    auto gen = llvm::orc::DynamicLibrarySearchGenerator::GetForCurrentProcess(dl);
    if (!gen) {
	return set_io_error(r, errorMsgObj(gen.takeError()));
    }
    csession->es.getMainJITDylib().setGenerator(*gen);

    auto sessObj = alloc_external(compilerSessionClass(), csession);
    return set_io_result(r, sessObj);
}

obj_res lean_llvm_addFromClangCompile(b_obj_arg compSessObj,
			    b_obj_arg argArrayObj,
			    lean::obj_arg r) {

    auto csession = getCompilerSession(compSessObj);

    llvm::LLVMContext* ctx = csession->ctx.getContext();

    auto modPtr = compileArgs(ctx, argArrayObj);



    if (modPtr == 0) {
	return set_io_error(r, mk_string("Compilation failed"));
    }

    llvm::orc::ExecutionSession& es = csession->es;
    llvm::orc::JITDylib& dylib = es.getMainJITDylib();
    llvm::orc::ThreadSafeModule tsm(std::move(modPtr), csession->ctx);

    llvm::Error e = csession->compileLayer.add(dylib, std::move(tsm));
    if (e) {
	return set_io_error(r, errorMsgObj(std::move(e)));
    }

    return set_io_result(r, box(0));
}

obj_res lean_llvm_lookupFn(b_obj_arg compSessObj,
		 b_obj_arg symNameObj,
		 b_obj_arg tpObj,
		 lean::obj_arg r) {
    auto csession = getCompilerSession(compSessObj);
    llvm::StringRef symName(string_cstr(symNameObj));

    llvm::orc::ExecutionSession& es = csession->es;
    llvm::orc::MangleAndInterner& mangle = csession->mangle;

    llvm::orc::SymbolStringPtr symPtr = mangle(symName);

    llvm::orc::JITDylib* dylib = &es.getMainJITDylib();

    dylib->dump(llvm::errs());


    llvm::Expected<llvm::JITEvaluatedSymbol> sym = es.lookup({dylib}, symPtr);
    if (!sym) {
	return set_io_error(r, errorMsgObj(sym.takeError()));
    }

    inc_ref(compSessObj);

    void* addr = reinterpret_cast<void*>(sym->getAddress());
    std::cerr << "Addr " << addr << std::endl;
    obj_res f = alloc_closure(addr, 2, 0);

    return set_io_result(r, f);
}
}
