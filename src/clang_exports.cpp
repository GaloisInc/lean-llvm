#include "llvm_exports.h"

#include <runtime/io.h>

#include <clang/Frontend/CompilerInstance.h>
#include <clang/CodeGen/CodeGenAction.h>


using namespace lean;

namespace lean_llvm {

static
obj_res compileArgs(obj_arg ctxObj,
		    const char *const * args,
		    const char *const * argEnd,
		    lean::obj_arg r) {
    auto ctx = toLLVMContext(ctxObj);

    clang::IntrusiveRefCntPtr<clang::DiagnosticIDs > diags(new clang::DiagnosticIDs());
    clang::IntrusiveRefCntPtr<clang::DiagnosticOptions > diagOpts(new clang::DiagnosticOptions());

    clang::DiagnosticsEngine diagEngine(diags, diagOpts);

    std::shared_ptr<clang::CompilerInvocation> invocation(new clang::CompilerInvocation());
    clang::CompilerInvocation::CreateFromArgs(*invocation, args, argEnd, diagEngine);

    // Create the compiler instance
    clang::CompilerInstance instance;
    instance.setInvocation(invocation);

    // Create diagnostics.
    instance.createDiagnostics();
    if (!instance.hasDiagnostics()) {
	dec_ref(ctxObj);
	return set_io_error(r, mk_string("Diagnostics creation failed"));
    }

    // Generate LLVM module using clang.
    clang::EmitLLVMOnlyAction act(ctx);
    if (!instance.ExecuteAction(act)) {
	dec_ref(ctxObj);
	return set_io_error(r, mk_string("Compilation failed"));
    }
    // Return module.
    auto modPtr = act.takeModule();
    return set_io_result(r, allocModuleObj(ctxObj, std::move(modPtr)));
}

obj_res compileCFile(obj_arg ctxObj, b_obj_arg pathObj, obj_arg r) {
    const char * args[] = { string_cstr(pathObj) };
    const char *const * argEnd = args + sizeof(args) / sizeof(args[0]);
    return compileArgs(ctxObj, args, argEnd, r);
}

obj_res compileCPPFile(obj_arg ctxObj, b_obj_arg pathObj, obj_arg r) {
    const char * args[] = { string_cstr(pathObj), "-stdlib=libc++" };
    const char *const * argEnd = args + sizeof(args) / sizeof(args[0]);
    return compileArgs(ctxObj, args, argEnd, r);
}

}
