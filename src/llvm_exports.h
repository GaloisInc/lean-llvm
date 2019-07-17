#include <runtime/object.h>
#include <llvm/IR/Module.h>

namespace lean_llvm {

llvm::LLVMContext* toLLVMContext(lean::b_obj_arg o);

lean::obj_res allocModuleObj(lean::object* ctx, std::unique_ptr<llvm::Module> m);

}
