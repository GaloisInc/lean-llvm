#include <runtime/object.h>
#include <llvm/IR/Module.h>

using namespace lean;

llvm::LLVMContext* toLLVMContext(b_obj_arg o);

lean::obj_res allocModuleObj(object* ctx, std::unique_ptr<llvm::Module> m);

void trivialForeach(void* p, b_obj_arg a);

// Casts to given type and invokes delete
template<typename T>
void deleteFinalize(void* p) {
    delete static_cast<T*>(p);
}

// Register a class whose external data is a pointer to type `T`, and whose
// finalizer just calls delete on the pointer with that type.
template<typename T>
external_object_class* registerDeleteClass() {
    return register_external_object_class(&deleteFinalize<T>, &trivialForeach);
}

llvm::Triple* getTriple(b_obj_arg o);

obj_res errorMsgObj(llvm::Error e);

/* Create a pair from the two arguments. */
static
inline obj_res mk_pair(obj_arg x, obj_arg y) {
  obj_res r = alloc_cnstr(0, 2, 0);
  cnstr_set(r, 0, x);
  cnstr_set(r, 1, y);
  return r;
}
