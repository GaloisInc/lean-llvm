#include <runtime/object.h>
#include <llvm/IR/Module.h>

llvm::LLVMContext* toLLVMContext(lean::b_obj_arg o);

lean::obj_res allocModuleObj(lean::object* ctx, std::unique_ptr<llvm::Module> m);

void trivialForeach(void* p, lean::b_obj_arg a);

// Casts to given type and invokes delete
template<typename T>
void deleteFinalize(void* p) {
    delete static_cast<T*>(p);
}

// Register a class whose external data is a pointer to type `T`, and whose
// finalizer just calls delete on the pointer with that type.
template<typename T>
lean::external_object_class* registerDeleteClass() {
    return lean::register_external_object_class(&deleteFinalize<T>, &trivialForeach);
}

llvm::Triple* getTriple(lean::b_obj_arg o);

lean::obj_res errorMsgObj(llvm::Error e);


