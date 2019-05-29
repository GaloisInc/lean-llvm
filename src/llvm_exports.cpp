#include <cstddef>

#include <llvm/IR/LLVMContext.h>
#include <llvm/Support/MemoryBuffer.h>
#include <llvm/Bitcode/BitcodeReader.h>

#include "apply.h"
#include <iostream>

////////////////////////////////////////////////////////////////////////
// Import lean

using namespace std;
using namespace lean;

////////////////////////////////////////////////////////////////////////
// Copied from io.cpp

extern obj_res const REAL_WORLD = box(0);

static obj_res set_io_error(obj_arg r, obj_arg e) {
    if (is_exclusive(r)) {
        cnstr_set_tag(r, 1);
        cnstr_set(r, 0, e);
        return r;
    } else {
        dec_ref(r);
        object * new_r = alloc_cnstr(1, 2, 0);
        cnstr_set(new_r, 0, e);
        cnstr_set(new_r, 1, REAL_WORLD);
        return new_r;
    }
}

static obj_res set_io_result(obj_arg r, obj_arg a) {
    if (is_exclusive(r)) {
        cnstr_set(r, 0, a);
        return r;
    } else {
        dec_ref(r);
        object * new_r = alloc_cnstr(0, 2, 0);
        cnstr_set(new_r, 0, a);
        cnstr_set(new_r, 1, REAL_WORLD);
        return new_r;
    }
}

////////////////////////////////////////////////////////////////////////
// LLVM Specific

using namespace llvm;

namespace lean_llvm {

void llvmContextFinalize(void* p) {
    LLVMContext* d = static_cast<LLVMContext*>(p);
    delete d;
}

void llvmContextForeach(void * p, b_obj_arg a) {
    // Do not think anything is needed
}

static
external_object_class* getLlvmContextClass() {
    // Use static thread to make this thread safe (hopefully).
    static
    external_object_class* c(register_external_object_class(&llvmContextFinalize,
							    &llvmContextForeach));
    return c;
}

LLVMContext& toLLVMContext(b_obj_arg o) {
    lean_assert(external_class(o) == getLlvmContextClass());
    return *static_cast<LLVMContext*>(external_data(o));
}


obj_res newLLVMContext(obj_arg r) {
    LLVMContext* ctx = new LLVMContext();
    object* ctxObj = alloc_external(getLlvmContextClass(), ctx);
    return set_io_result(r, ctxObj);
}


////////////////////////////////////////////////////////////////////
// MemoryBuffer

void memoryBufferFinalize(void* p) {
    MemoryBuffer* d = static_cast<MemoryBuffer*>(p);
    std::cerr << "Finalize MB " << d << std::endl;
    delete d;
}

void memoryBufferForeach(void * p, b_obj_arg a) {
    std::cerr << "MemoryBufferForeach" << std::endl;
}

static
external_object_class* getMemoryBufferClass() {
    // Use static thread to make this thread safe (hopefully).
    static
    external_object_class* c(register_external_object_class(&memoryBufferFinalize,
							    &memoryBufferForeach));
    return c;
}

MemoryBuffer* toMemoryBuffer(b_obj_arg o) {
    lean_assert(external_class(o) == getMemoryBufferClass());
    return static_cast<MemoryBuffer*>(external_data(o));
}

obj_res newMemoryBufferFromFile(b_obj_arg fname, obj_arg r) {
    const char* path = string_cstr(fname);

    llvm::ErrorOr<std::unique_ptr<MemoryBuffer>> MBOrErr =
	MemoryBuffer::getFile(path);
    if (std::error_code EC = MBOrErr.getError()) {
	return set_io_error(r, mk_string(EC.message()));
    }

    MemoryBuffer* b = MBOrErr.get().release();
    //FIXME: What if alloc_external fails?
    object* bufferObj = alloc_external(getMemoryBufferClass(), b);
    return set_io_result(r, bufferObj);

}

////////////////////////////////////////////////////////////////////
// Module

struct ModuleRec {
    ModuleRec(object* c, llvm::Module* m)
	: ctxObj(c), module(std::move(m)) {
	inc_ref(c);
    }

    ~ModuleRec() {
	dec_ref(ctxObj);
    }

    // Lean object for context (we hold a handle to this so that
    // it is not deleted before we are done with the module).
    object* ctxObj;

    llvm::Module* module;
};

void moduleRecFinalize(void* p) {
    ModuleRec* d = static_cast<ModuleRec*>(p);
    delete d;
}

// TODO: Check if this is right.
void moduleRecForeach(void * p, b_obj_arg a) {
    ModuleRec* d = static_cast<ModuleRec*>(p);
    apply_1(a, d->ctxObj);
}

static
external_object_class* getModuleRecClass() {
    // Use static thread to make this thread safe due to static initialization rule.
    static
    external_object_class* c(register_external_object_class(&moduleRecFinalize,
							    &moduleRecForeach));
    return c;
}


void trivialFinalize(void* p ) {
  return;
}

void trivialForeach(void* p, b_obj_arg a ) {
  return;
}

static
external_object_class* getTrivialObjectClass() {
  static
  external_object_class* c( register_external_object_class(&trivialFinalize, &trivialForeach) );

  return c;
}


ModuleRec* toModuleRec(b_obj_arg o) {
    lean_assert(external_class(o) == getModuleRecClass());
    return static_cast<ModuleRec*>(external_data(o));
}

Module* toModule(b_obj_arg o) {
    return toModuleRec(o)->module;
}

obj_res parseBitcodeFile(b_obj_arg b, b_obj_arg c, obj_arg r) {
    MemoryBufferRef Buf = toMemoryBuffer(b)->getMemBufferRef();
    LLVMContext& Ctx = toLLVMContext(c);
    ErrorOr<std::unique_ptr<Module>> ModuleOrErr =
          expectedToErrorOrAndEmitErrors(Ctx, parseBitcodeFile(Buf, Ctx));

    if (std::error_code EC = ModuleOrErr.getError()) {
	return set_io_error(r, mk_string(EC.message()));
    }

    object* moduleObj = alloc_external(getModuleRecClass(), new ModuleRec(c, ModuleOrErr.get().release()));
    return set_io_result(r, moduleObj);
}

obj_res getModuleIdentifier(b_obj_arg m, obj_arg r) {
    return set_io_result(r, mk_string(toModule(m)->getModuleIdentifier()));
}

obj_res setModuleIdentifier(b_obj_arg m, b_obj_arg nm, obj_arg r) {
    toModule(m)->setModuleIdentifier(string_to_std(nm));
    return set_io_result(r, box(0));
}

obj_res mkSomeList( b_obj_arg m ) {
  obj_res x = alloc_cnstr( 1, 2, 0 );
  cnstr_set( x, 0, m );
  cnstr_set( x, 1, box(0) );

  obj_res y = alloc_cnstr( 1, 2, 0 );
  cnstr_set (y, 0, m );
  cnstr_set (y, 1, x ); 

  return y;
}

obj_res getFunctionArray (b_obj_arg m, obj_arg r ) {
  Module *mod = toModule(m);

  obj_res arr = alloc_array( 0, 0 );

  for( Function &f : *mod ) {
    obj_res f_ob = alloc_external( getTrivialObjectClass(), &f );
    arr = array_push( arr, f_ob );
  }

  return set_io_result( r, arr );
}


obj_res getBasicBlockArray( b_obj_arg f, obj_arg r ) {
  Function *fun = static_cast<Function*>(external_data(f));

  obj_res arr = alloc_array( 0, 0 );
  for( BasicBlock &bb : *fun ) {
    obj_res bb_ob = alloc_external( getTrivialObjectClass(), &bb );
    arr = array_push( arr, bb_ob );
  }

  return set_io_result( r, arr );
}

obj_res getBBName ( b_obj_arg f, obj_arg r ) {
  BasicBlock *bb = static_cast<BasicBlock*>(external_data(f));
  ValueName *vnm = bb->getValueName();
  if( vnm == nullptr ) {
    return set_io_result( r, mk_option_none() );
  } else {
    return set_io_result( r, mk_option_some(mk_string(vnm->getKey().str())) );
  }
}

obj_res getFunctionName( b_obj_arg f, obj_arg r ) {
  Function *fun = static_cast<Function*>(external_data(f));
  std::string str = fun->getValueName()->getKey().str();
  return set_io_result( r, mk_string(str) );
}




}

