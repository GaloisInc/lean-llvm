/*
This module defines C functions needed for invoking LLVM
from Lean.
*/

#include "llvm_exports.h"

#include <cstddef>
#include <iostream>

#include <llvm/ADT/Triple.h>
#include <llvm/Bitcode/BitcodeReader.h>
#include <llvm/IR/Instructions.h>
#include <llvm/Support/raw_os_ostream.h>
#include <llvm/Support/TargetSelect.h>

#include <runtime/apply.h>
#include <runtime/io.h>
#include <runtime/mpz.h>
#include <runtime/utf8.h>


////////////////////////////////////////////////////////////////////////
// Import lean

using namespace lean;


////////////////////////////////////////////////////////////////////////
// StringRef

static inline char * w_string_cstr(object * o) {
  lean_assert(lean_is_string(o)); return lean_to_string(o)->m_data;
}

object * mk_string(const llvm::StringRef& s) {
    size_t sz  = s.size();
    size_t len = utf8_strlen(s.data(), sz);
    size_t rsz = sz + 1;
    object * r = alloc_string(rsz, rsz, len);
    memcpy(w_string_cstr(r), s.data(), sz);
    w_string_cstr(r)[sz] = 0;
    return r;
}

const llvm::StringRef asStringRef( object* o ) {
  lean_assert(is_string(o));
  size_t sz_with_null = string_size(o);
  return llvm::StringRef( w_string_cstr(o), sz_with_null - 1 );
}


////////////////////////////////////////////////////////////////////////
// Generic class functions


void trivialFinalize(void* p) {
  return;
}

void trivialForeach(void* p, b_obj_arg a) {
  return;
}

static
external_object_class* getTrivialObjectClass() {
  static
  external_object_class* c(register_external_object_class(&trivialFinalize, &trivialForeach));

  return c;
}

////////////////////////////////////////////////////////////////////////
// Owned objects

// This owns a LLVM module, and also a pointer to an owner object to ensure
// the owner is not freed as along as this object is alive.
//
// This will not delete the object when it goes out of scope.
template<typename T>
struct OwnedExternal {
    OwnedExternal(object* c, T* v)
      : ctxObj(c), value(v) {
	inc_ref(c);
    }

    ~OwnedExternal() {
	dec_ref(ctxObj);
    }


    // Lean object for context (we hold a handle to this so that
    // it is not deleted before we are done with the module).
    object* ctxObj;

    T* value;
};

template<typename T>
void ownedExternalFinalize(void* p) {
    delete static_cast<OwnedExternal<T>*>(p);
}

template<typename T>
void ownedExternalForeach(void *p, b_obj_arg a) {
    auto d = static_cast<OwnedExternal<T>*>(p);
    apply_1(a, d->ctxObj);
}


// Register a class whose lifetime is controlled by another object.  It holds
// a reference to the owner while alive and releases it when finalized.
template<typename T>
static
external_object_class* registerOwnedClass() {
    return register_external_object_class(&ownedExternalFinalize<T>, &ownedExternalForeach<T>);
}

////////////////////////////////////////////////////////////////////////
// LLVMContext

/** Class for freshly created LLVM contexts. */
static
external_object_class* getLLVMContextClass() {
    // Use static thread to make this thread safe (hopefully).
    static external_object_class* c = registerDeleteClass<llvm::LLVMContext>();
    return c;
}

/** Get the LLVM context associated with the object. */
llvm::LLVMContext* toLLVMContext(b_obj_arg o) {
    lean_assert(external_class(o) == getLLVMContextClass());
    return static_cast<llvm::LLVMContext*>(external_data(o));
}

////////////////////////////////////////////////////////////////////
// MemoryBuffer

void memoryBufferFinalize(void* p) {
    delete static_cast<llvm::MemoryBuffer*>(p);
}

static
external_object_class* getMemoryBufferClass() {
    // Use static thread to make this thread safe (hopefully).
    static
    external_object_class* c(register_external_object_class(&memoryBufferFinalize,
							    &trivialForeach));
    return c;
}

llvm::MemoryBuffer* toMemoryBuffer(b_obj_arg o) {
    lean_assert(external_class(o) == getMemoryBufferClass());
    return static_cast<llvm::MemoryBuffer*>(external_data(o));
}

////////////////////////////////////////////////////////////////////////
// Types

// According to the LLVM programmer's documentation, llvm::Type objects
//  are never free'd once allocated.  Thus, we do not need to manage
//  the storage duration of these objects.
static inline
obj_res allocTypeObj(llvm::Type* tp) {
    return alloc_external(getTrivialObjectClass(), tp);
}

static inline
llvm::Type* toType(b_obj_arg o) {
    lean_assert(external_class(o) == getTrivialObjectClass());
    return static_cast<llvm::Type*>(external_data(o));
}

////////////////////////////////////////////////////////////////////////
// Values

static
external_object_class* getValueObjectClass() {
    // Use static thread to make this thread safe due to static initialization rule.
    static
	external_object_class* c(register_external_object_class(&ownedExternalFinalize<llvm::Value>,
								&ownedExternalForeach<llvm::Value>));
    return c;
}

obj_res getOptionalNameObj(llvm::ValueName* nm) {
    return (nm == nullptr)
	? mk_option_none()
	: mk_option_some(mk_string(nm->getKey()));
}

obj_res allocValueObj(obj_res parent, llvm::Value* v) {
    auto e = new OwnedExternal<llvm::Value>(parent, v);
    return alloc_external(getValueObjectClass(), e);
}

static
llvm::Value* toValue(b_obj_arg o) {
  lean_assert(external_class(o) == getValueObjectClass());
  return static_cast<OwnedExternal<llvm::Value>*>(external_data(o))->value;
}

static
obj_res valueParent(b_obj_arg o) {
    lean_assert(external_class(o) == getValueObjectClass());
    return static_cast<OwnedExternal<llvm::Value>*>(external_data(o))->ctxObj;
}

// llvm::Instruction is a subtype of llvm::Value, so we can use the same
// allocation strategy for it.
obj_res allocInstructionObj(obj_res parent, llvm::Instruction* i) {
  return allocValueObj( parent, i );
}

static
llvm::Instruction* toInstruction(b_obj_arg o) {
  return llvm::dyn_cast<llvm::Instruction>(toValue(o));
}

// llvm::BasicBlock is a subtype of llvm::Value, so we can use the same
// allocation strategy for it.
obj_res allocBasicBlockObj(obj_arg parent, llvm::BasicBlock* bb) {
  return allocValueObj( parent, bb );
}

llvm::BasicBlock* toBasicBlock(b_obj_arg o) {
  return llvm::dyn_cast<llvm::BasicBlock>(toValue(o));
}

////////////////////////////////////////////////////////////////////////
// Functions

// Allocate a function object (the parent lifetime should exceed this objects).
obj_res allocFunctionObj(obj_arg parent, llvm::Function* f) {
  return allocValueObj( parent, f );
}

llvm::Function* toFunction(b_obj_arg o) {
  return llvm::dyn_cast<llvm::Function>(toValue(o));
}

////////////////////////////////////////////////////////////////////////
// Global Variables

// Allocate a global variable object (the parent lifetime should exceed this objects).
obj_res allocGlobalVarObj(obj_arg parent, llvm::GlobalVariable* gv) {
  return allocValueObj( parent, gv );
}

llvm::GlobalVariable* toGlobalVar(b_obj_arg o) {
  return llvm::dyn_cast<llvm::GlobalVariable>(toValue(o));
}


////////////////////////////////////////////////////////////////////
// Module

// This owns a LLVM module, and also a pointer to the context to ensure
// the context is not freed as long as the module is alive.
struct ModuleRec {
    // Lean object for context (we hold a handle to this so that
    // it is not deleted before we are done with the module).
    object* ctxObj;

    std::unique_ptr<llvm::Module> module;

    ModuleRec(const ModuleRec&) = delete;

    ModuleRec(object* c, std::unique_ptr<llvm::Module> m)
	: ctxObj(c), module(std::move(m)) {
    }

    ~ModuleRec() {
	module = 0;
	dec_ref(ctxObj);
    }

};

void moduleRecForeach(void * p, b_obj_arg a) {
    ModuleRec* d = static_cast<ModuleRec*>(p);
    apply_1(a, d->ctxObj);
}

static
external_object_class* getModuleRecClass() {
    // Use static thread to make this thread safe due to static initialization rule.
    static
	external_object_class* c(register_external_object_class(&deleteFinalize<ModuleRec>,
								&moduleRecForeach));
    return c;
}

obj_res allocModuleObj(object* ctx, std::unique_ptr<llvm::Module> m) {
    return alloc_external(getModuleRecClass(), new ModuleRec(ctx, std::move(m)));
}

llvm::Module* toModule(b_obj_arg o) {
    lean_assert(external_class(o) == getModuleRecClass());
    auto p = static_cast<ModuleRec*>(external_data(o));
    return p->module.get();
}

/** Create an object from an LLVM error. */
obj_res errorMsgObj(llvm::Error e) {
    std::string msg;
    handleAllErrors(std::move(e), [&](llvm::ErrorInfoBase &eib) {
        msg = eib.message();
    });
    return mk_string(msg);
}

////////////////////////////////////////////////////////////////////////
// Triple

/** Get triple class. */
static
external_object_class* getTripleClass() {
    static external_object_class* c = registerDeleteClass<llvm::Triple>();
    return c;
}

llvm::Triple* getTriple(b_obj_arg o) {
    lean_assert(external_class(o) == getTripleClass());
    return static_cast<llvm::Triple*>(external_data(o));
}



extern "C" {

/** Create a new LLVM context object. */
obj_res lean_llvm_newContext(obj_arg /*r*/) {
    auto ctx = new llvm::LLVMContext();
    object* ctxObj = alloc_external(getLLVMContextClass(), ctx);
    return set_io_result(ctxObj);
}


obj_res lean_llvm_newMemoryBufferFromFile(b_obj_arg fname, obj_arg r) {
    const char* path = string_cstr(fname);

    auto MBOrErr = llvm::MemoryBuffer::getFile(path);
    if (std::error_code EC = MBOrErr.getError()) {
	return set_io_error(mk_string(EC.message()));
    }

 auto b = std::move(MBOrErr.get());
    object* bufferObj = alloc_external(getMemoryBufferClass(), b.get());
    b.release();
    return set_io_result(bufferObj);
}

obj_res lean_llvm_getTypeTag(b_obj_arg tp_obj, obj_arg r) {
    auto tp = toType(tp_obj);
    llvm::Type::TypeID id = tp->getTypeID();
    obj_res n = box(id);
    return set_io_result(n);
}

obj_res lean_llvm_newPrimitiveType( b_obj_arg ctx_obj, b_obj_arg code, obj_arg r ) {
  llvm::LLVMContext *ctx = toLLVMContext(ctx_obj);
  llvm::Type::TypeID id = static_cast<llvm::Type::TypeID>(unbox(code));
  if (auto tp = llvm::Type::getPrimitiveType(*ctx, id) ) {
    obj_res tp_obj = allocTypeObj(tp);
    return set_io_result( tp_obj );
  }

  return set_io_error( mk_string("newPrimitiveType expected primitive type code") );
}

obj_res lean_llvm_newIntegerType( b_obj_arg ctx_obj, b_obj_arg w, obj_arg r ) {
  llvm::LLVMContext *ctx = toLLVMContext(ctx_obj);
  auto tp = llvm::IntegerType::get(*ctx, unbox(w));
  return set_io_result( allocTypeObj(tp) );
}

obj_res lean_llvm_newArrayType( b_obj_arg n, b_obj_arg tp_obj, obj_arg r ) {
  auto eltp = toType(tp_obj);
  auto tp = llvm::ArrayType::get( eltp, unbox(n) );
  return set_io_result( allocTypeObj(tp) );
}

obj_res lean_llvm_newVectorType( b_obj_arg n, b_obj_arg tp_obj, obj_arg r ) {
  auto eltp = toType(tp_obj);
  auto tp = llvm::VectorType::get( eltp, unbox(n) );
  return set_io_result( allocTypeObj(tp) );
}

obj_res lean_llvm_newPointerType( b_obj_arg tp_obj, obj_arg r ) {
  auto eltp = toType(tp_obj);
  auto addrSpace = 0;
  auto tp = llvm::PointerType::get( eltp, addrSpace );
  return set_io_result( allocTypeObj(tp) );
}

obj_res lean_llvm_newFunctionType( b_obj_arg ret_obj, b_obj_arg args_obj, b_obj_arg varargs, obj_arg r ) {
  auto ret = toType(ret_obj);
  
  size_t n = array_size(args_obj);
  llvm::Type* tps[n];
  for( size_t i = 0; i<n; i++ ) {
    tps[i] = toType(array_get(args_obj, i));
  }
  llvm::ArrayRef<llvm::Type*> args( tps, n );
  auto tp = llvm::FunctionType::get( ret, args, unbox(varargs) );

  return set_io_result( allocTypeObj(tp) );
}


obj_res lean_llvm_newLiteralStructType( b_obj_arg packed, b_obj_arg tps_obj, obj_arg r ) {
  size_t n = array_size(tps_obj);
  llvm::Type* tps[n];
  for( size_t i = 0; i<n; i++ ) {
    tps[i] = toType(array_get(tps_obj, i));
  }
  llvm::ArrayRef<llvm::Type*> tps_arr( tps, n );
  auto tp = llvm::StructType::create( tps_arr, llvm::StringRef(), unbox(packed) );
  return set_io_result( allocTypeObj(tp) );
}

obj_res lean_llvm_newOpaqueStructType( b_obj_arg ctx_obj, b_obj_arg nm_obj, obj_arg r ) {
  auto ctx = toLLVMContext(ctx_obj);
  auto nm  = asStringRef(nm_obj);

  auto tp = llvm::StructType::create( *ctx, nm );
  return set_io_result( allocTypeObj(tp) );
}

obj_res lean_llvm_setStructTypeBody( b_obj_arg tp_obj, b_obj_arg packed, b_obj_arg tps_obj, obj_arg r ) {
  if( auto tp = llvm::dyn_cast<llvm::StructType>(toType(tp_obj)) ) {

    size_t n = array_size(tps_obj);
    llvm::Type* tps[n];
    for( size_t i = 0; i<n; i++ ) {
      tps[i] = toType(array_get(tps_obj, i));
    }
    llvm::ArrayRef<llvm::Type*> tps_arr( tps, n );

    tp->setBody( tps_arr, unbox(packed) );
    return set_io_result( box(0) );
  }

  return set_io_result( mk_string("expected struct type in setStructTypeBody"));
}

obj_res lean_llvm_getTypeName( b_obj_arg tp_obj, obj_arg r ) {
  auto tp = toType(tp_obj);
  auto structtp = llvm::dyn_cast<llvm::StructType>( tp );

  if( !structtp ) {
    return set_io_result( mk_option_none() );
  }

  auto nm = structtp->getName();
  if( nm.empty() ) {
    return set_io_result( mk_option_none() );
  }

  obj_res str = mk_string( nm );
  return set_io_result( mk_option_some( str ) );
}

obj_res lean_llvm_typeIsOpaque( b_obj_arg tp_obj, obj_arg r) {
  auto tp = toType(tp_obj);
  if( auto stp = llvm::dyn_cast<llvm::StructType>(tp) ) {
    unsigned int opaque = stp->isOpaque();
    return set_io_result( box(opaque) );
  }

  return set_io_result( box(0) );
}


obj_res lean_llvm_getIntegerTypeWidth(b_obj_arg tp_obj, obj_arg r) {
    auto tp = toType(tp_obj);
    unsigned int w = tp->getIntegerBitWidth();
    obj_res w_obj = box(w); // TODO, overflow?
    return set_io_result(w_obj);
}

obj_res lean_llvm_getPointerElementType(b_obj_arg tp_obj, obj_arg r) {
    auto tp = toType(tp_obj);
    llvm::PointerType *pt = llvm::dyn_cast<llvm::PointerType>(tp);
    if (!pt) {
	return set_io_result(mk_option_none());
    }

    llvm::Type* elt_tp = pt->getElementType();
    obj_res elt_tp_obj = allocTypeObj( elt_tp );
    return set_io_result(mk_option_some(elt_tp_obj));
}

obj_res lean_llvm_getSequentialTypeData( b_obj_arg tp_obj, obj_arg r) {
  auto tp = toType(tp_obj);
  auto seq = llvm::dyn_cast<llvm::SequentialType>(tp);
  if(!seq) {
    return set_io_result(mk_option_none());
  }

  auto num = seq->getNumElements();
  auto elt_tp = seq->getElementType();
  obj_res x = mk_pair( mk_nat_obj(num), allocTypeObj( elt_tp ) );

  return set_io_result(mk_option_some( x ));
}

obj_res lean_llvm_getStructTypeData( b_obj_arg tp_obj, obj_arg r) {
  auto tp = toType(tp_obj);
  auto st = llvm::dyn_cast<llvm::StructType>(tp);

  if(!st) {
    return set_io_result( mk_option_none() );
  }

  unsigned int packed = st->isPacked();

  unsigned int n = st->getNumElements();
  obj_res arr = alloc_array(n, n);
  auto p = array_cptr(arr);
  for(unsigned i = 0; i<n; i++) {
    auto v = st->getElementType(i);
    *(p++) = allocTypeObj(v);
  }

  obj_res x = mk_pair( box(packed), arr );
  return set_io_result( mk_option_some(x) );
}

obj_res lean_llvm_getFunctionTypeData( b_obj_arg tp_obj, obj_arg r ) {
  auto tp = toType(tp_obj);
  auto fn = llvm::dyn_cast<llvm::FunctionType>(tp);

  if(!fn) {
    return set_io_result( mk_option_none() );
  }

  unsigned int varargs = fn->isVarArg();
  auto ret = fn->getReturnType();
  auto n = fn->getNumParams();
  auto arr = alloc_array(n, n);
  auto p = array_cptr(arr);
  for(unsigned i = 0; i<n; i++) {
    auto v = fn->getParamType(i);
    *(p++) = allocTypeObj(v);
  }

  obj_res x = mk_pair( allocTypeObj(ret), mk_pair( arr, box(varargs) ));
  return set_io_result( mk_option_some( x ));
}
}


extern "C" {

obj_res lean_llvm_getValueType(b_obj_arg v_obj, obj_arg r) {
    auto tp = toValue(v_obj)->getType();
    return set_io_result( allocTypeObj(tp) );
}

obj_res lean_llvm_decomposeValue(b_obj_arg v_obj, obj_arg r) {
    auto v = toValue(v_obj);

    obj_res x;
    if (auto c = llvm::dyn_cast<llvm::Constant>(v)) {

        // constant_value : llvm.code.const -> LLVMConstant -> value_decomposition
        inc_ref( v_obj );
	x = alloc_cnstr(1, 1, 0);
	cnstr_set(x, 0, v_obj);

    } else if (auto a = llvm::dyn_cast<llvm::Argument>(v)) {

        // argument_value : Nat -> value_decomposition
	x = alloc_cnstr(2, 1, 0);
	cnstr_set(x, 0, box(a->getArgNo()));

    } else if (auto b = llvm::dyn_cast<llvm::BasicBlock>(v)) {

        // block_value : BasicBlock -> value_decomposition
        inc_ref( v_obj );
	x = alloc_cnstr(3, 1, 0);
	cnstr_set(x, 0, v_obj);

    } else if (auto i = llvm::dyn_cast<llvm::Instruction>(v)) {

	// instruction_value : llvm.code.instr -> Instruction -> value_decomposition
        inc_ref( v_obj );
	x = alloc_cnstr(4, 1, 0);
	cnstr_set(x, 0, v_obj);

    } else {
        // unknown_value  : value_decomposition

      llvm::raw_os_ostream ros(std::cout);
      ros << "Unknown value! " << v->getValueID() << "\n";
      v->print( ros );
      x= alloc_cnstr(0,0,0);
    }

    return set_io_result(x);
}

obj_res lean_llvm_getConstantTag( b_obj_arg c_obj, obj_arg r ) {
  auto v = toValue(c_obj);
  if( auto c = llvm::dyn_cast<llvm::Constant>(v) ) {
    unsigned int id = v->getValueID();
    return set_io_result( box(id) );
  } else {
    return set_io_error( "expected llvm::Constant value in 'getConstantTag'" );
  }
}

obj_res lean_llvm_getConstantName(b_obj_arg c_obj, obj_arg r) {
    auto v = toValue(c_obj);
    return set_io_result(getOptionalNameObj(v->getValueName()));
}

uint8_t lean_llvm_instructionLt(b_obj_arg x, b_obj_arg y) {
  return toValue(x) < toValue(y);
}

obj_res lean_llvm_getInstructionName(b_obj_arg i_obj, obj_arg r) {
    auto i = toInstruction(i_obj);
    return set_io_result(getOptionalNameObj(i->getValueName()));
}

obj_res lean_llvm_getInstructionType(b_obj_arg i_obj, obj_arg r) {
    auto i = toInstruction(i_obj);
    return set_io_result(allocTypeObj(i->getType()));
}

obj_res lean_llvm_getInstructionOpcode(b_obj_arg i_obj, obj_arg r) {
    auto i = toInstruction(i_obj);
    unsigned int opcode = i->getOpcode();
    return set_io_result( box( opcode ) );
}

obj_res lean_llvm_getInstructionReturnValue(b_obj_arg i_obj, obj_arg r) {
    auto i = toInstruction(i_obj);
    auto parent = valueParent(i_obj);
    auto ri = llvm::dyn_cast<llvm::ReturnInst>(i);
    if (!ri) {
	return set_io_result( mk_option_none());
    }

    llvm::Value* v = ri->getReturnValue();
    if (!v) {
	return set_io_result( mk_option_none());
    }

    obj_res v_obj = allocValueObj(parent,v);
    return set_io_result( mk_option_some(v_obj));
}

obj_res lean_llvm_getBinaryOperatorValues(b_obj_arg i_obj, obj_arg r) {
    auto i = toInstruction(i_obj);
    auto parent = valueParent(i_obj);
    auto bop = llvm::dyn_cast<llvm::BinaryOperator>(i);
    if (!bop || bop->getNumOperands() != 2) {
	return set_io_result( mk_option_none());

    }
    obj_res v1_obj = allocValueObj(parent, bop->getOperand(0));
    obj_res v2_obj = allocValueObj(parent, bop->getOperand(1));
    obj_res pair = mk_pair(v1_obj, v2_obj);
    return set_io_result( mk_option_some(pair));
}

obj_res lean_llvm_getICmpInstData(b_obj_arg i_obj, obj_arg r) {
    auto i = toInstruction(i_obj);
    auto parent = valueParent(i_obj);
    auto ci = llvm::dyn_cast<llvm::CmpInst>(i);

    if (!ci || (ci->getNumOperands() != 2)) {
	return set_io_result(mk_option_none());
    }

    llvm::CmpInst::Predicate pred = ci->getPredicate();
    if(! (llvm::CmpInst::FIRST_ICMP_PREDICATE <= pred && pred <= llvm::CmpInst::LAST_ICMP_PREDICATE) ) {
      return set_io_result( mk_option_none() );
    }

    unsigned int icmpOp =
      static_cast<unsigned int>( pred ) -
      static_cast<unsigned int>( llvm::CmpInst::FIRST_ICMP_PREDICATE );

    obj_res v1_obj = allocValueObj(parent, ci->getOperand(0));
    obj_res v2_obj = allocValueObj(parent, ci->getOperand(1));

    obj_res tuple = mk_pair(box(icmpOp), mk_pair(v1_obj, v2_obj));

    return set_io_result(mk_option_some(tuple));
}

obj_res lean_llvm_getBranchInstData(b_obj_arg i_obj, obj_arg r) {
    auto i = toInstruction(i_obj);
    auto parent = valueParent(i_obj);
    auto bi = llvm::dyn_cast<llvm::BranchInst>(i);
    if (!bi) {
	return set_io_result(mk_option_none());
    }

    if (bi->getNumSuccessors() == 1) {
      obj_res b_obj = allocBasicBlockObj( parent, bi->getSuccessor(0) );

	obj_res x = alloc_cnstr(0, 1, 0);
	cnstr_set(x, 0, b_obj);

	return set_io_result( mk_option_some(x));

    } else if (bi->getNumSuccessors() == 2) {
	obj_res x = alloc_cnstr(1, 3, 0);

	obj_res c_obj = allocValueObj( parent, bi->getCondition() );
	obj_res t_obj = allocBasicBlockObj( parent, bi->getSuccessor(0) );
	obj_res f_obj = allocBasicBlockObj( parent, bi->getSuccessor(1) );

	cnstr_set(x, 0, c_obj);
	cnstr_set(x, 1, t_obj);
	cnstr_set(x, 2, f_obj);

	return set_io_result(mk_option_some(x));
    } else {
	return set_io_result(mk_option_none());
    }
}

obj_res lean_llvm_getGEPData( b_obj_arg i_obj, obj_arg r ) {
  auto i = toInstruction(i_obj);
  auto parent = valueParent(i_obj);
  auto gep = llvm::dyn_cast<llvm::GetElementPtrInst>(i);
  if( !gep ) {
    return set_io_result( mk_option_none() );
  }

  obj_res inbounds;
  if( gep->isInBounds() ) {
    inbounds = alloc_cnstr( 1, 0, 0 );
  } else {
    inbounds = alloc_cnstr( 0, 0, 0 );
  }

  obj_res base_obj = allocValueObj(parent, gep->getPointerOperand());

  obj_res arr = alloc_array( 0, 0 );
  for( llvm::Use &u : gep->indices() ) {
    arr = array_push( arr, allocValueObj( parent, u.get() ));
  }

  obj_res tuple = mk_pair( inbounds, mk_pair( base_obj, arr ) );
  return set_io_result( mk_option_some( tuple ) );
}

obj_res lean_llvm_getAllocaData(b_obj_arg i_obj, obj_arg r) {
    auto i = toInstruction(i_obj);
    auto parent = valueParent(i_obj);
    auto ai = llvm::dyn_cast<llvm::AllocaInst>(i);
    if (!ai) {
        return set_io_result(mk_option_none());
    }

    obj_res tp_obj = allocTypeObj(ai->getAllocatedType());

    obj_res nelems
	= ai->isArrayAllocation()
        ? nelems = mk_option_some(allocValueObj(parent, ai->getArraySize()))
	: mk_option_none();

    obj_res align = mk_option_some(box(ai->getAlignment()));

    obj_res tuple = mk_pair(tp_obj, mk_pair(nelems, align));

    return set_io_result(mk_option_some(tuple));
}

obj_res lean_llvm_getStoreData (b_obj_arg i_obj, obj_arg r) {

    auto i = toInstruction(i_obj);
    auto parent = valueParent(i_obj);

    auto si = llvm::dyn_cast<llvm::StoreInst>(i);
    if (!si) {
	return set_io_result(mk_option_none());
    }

    obj_res val_obj = allocValueObj(parent, si->getValueOperand());
    obj_res ptr_obj = allocValueObj(parent, si->getPointerOperand());
    obj_res align = mk_option_some(box(si->getAlignment()));

    obj_res tuple = mk_pair(val_obj, mk_pair(ptr_obj, align));

    return set_io_result(mk_option_some(tuple));
}

obj_res lean_llvm_getLoadData(b_obj_arg i_obj, obj_arg r) {
    auto i = toInstruction(i_obj);
    auto parent = valueParent(i_obj);
    auto li = llvm::dyn_cast<llvm::LoadInst>(i);
    if (!li) {
	return set_io_result(mk_option_none());
    }

    llvm::Value* ptr = li->getPointerOperand();

    obj_res ptr_obj = allocValueObj(parent, ptr);
    obj_res align = mk_option_some(box(li->getAlignment()));

    obj_res pair  = mk_pair(ptr_obj, align);
    return set_io_result(mk_option_some(pair));
}

obj_res lean_llvm_getCastInstData(b_obj_arg i_obj, obj_arg r) {
    auto i = toInstruction(i_obj);
    auto parent = valueParent(i_obj);
    auto ci = llvm::dyn_cast<llvm::CastInst>(i);
    if (!ci) {
	return set_io_result(mk_option_none());
    }

    unsigned int opcode = static_cast<unsigned int>(ci->getOpcode());

    obj_res pair = mk_pair(box(opcode), allocValueObj(parent, ci->getOperand(0)));
    return set_io_result(mk_option_some(pair));
}


obj_res lean_llvm_getCallInstData( b_obj_arg i_obj, obj_arg r ) {
  auto i = toInstruction(i_obj);
  auto parent = valueParent(i_obj);
  auto ci = llvm::dyn_cast<llvm::CallInst>(i);
  if(!ci) {
    return set_io_result( mk_option_none() );
  }

  bool tailcall = ci->isTailCall();
  llvm::Type *retty = ci->getType();
  llvm::Value *val = ci->getCalledOperand();

  unsigned n = ci->getNumArgOperands();
  obj_res arr = alloc_array(n, n);
  auto p = array_cptr(arr);
  for(unsigned i = 0; i<n; i++) {
    auto v = ci->getArgOperand(i);
    *(p++) = allocValueObj(parent, v);
  }

  obj_res tuple =
    mk_pair( box(tailcall),
    mk_pair( allocTypeObj(retty),
    mk_pair( allocValueObj(parent, val),
             arr )));

  return set_io_result(mk_option_some( tuple ));
}

obj_res lean_llvm_getSelectInstData(b_obj_arg i_obj, obj_arg r) {
    auto i = toInstruction(i_obj);
    auto parent = valueParent(i_obj);
    auto si = llvm::dyn_cast<llvm::SelectInst>(i);
    if (!si) {
	return set_io_result(mk_option_none());
    }

    obj_res tuple =
      mk_pair(allocValueObj(parent, si->getCondition()),
	      mk_pair(allocValueObj(parent, si->getTrueValue()),
		      allocValueObj(parent, si->getFalseValue())));
    return set_io_result(mk_option_some(tuple));

}

obj_res lean_llvm_hasNoUnsignedWrap(b_obj_arg i_obj, obj_arg r) {
    auto i = toInstruction(i_obj);
    bool b = i->hasNoUnsignedWrap();
    return set_io_result(box(b));
}

obj_res lean_llvm_hasNoSignedWrap(b_obj_arg i_obj, obj_arg r) {
    auto i = toInstruction(i_obj);
    bool b = i->hasNoSignedWrap();
    return set_io_result(box(b));
}

obj_res lean_llvm_isExact(b_obj_arg i_obj, obj_arg r) {
    auto i = toInstruction(i_obj);
    bool b = i->isExact();
    return set_io_result(box(b));
}

uint8_t lean_llvm_basicBlockLt(b_obj_arg x, b_obj_arg y) {
    return toValue(x) < toValue(y);
}

obj_res lean_llvm_getPhiData(b_obj_arg i_obj, obj_arg r) {
    auto i = toInstruction(i_obj);
    auto parent = valueParent(i_obj);
    auto phi = llvm::dyn_cast<llvm::PHINode>(i);
    if (!phi) {
	return set_io_result(mk_option_none());
    }

    size_t n = phi->getNumIncomingValues();

    obj_res arr = alloc_array(n, n);
    auto p = array_cptr(arr);
    for(unsigned i = 0; i<n; i++) {
	auto v = phi->getIncomingValue(i);
	auto bb = phi->getIncomingBlock(i);

	*(p++) = mk_pair(allocValueObj(parent, v), allocBasicBlockObj(parent, bb));
    }

    return set_io_result( mk_option_some(arr));
}

obj_res lean_llvm_getBBName (b_obj_arg f, obj_arg r) {
    auto bb = toBasicBlock(f);
    return set_io_result(getOptionalNameObj(bb->getValueName()));
}

obj_res lean_llvm_getInstructionArray(b_obj_arg bb_obj, obj_arg r) {
    auto bb = toBasicBlock(bb_obj);
    auto parent = valueParent(bb_obj);

    obj_res arr = alloc_array(0, 0);
    for (llvm::Instruction &i : *bb) {
      obj_res instr_obj = allocInstructionObj( parent, &i );
      arr = array_push(arr, instr_obj);
    }

    return set_io_result(arr);
}

obj_res lean_llvm_newFunction( obj_arg m_obj, b_obj_arg tp_obj, b_obj_arg nm_obj, obj_arg r ) {
  auto mod = toModule(m_obj);
  auto tp  = toType(tp_obj);
  auto str = asStringRef(nm_obj);

  auto linkage = llvm::GlobalValue::LinkageTypes::ExternalLinkage;

  if( auto fnty = llvm::dyn_cast<llvm::FunctionType>(tp) ) {
    llvm::Twine tw( str );
    llvm::Function* f = llvm::Function::Create( fnty, linkage, tw, mod );

    obj_arg f_obj = allocFunctionObj( m_obj, f );
    return set_io_result( f_obj );
  }

  return set_io_error( mk_string("Expected function type in newFunction") );
}

obj_res lean_llvm_getFunctionName(b_obj_arg f, obj_arg r) {
    auto fun = toFunction(f);
    std::string str = fun->getValueName()->getKey().str();
    return set_io_result( mk_string(str));
}

obj_res lean_llvm_getFunctionArgs(b_obj_arg f, obj_arg r) {
    auto args = toFunction(f)->args();
    size_t sz = args.end() - args.begin();

    obj_res arr = alloc_array(sz, sz);
    auto p = array_cptr(arr);
    for (llvm::Argument& arg : args) {
	*(p++) = mk_pair(getOptionalNameObj(arg.getValueName()),
			 allocTypeObj(arg.getType()));
    }

    return set_io_result(arr);
}

obj_res lean_llvm_getReturnType(b_obj_arg f, obj_arg r) {
  return set_io_result(allocTypeObj(toFunction(f)->getReturnType()));
}

obj_res lean_llvm_getBasicBlockArray(b_obj_arg f, obj_arg r) {
    auto& bblist = toFunction(f)->getBasicBlockList();
    auto parent = valueParent(f);

    size_t sz = bblist.size();
    obj_res arr = alloc_array(sz, sz);
    auto p = array_cptr(arr);
    for(llvm::BasicBlock& bb : bblist) {
      *(p++) = allocBasicBlockObj(parent, &bb);
    }
    return set_io_result(arr);
}

obj_res lean_llvm_getGlobalVarData( b_obj_arg gv_obj, obj_arg r ) {
  auto gv = toGlobalVar(gv_obj);
  auto parent = valueParent(gv_obj);
  if( !gv ) {
    return set_io_result( mk_option_none() );
  }
  
  auto nm = mk_string(gv->getValueName()->getKey());

  obj_res val;
  if( gv->hasInitializer() ) {
    val = mk_option_some( allocValueObj( parent, gv->getInitializer() ));
  } else {
    val = mk_option_none();
  }

  unsigned align = gv->getAlignment();

  return set_io_result( mk_option_some( mk_pair( nm, mk_pair( val, box(align) ) )));
}
}


extern "C" {

obj_res lean_llvm_parseBitcodeFile(obj_arg b, b_obj_arg ctxObj, obj_arg r) {
    auto ctx = toLLVMContext(ctxObj);
    llvm::MemoryBufferRef buf = toMemoryBuffer(b)->getMemBufferRef();

    auto moduleOrErr = parseBitcodeFile(buf, *ctx);
    if (!moduleOrErr) {
	dec_ref(ctxObj);
	return set_io_error( errorMsgObj(moduleOrErr.takeError()));
    }

    return set_io_result(allocModuleObj(ctxObj, std::move(*moduleOrErr)));
}

obj_res lean_llvm_newModule( obj_arg ctxObj, obj_arg nmObj, obj_arg r ) {
  auto ctx = toLLVMContext(ctxObj);
  auto nm  = asStringRef( nmObj );

  auto mod = new llvm::Module( nm, *ctx );
  auto modObj = allocModuleObj( ctxObj, std::unique_ptr<llvm::Module>(mod) );

  return set_io_result( modObj );
}

obj_res lean_llvm_printModule( obj_arg modObj, obj_arg r ) {
  auto mod = toModule(modObj);

  llvm::raw_os_ostream ros(std::cout);
  mod->print( ros, nullptr );

  return set_io_result( box(0) );
}


obj_res lean_llvm_initNativeFns(obj_arg r) {
    LLVM_NATIVE_TARGETINFO();
    LLVM_NATIVE_TARGETMC();
    LLVM_NATIVE_TARGET();
    LLVM_NATIVE_ASMPRINTER();
    return set_io_result(box(0));
}

obj_res lean_llvm_getModuleIdentifier(b_obj_arg m, obj_arg r) {
    return set_io_result(mk_string(toModule(m)->getModuleIdentifier()));
}

obj_res lean_llvm_setModuleIdentifier(b_obj_arg m, b_obj_arg nm, obj_arg r) {
    toModule(m)->setModuleIdentifier(string_to_std(nm));
    return set_io_result(box(0));
}

obj_res lean_llvm_getModuleDataLayoutStr(b_obj_arg m, obj_arg r) {
    return set_io_result(mk_string(toModule(m)->getDataLayoutStr()));
}

obj_res lean_llvm_getFunctionArray (b_obj_arg m, obj_arg r) {
    llvm::Module::FunctionListType& flist = toModule(m)->getFunctionList();

    size_t sz = flist.size();
    obj_res arr = alloc_array(sz, sz);
    auto p = array_cptr(arr);
    for (llvm::Function& f : flist) {
	*(p++) = allocFunctionObj(m, &f);
    }

    return set_io_result(arr);
}

obj_res lean_llvm_getGlobalArray (b_obj_arg m, obj_arg r) {
    llvm::Module::GlobalListType& gvlist = toModule(m)->getGlobalList();

    size_t sz = gvlist.size();
    obj_res arr = alloc_array(sz, sz);
    auto p = array_cptr(arr);
    for (llvm::GlobalVariable& gv : gvlist) {
	*(p++) = allocGlobalVarObj(m, &gv);
    }

    return set_io_result(arr);
}


obj_res lean_llvm_getConstIntData(b_obj_arg c_obj, obj_arg r) {
    auto cint = llvm::dyn_cast<llvm::ConstantInt>(toValue(c_obj));
    if (!cint) {
	return set_io_result(mk_option_none());
    }

    unsigned width = cint->getBitWidth();
    obj_res val_obj;

    if (width <= 64) {
	uint64_t val = cint->getValue().getZExtValue();
	if (val <= LEAN_MAX_SMALL_NAT) {
	    val_obj = box(val);
	} else {
	    val_obj = mk_nat_obj_core(mpz(val));
	}
    } else {
	unsigned int i = cint->getValue().getNumWords();

	if (i == 0) {
	    val_obj = box(0);

	} else if (i == 1) {

	    // list of 64-bit limbs in little-endian order
	    const uint64_t *rawvals = cint->getValue().getRawData();
	    uint64_t val = rawvals[0];
	    val_obj
	       = (val <= LEAN_MAX_SMALL_NAT)
	       ? box(val)
	       : mk_nat_obj_core(mpz(val));
	} else {

	    // list of 64-bit limbs in little-endian order
	    const uint64_t *rawvals = cint->getValue().getRawData();
	    mpz *m = new mpz(rawvals[--i]);

	    while (i-- > 0) {
		mul2k(*m, *m, 64);
		*m |= mpz(rawvals[i]);
	    }

	    val_obj = mk_nat_obj_core(*m);
	}
    }

    obj_res pair = mk_pair(box(width), val_obj);
    return set_io_result(mk_option_some(pair));
}

obj_res lean_llvm_getConstExprData (b_obj_arg c_obj, obj_arg r ) {
  auto parent = valueParent(c_obj);
  auto cexpr = llvm::dyn_cast<llvm::ConstantExpr>(toValue(c_obj));
  if( !cexpr ) {
    return set_io_result(mk_option_none() );
  }

  unsigned opcode = cexpr->getOpcode();
  unsigned sz = cexpr->getNumOperands();

  obj_res arr = alloc_array(sz, sz);
  auto p = array_cptr(arr);

  for( unsigned i=0; i<sz; i++ ) {
    auto cop = llvm::dyn_cast<llvm::Constant>( cexpr->getOperand(i) );
    if( cop ) {
      *(p++) = allocValueObj(parent, cop);
    } else {
      // FIXME... leaks memory here?
      return set_io_error( mk_string("Expected constant value argument to constant expr!") );
    }
  }
  return set_io_result( mk_option_some( mk_pair( box(opcode), arr )) );
}

obj_res lean_llvm_getConstArrayData( b_obj_arg c_obj, obj_arg r ) {
  auto parent = valueParent( c_obj );
  auto carr = llvm::dyn_cast<llvm::ConstantDataSequential>(toValue(c_obj));

  if( !carr ) {
    return set_io_result( mk_option_none() );
  }

  auto elty = allocTypeObj(carr->getElementType());

  unsigned sz = carr->getNumElements();
  obj_res arr = alloc_array( sz, sz );
  auto p = array_cptr(arr);

  for( unsigned i = 0; i<sz; i++ ) {
    auto elem = carr->getElementAsConstant( i );
    *(p++) = allocValueObj( parent, elem );
  }

  return set_io_result(mk_option_some( mk_pair( elty, arr )));
}


/** Return a String object with a process triple. */
obj_res lean_llvm_getProcessTriple(b_obj_arg unit) {
    return mk_string(llvm::sys::getProcessTriple());
}

/** Create a triple object from the provided string. */
obj_res lean_llvm_newTriple(b_obj_arg str) {
    return alloc_external(getTripleClass(), new llvm::Triple(string_cstr(str)));
}

}
