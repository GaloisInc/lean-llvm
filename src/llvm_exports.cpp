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
#include <llvm/Support/TargetSelect.h>

#include <runtime/apply.h>
#include <runtime/io.h>
#include <runtime/mpz.h>
#include <runtime/utf8.h>


////////////////////////////////////////////////////////////////////////
// Import lean

using namespace lean;

////////////////////////////////////////////////////////////////////////
// LLVM Specific

namespace lean_llvm {

/* Create a pair from the two arguments. */
static
inline obj_res mk_pair(obj_arg x, obj_arg y) {
    obj_res r = alloc_cnstr(0, 2, 0);
    cnstr_set(r, 0, x);
    cnstr_set(r, 1, y);
    return r;
}

////////////////////////////////////////////////////////////////////////
// StringRef

static inline char * w_string_cstr(object * o) {
    lean_assert(is_string(o));
    return reinterpret_cast<char *>(o) + sizeof(string_object);
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


template<typename T>
class OwnedPtr {
    T* ptrVal;
    object* parentObj;
    OwnedPtr() = delete;
    OwnedPtr(const OwnedPtr&) = delete;
public:

    /** Construct an owned ptr.  We assume the object reference count has been incremented. */
    OwnedPtr(obj_arg par, T* p)
	: ptrVal(p), parentObj(par) {

    }

    ~OwnedPtr() {
	dec_ref(parentObj);
    }

    object* parent() {
	return parentObj;
    }

    T* ptr() {
	return ptrVal;
    }
};

// Casts to given type and invokes delete
template<typename T>
void ownedForeach(void * p, b_obj_arg a) {
    auto d = static_cast<OwnedPtr<T>*>(p);
    apply_1(a, d->parent());
}

// Casts to given type and invokes delete
template<typename T>
void ownedFinalize(void* p) {
    delete static_cast<OwnedPtr<T>*>(p);
}

// Register a class whose lifetime is controlled by another object.  It holds
// a reference to the owner while alive and releases it when finalized.
template<typename T>
static
external_object_class* registerOwnedClass() {
    return register_external_object_class(&ownedFinalize<T>, &ownedForeach<T>);
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

/** Create a new LLVM context object. */
obj_res newLLVMContext(obj_arg r) {
    auto ctx = new llvm::LLVMContext();
    object* ctxObj = alloc_external(getLLVMContextClass(), ctx);
    return set_io_result(r, ctxObj);
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

obj_res newMemoryBufferFromFile(b_obj_arg fname, obj_arg r) {
    const char* path = string_cstr(fname);

    auto MBOrErr = llvm::MemoryBuffer::getFile(path);
    if (std::error_code EC = MBOrErr.getError()) {
	return set_io_error(r, mk_string(EC.message()));
    }

 auto b = std::move(MBOrErr.get());
    object* bufferObj = alloc_external(getMemoryBufferClass(), b.get());
    b.release();
    return set_io_result(r, bufferObj);
}



////////////////////////////////////////////////////////////////////////
// Types

static inline
obj_res allocTypeObj(llvm::Type* tp) {
    return alloc_external(getTrivialObjectClass(), tp);
}

static inline
llvm::Type* toType(b_obj_arg o) {
    lean_assert(external_class(o) == getTrivialObjectClass());
    return static_cast<llvm::Type*>(external_data(o));
}

obj_res getTypeTag(b_obj_arg tp_obj, obj_arg r) {
    auto tp = toType(tp_obj);
    llvm::Type::TypeID id = tp->getTypeID();
    obj_res n = box(id);
    return set_io_result(r, n);
}

obj_res getIntegerTypeWidth(b_obj_arg tp_obj, obj_arg r) {
    auto tp = toType(tp_obj);
    unsigned int w = tp->getIntegerBitWidth();
    obj_res w_obj = box(w); // TODO, overflow?
    return set_io_result(r, w_obj);
}

obj_res getPointerElementType(b_obj_arg tp_obj, obj_arg r) {
    auto tp = toType(tp_obj);
    llvm::PointerType *pt = llvm::dyn_cast<llvm::PointerType>(tp);
    if (!pt) {
	return set_io_result(r, mk_option_none());
    }

    llvm::Type* elt_tp = pt->getElementType();
    obj_res elt_tp_obj = alloc_external(getTrivialObjectClass(), elt_tp);
    return set_io_result(r, mk_option_some(elt_tp_obj));
}


////////////////////////////////////////////////////////////////////////
// Values

obj_res getOptionalNameObj(llvm::ValueName* nm) {
    return (nm == nullptr)
	? mk_option_none()
	: mk_option_some(mk_string(nm->getKey()));
}

obj_res allocValueObj(llvm::Value* v) {
    //FIXME: Manage parent liftime.
    return alloc_external(getTrivialObjectClass(), v);
}

static
llvm::Value* toValue(b_obj_arg o) {
    return static_cast<llvm::Value*>(external_data(o));
}

obj_res getValueType(b_obj_arg v_obj, obj_arg r) {
    auto tp = toValue(v_obj)->getType();
    return set_io_result(r,allocTypeObj(tp));
}

obj_res decomposeValue(b_obj_arg v_obj, obj_arg r) {
    auto v = toValue(v_obj);
    obj_res x;
    if (auto a = llvm::dyn_cast<llvm::Argument>(v)) {

	x = alloc_cnstr(1, 0, 0);
	cnstr_set(x, 0, box(a->getArgNo()));

    } else if (auto i = llvm::dyn_cast<llvm::Instruction>(v)) {
	obj_res i_obj = alloc_external(getTrivialObjectClass(), i);
	x = alloc_cnstr(2, 0, 0);
	cnstr_set(x, 0, i_obj);

    } else if (auto c = llvm::dyn_cast<llvm::Constant>(v)) {

	obj_res c_obj = alloc_external(getTrivialObjectClass(), c);
	x = alloc_cnstr(3, 0, 0);
	cnstr_set(x, 0, c_obj);

    } else {
	x = alloc_cnstr(0,0,0);
    }

    return set_io_result(r, x);
}

////////////////////////////////////////////////////////////////////////
// Instructions

static
llvm::Instruction* toInstruction(b_obj_arg o) {
    auto v = toValue(o);
    return llvm::dyn_cast<llvm::Instruction>(v);
}

uint8_t instructionLt(b_obj_arg x, b_obj_arg y) {
    return external_data(x) < external_data(y);
}

obj_res getInstructionName(b_obj_arg i_obj, obj_arg r) {
    auto i = toInstruction(i_obj);
    return set_io_result(r, getOptionalNameObj(i->getValueName()));
}

obj_res getInstructionType(b_obj_arg i_obj, obj_arg r) {
    auto i = toInstruction(i_obj);
    return set_io_result(r, allocTypeObj(i->getType()));
}

obj_res getInstructionOpcode(b_obj_arg i_obj, obj_arg r) {
    auto i = toInstruction(i_obj);
    unsigned int opcode = i->getOpcode();
    return set_io_result(r, box(opcode));
}

obj_res getInstructionReturnValue(b_obj_arg i_obj, obj_arg r) {
    auto i = toInstruction(i_obj);
    auto ri = llvm::dyn_cast<llvm::ReturnInst>(i);
    if (!ri) {
	return set_io_result(r, mk_option_none());
    }

    llvm::Value* v = ri->getReturnValue();
    if (!v) {
	return set_io_result(r, mk_option_none());
    }

    obj_res v_obj = allocValueObj(v);
    return set_io_result(r, mk_option_some(v_obj));
}

obj_res getBinaryOperatorValues(b_obj_arg i_obj, obj_arg r) {
    auto i = toInstruction(i_obj);
    auto bop = llvm::dyn_cast<llvm::BinaryOperator>(i);
    if (!bop || bop->getNumOperands() != 2) {
	return set_io_result(r, mk_option_none());

    }
    obj_res v1_obj = allocValueObj(bop->getOperand(0));
    obj_res v2_obj = allocValueObj(bop->getOperand(1));
    obj_res pair = mk_pair(v1_obj, v2_obj);
    return set_io_result(r, mk_option_some(pair));
}

obj_res getCmpInstData(b_obj_arg i_obj, obj_arg r) {
    auto i = toInstruction(i_obj);
    auto ci = llvm::dyn_cast<llvm::CmpInst>(i);

    if (!ci || (ci->getNumOperands() != 2)) {
	return set_io_result(r, mk_option_none());
    }

    unsigned int cmpOp = static_cast<unsigned int>(ci->getPredicate());
    obj_res v1_obj = allocValueObj(ci->getOperand(0));
    obj_res v2_obj = allocValueObj(ci->getOperand(1));

    obj_res tuple = mk_pair(box(cmpOp), mk_pair(v1_obj, v2_obj));

    return set_io_result(r, mk_option_some(tuple));
}

obj_res getBranchInstData(b_obj_arg i_obj, obj_arg r) {
    auto i = toInstruction(i_obj);
    auto bi = llvm::dyn_cast<llvm::BranchInst>(i);
    if (!bi) {
	return set_io_result(r, mk_option_none());
    }

    if (bi->getNumSuccessors() == 1) {
	obj_res b_obj = alloc_external(getTrivialObjectClass(), bi->getSuccessor(0));

	obj_res x = alloc_cnstr(0, 1, 0);
	cnstr_set(x, 0, b_obj);

	return set_io_result(r, mk_option_some(x));

    } else if (bi->getNumSuccessors() == 2) {
	obj_res x = alloc_cnstr(1, 3, 0);

	obj_res c_obj = alloc_external(getTrivialObjectClass(), bi->getCondition());
	obj_res t_obj = alloc_external(getTrivialObjectClass(), bi->getSuccessor(0));
	obj_res f_obj = alloc_external(getTrivialObjectClass(), bi->getSuccessor(1));

	cnstr_set(x, 0, c_obj);
	cnstr_set(x, 1, t_obj);
	cnstr_set(x, 2, f_obj);

	return set_io_result(r, mk_option_some(x));
    } else {
	return set_io_result(r, mk_option_none());
    }
}

obj_res getGEPData( b_obj_arg i_obj, obj_arg r ) {
  auto i = toInstruction(i_obj);
  auto gep = llvm::dyn_cast<llvm::GetElementPtrInst>(i);
  if( !gep ) {
    return set_io_result( r, mk_option_none() );
  }

  obj_res inbounds;
  if( gep->isInBounds() ) {
    inbounds = alloc_cnstr( 1, 0, 0 );
  } else {
    inbounds = alloc_cnstr( 0, 0, 0 );
  }

  obj_res base_obj = allocValueObj(gep->getPointerOperand());

  obj_res arr = alloc_array( 0, 0 );
  for( llvm::Use &u : gep->indices() ) {
    arr = array_push( arr, allocValueObj( u.get() ));
  }

  obj_res tuple = mk_pair( inbounds, mk_pair( base_obj, arr ) );
  return set_io_result( r, mk_option_some( tuple ) );
}

obj_res getAllocaData(b_obj_arg i_obj, obj_arg r) {
    auto i = toInstruction(i_obj);
    auto ai = llvm::dyn_cast<llvm::AllocaInst>(i);
    if (!ai) {
        return set_io_result(r, mk_option_none());
    }

    obj_res tp_obj = allocTypeObj(ai->getAllocatedType());

    obj_res nelems
	= ai->isArrayAllocation()
	? nelems = mk_option_some(allocValueObj(ai->getArraySize()))
	: mk_option_none();

    obj_res align = mk_option_some(box(ai->getAlignment()));

    obj_res tuple = mk_pair(tp_obj, mk_pair(nelems, align));

    return set_io_result(r, mk_option_some(tuple));
}

obj_res getStoreData (b_obj_arg i_obj, obj_arg r) {

    auto i = toInstruction(i_obj);

    auto si = llvm::dyn_cast<llvm::StoreInst>(i);
    if (!si) {
	return set_io_result(r, mk_option_none());
    }

    obj_res val_obj = allocValueObj(si->getValueOperand());
    obj_res ptr_obj = allocValueObj(si->getPointerOperand());
    obj_res align = mk_option_some(box(si->getAlignment()));

    obj_res tuple = mk_pair(val_obj, mk_pair(ptr_obj, align));

    return set_io_result(r, mk_option_some(tuple));
}

obj_res getLoadData(b_obj_arg i_obj, obj_arg r) {
    auto i = toInstruction(i_obj);
    auto li = llvm::dyn_cast<llvm::LoadInst>(i);
    if (!li) {
	return set_io_result(r, mk_option_none());
    }

    llvm::Value* ptr = li->getPointerOperand();

    obj_res ptr_obj = alloc_external(getTrivialObjectClass(), ptr);
    obj_res align = mk_option_some(box(li->getAlignment()));

    obj_res pair  = mk_pair(ptr_obj, align);
    return set_io_result(r, mk_option_some(pair));
}

obj_res getCastInstData(b_obj_arg i_obj, obj_arg r) {
    auto i = toInstruction(i_obj);
    auto ci = llvm::dyn_cast<llvm::CastInst>(i);
    if (!ci) {
	return set_io_result(r, mk_option_none());
    }

    unsigned int opcode = static_cast<unsigned int>(ci->getOpcode());

    obj_res pair = mk_pair(box(opcode), allocValueObj(ci->getOperand(0)));
    return set_io_result(r, mk_option_some(pair));
}


obj_res getSelectInstData(b_obj_arg i_obj, obj_arg r) {
    auto i = toInstruction(i_obj);
    auto si = llvm::dyn_cast<llvm::SelectInst>(i);
    if (!si) {
	return set_io_result(r, mk_option_none());
    }


    obj_res tuple =
	mk_pair(allocValueObj(si->getCondition()),
		mk_pair(allocValueObj(si->getTrueValue()),
			allocValueObj(si->getFalseValue())));
    return set_io_result(r, mk_option_some(tuple));

}

obj_res hasNoUnsignedWrap(b_obj_arg i_obj, obj_arg r) {
    auto i = toInstruction(i_obj);
    bool b = i->hasNoUnsignedWrap();
    return set_io_result(r, box(b));
}

obj_res hasNoSignedWrap(b_obj_arg i_obj, obj_arg r) {
    auto i = toInstruction(i_obj);
    bool b = i->hasNoSignedWrap();
    return set_io_result(r, box(b));
}

obj_res isExact(b_obj_arg i_obj, obj_arg r) {
    auto i = toInstruction(i_obj);
    bool b = i->isExact();
    return set_io_result(r, box(b));
}

////////////////////////////////////////////////////////////////////////
// Basic blocks

obj_res allocBasicBlockObj(llvm::BasicBlock* bb) {
    return alloc_external(getTrivialObjectClass(), bb);
}

llvm::BasicBlock* toBasicBlock(b_obj_arg o) {
    return llvm::dyn_cast<llvm::BasicBlock>(toValue(o));
}


uint8_t basicBlockLt(b_obj_arg x, b_obj_arg y) {
    return external_data(x) < external_data(y);
}

obj_res getPhiData(b_obj_arg i_obj, obj_arg r) {
    auto i = toInstruction(i_obj);
    auto phi = llvm::dyn_cast<llvm::PHINode>(i);
    if (!phi) {
	return set_io_result(r, mk_option_none());
    }

    size_t n = phi->getNumIncomingValues();

    obj_res arr = alloc_array(n, n);
    auto p = array_cptr(arr);
    for(unsigned i = 0; i<n; i++) {
	auto v = phi->getIncomingValue(i);
	auto bb = phi->getIncomingBlock(i);

	*(p++) = mk_pair(allocValueObj(v), allocBasicBlockObj(bb));
    }

    return set_io_result(r, mk_option_some(arr));
}

obj_res getBBName (b_obj_arg f, obj_arg r) {
    auto bb = toBasicBlock(f);
    return set_io_result(r, getOptionalNameObj(bb->getValueName()));
}

obj_res getInstructionArray(b_obj_arg bb_obj, obj_arg r) {
    auto bb = toBasicBlock(bb_obj);

    obj_res arr = alloc_array(0, 0);
    for (llvm::Instruction &i : *bb) {
	obj_res instr_obj = alloc_external(getTrivialObjectClass(), &i);
	arr = array_push(arr, instr_obj);
    }

    return set_io_result(r, arr);
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

static
external_object_class* getFunctionObjectClass() {
    // Use static thread to make this thread safe due to static initialization rule.
    static
	external_object_class* c(register_external_object_class(&ownedExternalFinalize<llvm::Function>,
								&ownedExternalForeach<llvm::Function>));
    return c;
}

////////////////////////////////////////////////////////////////////////
// Functions

// Allocate a function object (the parent lifetime should exceed this objects).
obj_res allocFunctionObj(obj_arg parent, llvm::Function* f) {
    //FIXME: Manage parent liftime.
    auto e = new OwnedExternal<llvm::Function>(parent, f);
    return alloc_external(getFunctionObjectClass(), e);
}

llvm::Function* toFunction(b_obj_arg o) {
    lean_assert(external_class(o) == getFunctionObjectClass());
    return static_cast<OwnedExternal<llvm::Function>*>(external_data(o))->value;
}


obj_res getFunctionName(b_obj_arg f, obj_arg r) {
    auto fun = toFunction(f);
    std::string str = fun->getValueName()->getKey().str();
    return set_io_result(r, mk_string(str));
}

obj_res getFunctionArgs(b_obj_arg f, obj_arg r) {
    auto args = toFunction(f)->args();
    size_t sz = args.end() - args.begin();

    obj_res arr = alloc_array(sz, sz);
    auto p = array_cptr(arr);
    for (llvm::Argument& arg : args) {
	*(p++) = mk_pair(getOptionalNameObj(arg.getValueName()),
			 allocTypeObj(arg.getType()));
    }

    return set_io_result(r, arr);
}

obj_res getReturnType(b_obj_arg f, obj_arg r) {
    return set_io_result(r, allocTypeObj(toFunction(f)->getReturnType()));
}

obj_res getBasicBlockArray(b_obj_arg f, obj_arg r) {
    auto& bblist = toFunction(f)->getBasicBlockList();

    size_t sz = bblist.size();
    obj_res arr = alloc_array(sz, sz);
    auto p = array_cptr(arr);
    for(llvm::BasicBlock& bb : bblist) {
	*(p++) = allocBasicBlockObj(&bb);
    }
    return set_io_result(r, arr);
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

obj_res parseBitcodeFile(obj_arg b, b_obj_arg ctxObj, obj_arg r) {
    auto ctx = toLLVMContext(ctxObj);
    llvm::MemoryBufferRef buf = toMemoryBuffer(b)->getMemBufferRef();

    auto moduleOrErr = parseBitcodeFile(buf, *ctx);
    if (!moduleOrErr) {
	dec_ref(ctxObj);
	return set_io_error(r, errorMsgObj(moduleOrErr.takeError()));
    }

    return set_io_result(r, allocModuleObj(ctxObj, std::move(*moduleOrErr)));
}

obj_res initNativeFns(obj_arg r) {
    LLVM_NATIVE_TARGETINFO();
    LLVM_NATIVE_TARGETMC();
    LLVM_NATIVE_TARGET();
    LLVM_NATIVE_ASMPRINTER();
    return set_io_result(r, box(0));
}

obj_res getModuleIdentifier(b_obj_arg m, obj_arg r) {
    return set_io_result(r, mk_string(toModule(m)->getModuleIdentifier()));
}

obj_res setModuleIdentifier(b_obj_arg m, b_obj_arg nm, obj_arg r) {
    toModule(m)->setModuleIdentifier(string_to_std(nm));
    return set_io_result(r, box(0));
}

obj_res getModuleDataLayoutStr(b_obj_arg m, obj_arg r) {
    return set_io_result(r, mk_string(toModule(m)->getDataLayoutStr()));
}

obj_res getFunctionArray (b_obj_arg m, obj_arg r) {
    llvm::Module::FunctionListType& flist = toModule(m)->getFunctionList();

    size_t sz = flist.size();
    obj_res arr = alloc_array(sz, sz);
    auto p = array_cptr(arr);
    for (llvm::Function& f : flist) {
	*(p++) = allocFunctionObj(m, &f);
    }

    return set_io_result(r, arr);
}

////////////////////////////////////////////////////////////////////////
// Constants

obj_res getConstIntData(b_obj_arg c_obj, obj_arg r) {
    auto cint = llvm::dyn_cast<llvm::ConstantInt>(toValue(c_obj));
    if (!cint) {
	return set_io_result(r, mk_option_none());
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
    return set_io_result(r, mk_option_some(pair));
}


////////////////////////////////////////////////////////////////////////
// Triple

/** Return a String object with a process triple. */
obj_res getProcessTriple(b_obj_arg unit) {
    return mk_string(llvm::sys::getProcessTriple());
}

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

/** Create a triple object from the provided string. */
obj_res newTriple(b_obj_arg str) {
    return alloc_external(getTripleClass(), new llvm::Triple(string_cstr(str)));
}

}
