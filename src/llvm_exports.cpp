#include <cstddef>

#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Instructions.h>
#include <llvm/Support/MemoryBuffer.h>
#include <llvm/Bitcode/BitcodeReader.h>

#include "apply.h"
#include "mpz.h"
#include "object.h"
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

obj_res getModuleDataLayoutStr( b_obj_arg m, obj_arg r ) {
  return set_io_result( r, mk_string(toModule(m)->getDataLayoutStr()) );
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

obj_res getReturnType( b_obj_arg f, obj_arg r) {
  Function *fun = static_cast<Function*>(external_data(f));
  Type *tp = fun->getReturnType();
  obj_res tp_obj = alloc_external( getTrivialObjectClass(), tp );
  return set_io_result( r, tp_obj );
}

obj_res getFunctionArgs( b_obj_arg f, obj_arg r) {
  Function *fun = static_cast<Function*>(external_data(f));

  obj_res arr = alloc_array( 0, 0 );
  for ( Argument &arg : fun->args() ) {
    ValueName *aname = arg.getValueName();
    obj_res aname_obj;
    if (aname == nullptr) {
      aname_obj = mk_option_none();
    } else {
      aname_obj = mk_option_some( mk_string(aname->getKey().str()) );
    }

    Type *tp = arg.getType();
    obj_res tp_obj = alloc_external( getTrivialObjectClass(), tp );

    obj_res tuple = alloc_cnstr( 0, 2, 0 );
    cnstr_set( tuple, 0, aname_obj );
    cnstr_set( tuple, 1, tp_obj );

    arr = array_push( arr, tuple );
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

obj_res getInstructionArray( b_obj_arg bb_obj, obj_arg r ) {
  BasicBlock* bb = static_cast<BasicBlock*>(external_data(bb_obj));

  obj_res arr = alloc_array( 0, 0 );
  for ( Instruction &i : *bb ) {
    obj_res instr_obj = alloc_external( getTrivialObjectClass(), &i );
    arr = array_push( arr, instr_obj );
  }

  return set_io_result( r, arr );
}

obj_res getFunctionName( b_obj_arg f, obj_arg r ) {
  Function *fun = static_cast<Function*>(external_data(f));
  std::string str = fun->getValueName()->getKey().str();
  return set_io_result( r, mk_string(str) );
}

obj_res getTypeTag ( b_obj_arg tp_obj, obj_arg r ) {
  Type* tp = static_cast<Type*>(external_data(tp_obj));
  Type::TypeID id = tp->getTypeID();
  obj_res n = box( id );
  return set_io_result( r, n );
}

obj_res getIntegerTypeWidth( b_obj_arg tp_obj, obj_arg r ) {
  Type* tp = static_cast<Type*>(external_data(tp_obj));
  unsigned int w = tp->getIntegerBitWidth();
  obj_res w_obj = box( w ); // TODO, overflow?
  return set_io_result( r, w_obj );
}


uint8_t instructionLt( b_obj_arg i1_obj, b_obj_arg i2_obj ) {
  Instruction *i1 = static_cast<Instruction*>(external_data(i1_obj));
  Instruction *i2 = static_cast<Instruction*>(external_data(i2_obj));

  bool b = i1 < i2;

  return b;
}

uint8_t basicBlockLt( b_obj_arg bb1_obj, b_obj_arg bb2_obj ) {
  BasicBlock *bb1 = static_cast<BasicBlock*>(external_data(bb1_obj));
  BasicBlock *bb2 = static_cast<BasicBlock*>(external_data(bb2_obj));

  bool b = bb1 < bb2;

  return b;
}


obj_res getInstructionName( b_obj_arg i_obj, obj_arg r ) {
  Instruction *i = static_cast<Instruction*>(external_data(i_obj));

  ValueName *vnm = i->getValueName();
  if( vnm == nullptr ) {
    return set_io_result( r, mk_option_none() );
  } else {
    return set_io_result( r, mk_option_some(mk_string(vnm->getKey().str())) );
  }
}

obj_res getInstructionType( b_obj_arg i_obj, obj_arg r) {
  Instruction *i = static_cast<Instruction*>(external_data(i_obj));
  Type *tp = i->getType();
  obj_res tp_obj = alloc_external( getTrivialObjectClass(), tp );
  return set_io_result( r, tp_obj );
}

obj_res getInstructionOpcode( b_obj_arg i_obj, obj_arg r ) {
  Instruction *i = static_cast<Instruction*>(external_data(i_obj));
  unsigned int opcode = i->getOpcode();
  return set_io_result( r, box(opcode) );
}

obj_res getInstructionReturnValue( b_obj_arg i_obj, obj_arg r ) {
  Instruction *i = static_cast<Instruction*>(external_data(i_obj));
  ReturnInst *ri = dyn_cast<ReturnInst>(i);
  if( ri ) {
    Value* v = ri->getReturnValue();
    if( v ) {
      obj_res v_obj = alloc_external( getTrivialObjectClass(), v );
      return set_io_result( r, mk_option_some( v_obj ) );
    }
  }
  return set_io_result( r, mk_option_none() );
}

obj_res getBinaryOperatorValues( b_obj_arg i_obj, obj_arg r ) {
  Instruction *i = static_cast<Instruction*>(external_data(i_obj));
  BinaryOperator *bop = dyn_cast<BinaryOperator>(i);
  if( bop && bop->getNumOperands() == 2 ) {
    Value *v1 = bop->getOperand( 0 );
    Value *v2 = bop->getOperand( 1 );

    obj_res v1_obj = alloc_external( getTrivialObjectClass(), v1 );
    obj_res v2_obj = alloc_external( getTrivialObjectClass(), v2 );
    obj_res pair = alloc_cnstr( 0, 2, 0 );
    cnstr_set( pair, 0, v1_obj );
    cnstr_set( pair, 1, v2_obj );
    return set_io_result( r, mk_option_some( pair ) );
  }

  return set_io_result( r, mk_option_none() );
}

obj_res getCmpInstData( b_obj_arg i_obj, obj_arg r ) {
  Instruction *i = static_cast<Instruction*>(external_data(i_obj));
  CmpInst *ci = dyn_cast<CmpInst>(i);

  if( ci && ci->getNumOperands() == 2 ) {
    unsigned int cmpOp = static_cast<unsigned int>(ci->getPredicate());
    Value *v1 = ci->getOperand( 0 );
    Value *v2 = ci->getOperand( 1 );

    obj_res v1_obj = alloc_external( getTrivialObjectClass(), v1 );
    obj_res v2_obj = alloc_external( getTrivialObjectClass(), v2 );

    obj_res pair = alloc_cnstr( 0, 2, 0 );
    cnstr_set( pair, 0, v1_obj );
    cnstr_set( pair, 1, v2_obj );

    obj_res tuple = alloc_cnstr( 0, 2, 0 );
    cnstr_set( tuple, 0, box(cmpOp) );
    cnstr_set( tuple, 1, pair );

    return set_io_result( r, mk_option_some( tuple ) );
  }

  return set_io_result( r, mk_option_none() );
}

obj_res getBranchInstData( b_obj_arg i_obj, obj_arg r ) {
  Instruction *i = static_cast<Instruction*>(external_data(i_obj));
  BranchInst *bi = dyn_cast<BranchInst>(i);
  if( bi ) {
    if( bi->getNumSuccessors() == 1 ) {
      obj_res b_obj = alloc_external( getTrivialObjectClass(), bi->getSuccessor(0) );

      obj_res x = alloc_cnstr( 0, 1, 0 );
      cnstr_set( x, 0, b_obj );

      return set_io_result( r, mk_option_some( x ) );

    } else if (bi->getNumSuccessors() == 2 ) {
      obj_res x = alloc_cnstr( 1, 3, 0 );

      obj_res c_obj = alloc_external( getTrivialObjectClass(), bi->getCondition() );

      obj_res t_obj = alloc_external( getTrivialObjectClass(), bi->getSuccessor(0) );
      obj_res f_obj = alloc_external( getTrivialObjectClass(), bi->getSuccessor(1) );

      cnstr_set( x, 0, c_obj );
      cnstr_set( x, 1, t_obj );
      cnstr_set( x, 2, f_obj );

      return set_io_result( r, mk_option_some( x ) );
    }
  }

  return set_io_result( r, mk_option_none() );
}

obj_res getPhiData( b_obj_arg i_obj, obj_arg r ) {
  Instruction *i = static_cast<Instruction*>(external_data(i_obj));
  PHINode* phi = dyn_cast<PHINode>(i);
  if( phi ) {
    obj_res arr = alloc_array( 0, 0 );

    unsigned n = phi->getNumIncomingValues();
    for( unsigned i = 0; i<n; i++ ) {
      Value* v = phi->getIncomingValue(i);
      BasicBlock* bb = phi->getIncomingBlock(i);

      obj_res v_obj = alloc_external( getTrivialObjectClass(), v );
      obj_res bb_obj = alloc_external( getTrivialObjectClass(), bb );

      obj_res pair = alloc_cnstr( 0, 2, 0 );
      cnstr_set( pair, 0, v_obj );
      cnstr_set( pair, 1, bb_obj );

      arr = array_push( arr, pair );
    }

    return set_io_result( r, mk_option_some(arr) );
  }

  return set_io_result( r, mk_option_none() );
}

obj_res getCastInstData( b_obj_arg i_obj, obj_arg r ) {
  Instruction *i = static_cast<Instruction*>(external_data(i_obj));
  CastInst *ci = dyn_cast<CastInst>(i);
  if( ci ) {

    unsigned int opcode = static_cast<unsigned int>(ci->getOpcode());
    Value* v = ci->getOperand( 0 );

    obj_res v_obj = alloc_external( getTrivialObjectClass(), v );

    obj_res pair = alloc_cnstr( 0, 2, 0 );
    cnstr_set( pair, 0, box(opcode) );
    cnstr_set( pair, 1, v_obj );

    return set_io_result( r, mk_option_some( pair ) );
  }

  return set_io_result( r, mk_option_none() );
}


obj_res getSelectInstData( b_obj_arg i_obj, obj_arg r ) {
  Instruction *i = static_cast<Instruction*>(external_data(i_obj));
  SelectInst *si = dyn_cast<SelectInst>(i);
  if( si ) {
    Value *vc = si->getCondition();
    Value *vt = si->getTrueValue();
    Value *ve = si->getFalseValue();

    obj_res vc_obj = alloc_external( getTrivialObjectClass(), vc );
    obj_res vt_obj = alloc_external( getTrivialObjectClass(), vt );
    obj_res ve_obj = alloc_external( getTrivialObjectClass(), ve );

    obj_res pair = alloc_cnstr( 0, 2, 0 );
    cnstr_set( pair, 0, vt_obj );
    cnstr_set( pair, 1, ve_obj );

    obj_res tuple = alloc_cnstr( 0, 2, 0 );
    cnstr_set( tuple, 0, vc_obj );
    cnstr_set( tuple, 1, pair );

    return set_io_result( r, mk_option_some( tuple ) );
  }

  return set_io_result( r, mk_option_none() );
}


obj_res getConstIntData( b_obj_arg c_obj, obj_arg r ) {
  Constant* c = static_cast<Constant*>(external_data(c_obj));
  ConstantInt * cint = dyn_cast<ConstantInt>(c);
  if( cint ) {
    unsigned width = cint->getBitWidth();
    obj_res val_obj;

    if( width <= 64 ) {
      uint64_t val = cint->getValue().getZExtValue();
      if( val <= LEAN_MAX_SMALL_NAT ) {
	val_obj = box( val );
      } else {
	val_obj = mk_nat_obj_core( mpz( val ) );
      }

    } else {
      unsigned int i = cint->getValue().getNumWords();

      if( i == 0 ) {
	val_obj = box(0);

      } else if( i == 1 ) {

	// list of 64-bit limbs in little-endian order
	const uint64_t *rawvals = cint->getValue().getRawData();
	uint64_t val = rawvals[0];
	if( val <= LEAN_MAX_SMALL_NAT ) {
	  val_obj = box( val );
	} else {
	  val_obj = mk_nat_obj_core( mpz( val ) );
	}
      } else {

	// list of 64-bit limbs in little-endian order
	const uint64_t *rawvals = cint->getValue().getRawData();
	mpz *m = new mpz( rawvals[--i] );

	while( i-- > 0 ) {
	  mul2k( *m, *m, 64 );
	  *m |= mpz( rawvals[i] );
	}

	val_obj = mk_nat_obj_core(*m);
      }
    }

    obj_res pair = alloc_cnstr( 0, 2, 0 );
    cnstr_set( pair, 0, box(width) );
    cnstr_set( pair, 1, val_obj );

    return set_io_result( r, mk_option_some( pair ) );
  }

  return set_io_result( r, mk_option_none() );
}


obj_res hasNoUnsignedWrap( b_obj_arg i_obj, obj_arg r ) {
  Instruction *i = static_cast<Instruction*>(external_data(i_obj));
  bool b = i->hasNoUnsignedWrap();
  return set_io_result( r, box(b) );
}

obj_res hasNoSignedWrap( b_obj_arg i_obj, obj_arg r ) {
  Instruction *i = static_cast<Instruction*>(external_data(i_obj));
  bool b = i->hasNoSignedWrap();
  return set_io_result( r, box(b) );
}

obj_res isExact( b_obj_arg i_obj, obj_arg r ) {
  Instruction *i = static_cast<Instruction*>(external_data(i_obj));
  bool b = i->isExact();
  return set_io_result( r, box(b) );
}

obj_res getValueType( b_obj_arg v_obj, obj_arg r ) {
  Value *v = static_cast<Value*>(external_data(v_obj));
  Type* tp = v->getType();
  obj_res tp_obj = alloc_external( getTrivialObjectClass(), tp );
  return set_io_result( r, tp_obj );
}


obj_res decomposeValue( b_obj_arg v_obj, obj_arg r ) {
  Value *v = static_cast<Value*>(external_data(v_obj));
  obj_res x;
  if( Argument *a = dyn_cast<Argument>(v) ) {

    x = alloc_cnstr( 1, 0, 0 );
    cnstr_set( x, 0, box(a->getArgNo()) );

  } else if( Instruction* i = dyn_cast<Instruction>(v) ) {

    obj_res i_obj = alloc_external( getTrivialObjectClass(), i );
    x = alloc_cnstr( 2, 0, 0 );
    cnstr_set( x, 0, i_obj );

  } else if( Constant* c = dyn_cast<Constant>(v) ) {

    obj_res c_obj = alloc_external( getTrivialObjectClass(), c );
    x = alloc_cnstr( 3, 0, 0 );
    cnstr_set( x, 0, c_obj );

  } else {
    x = alloc_cnstr(0,0,0);
  }

  return set_io_result( r, x );
}



}
