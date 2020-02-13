import Init.Data.Array
import Init.Data.Int
import Init.Data.RBMap
import Init.System.IO

import LeanLLVM.AST
import LeanLLVM.PP
import LeanLLVM.DataLayout
import LeanLLVM.LLVMCodes
import LeanLLVM.LLVMFFI

namespace llvm.
namespace output.

@[reducible]
def symMap := RBMap symbol ffi.Value (λx y => decide (x < y))

@[reducible]
def blockMap := RBMap block_label ffi.Value (λx y => decide (x.label < y.label))

@[reducible]
def valueMap := RBMap ident ffi.Value (λx y => decide (x < y))

@[reducible]
def typeMap := RBMap String ffi.Type_ (λx y => decide (x < y))

structure value_context :=
  ( symbol_map : symMap )
  ( block_map  : blockMap )
  ( value_map  : valueMap )
  ( type_map   : typeMap )

def value_context.init :=
  value_context.mk RBMap.empty RBMap.empty RBMap.empty RBMap.empty.

end output.

@[reducible]
def output (a:Type) := IO.Ref output.value_context → IO a.

namespace output.

instance monad : Monad output :=
  { bind := λa b mx mf r => mx r >>= λx => mf x r
  , pure := λa x r => pure x
  }.

instance monadExcept : MonadExcept IO.Error output :=
  { throw := λa err r => throw err
  , catch := λa m handle r => catch (m r) (λerr => handle err r)
  }.

instance mIO : MonadIO output :=
  { monadLift := λa m r => m
  }

def run {a:Type} (m:output a) : IO (value_context × a) :=
  do r <- IO.mkRef value_context.init;
     a <- m r;
     vc <- r.get;
     pure (vc, a)

def alterSymbolMap (f:symMap → symMap) : output Unit :=
  λr => r.modify (λvc => { vc with symbol_map := f vc.symbol_map }).

def lookupAlias (nm:String) : output (Option ffi.Type_) :=
  λr => do vc <- r.get;
           pure (vc.type_map.find nm)

/-
def createFunction (m:Module) (nm:symbol) : output LLVMFunction :=
  do f <- newFunction m nm.symbol;
     alterSymbolMap (λsm => sm.insert
-/

end output.

def outputFloatType (ctx:ffi.Context) : float_type → IO ffi.Type_
| float_type.half      => ffi.newPrimitiveType ctx code.type.half
| float_type.float     => ffi.newPrimitiveType ctx code.type.float
| float_type.double    => ffi.newPrimitiveType ctx code.type.double
| float_type.fp128     => ffi.newPrimitiveType ctx code.type.fp128
| float_type.x86_fp80  => ffi.newPrimitiveType ctx code.type.x86_fp80
| float_type.ppc_fp128 => ffi.newPrimitiveType ctx code.type.ppc_fp128

def outputPrimType (ctx:ffi.Context) : prim_type → IO ffi.Type_
| prim_type.label         => ffi.newPrimitiveType ctx code.type.label
| prim_type.token         => ffi.newPrimitiveType ctx code.type.token
| prim_type.void          => ffi.newPrimitiveType ctx code.type.void
| prim_type.float_type ft => outputFloatType ctx ft
| prim_type.x86mmx        => ffi.newPrimitiveType ctx code.type.x86_mmx
| prim_type.metadata      => ffi.newPrimitiveType ctx code.type.metadata
| prim_type.integer n     => ffi.newIntegerType ctx n

partial def outputType (ctx:ffi.Context) : llvm_type → output ffi.Type_
| llvm_type.prim_type pt => monadLift (outputPrimType ctx pt)
| llvm_type.alias nm     =>
      do x <- output.lookupAlias nm;
         match x with
         | some tp => pure tp
         | none => throw (IO.userError ("Unknown type alias: " ++ nm))
| llvm_type.array n t =>
    do t' <- outputType t;
       monadLift (ffi.newArrayType n t')
| llvm_type.vector n t =>
    do t' <- outputType t;
       monadLift (ffi.newVectorType n t')
| llvm_type.ptr_to t =>
    do t' <- outputType t;
       monadLift (ffi.newPointerType t')
| llvm_type.fun_ty ret args varargs =>
    do ret' <- outputType ret;
       args' <- Array.mapM outputType args;
       monadLift (ffi.newFunctionType ret' args' varargs)
| llvm_type.struct packed tps =>
    do tps' <- Array.mapM outputType tps;
       monadLift (ffi.newLiteralStructType packed tps')

def setupTypeAlias (ctx:ffi.Context) (nm:String) : output ffi.Type_ :=
  λr => do vc <- r.get;
           tp <- ffi.newOpaqueStructType ctx nm;
           let vc' := { vc with type_map := vc.type_map.insert nm tp };
           r.set vc';
           pure tp

def finalizeTypeAlias (ctx:ffi.Context) (ty:ffi.Type_) : type_decl_body → output Unit
| type_decl_body.opaque => pure ()
| type_decl_body.defn (llvm_type.struct packed tps) =>
     do tps' <- Array.mapM (outputType ctx) tps;
        monadLift (ffi.setStructTypeBody ty packed tps');
        pure ()
| type_decl_body.defn _ => throw (IO.userError "type alias defintion must be a struct body")
  

-- Process type aliases in two phases.  First, allocate named, opaque struct
-- types for each alias and record them in the value context.  Next, process
-- the bodies of type aliases and set the body of the non-opaque named struct types.
--
-- This two-phase approach ensures that recursive struct groups are properly handled.
def outputTypeAliases (ctx:ffi.Context) (tds:Array type_decl) : output Unit :=
  do fs <- Array.mapM (λ(td:type_decl) => 
              setupTypeAlias ctx td.name >>= λty => pure (finalizeTypeAlias ctx ty td.decl)) tds;
     Array.iterateM fs () (λ_ action _ => action)


def outputDeclare (ctx:ffi.Context) (m:ffi.Module) (d:declare) : output Unit :=
  do funtp <- outputType ctx (llvm_type.fun_ty d.ret_type d.args d.var_args);
     f <- monadLift (ffi.newFunction m funtp d.name.symbol);
     output.alterSymbolMap (λsm => sm.insert d.name (ffi.functionToValue f));
     pure ()

def outputDefine (ctx:ffi.Context) (m:ffi.Module) (d:define) : output Unit :=
  do let argTypes := d.args.map (λa => a.type);
     funtp <- outputType ctx (llvm_type.fun_ty d.ret_type argTypes d.var_args);
     f <- monadLift (ffi.newFunction m funtp d.name.symbol);
     output.alterSymbolMap (λsm => sm.insert d.name (ffi.functionToValue f));

  -- TODO!!!

     pure ()

def outputModule (ctx:ffi.Context) (m:module) : output ffi.Module :=
  do outputTypeAliases ctx m.types;
     let modnm := match m.source_name with
                  | some nm => nm
                  | none    => "";
     ffimod <- monadLift (ffi.newModule ctx modnm);
     Array.iterateM m.declares () (λ_ decl _ => outputDeclare ctx ffimod decl);
     Array.iterateM m.defines () (λ_ defn _ => outputDefine ctx ffimod defn);

     pure ffimod     


end llvm.
