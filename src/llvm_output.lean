import init.data.array
import init.data.int
import init.data.rbmap
import init.system.io

import .ast
import .pp
import .data_layout
import .llvm_ffi


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

instance mIO : monadIO output :=
  { monadLift := λa m r => m
  }

def run {a:Type} (m:output a) : IO (value_context × a) :=
  do r <- IO.mkRef value_context.init;
     a <- m r;
     vc <- r.get;
     pure (vc, a)

def alterSymbolMap (f:symMap → symMap) : output Unit :=
  λr => r.modify (λvc => { vc with symbol_map := f vc.symbol_map }).

/-
def createFunction (m:Module) (nm:symbol) : output LLVMFunction :=
  do f <- newFunction m nm.symbol;
     alterSymbolMap (λsm => sm.insert 
-/

end output.

end llvm.
