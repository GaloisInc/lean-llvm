import Init.Data.Array
import Init.Data.Int
import Std.Data.RBMap
import Init.Data.String

import Galois.Data.Bitvec

import LeanLLVM.AST
import LeanLLVM.PP
import LeanLLVM.TypeContext
import LeanLLVM.Value

open Std (RBMap)

namespace LLVM

inductive trace_event : Type
| load   (ptr : bitvec 64) (mt:mem_type) (val:Sim.Value)
| store  (ptr : bitvec 64) (mt:mem_type) (val:Sim.Value)
| alloca (ptr : bitvec 64) (sz : Nat)

namespace trace_event

def asString : trace_event -> String
| load ptr mt val  => "LOAD   " ++ ptr.pp_hex ++ " " ++ val.pretty.render
| store ptr mt val => "STORE  " ++ ptr.pp_hex ++ " " ++ val.pretty.render
| alloca ptr sz    => "ALLOCA " ++ ptr.pp_hex ++ " " ++ toString sz

end trace_event

structure frame :=
(locals   : Sim.regMap)
(func     : Define)
(curr     : BlockLabel)
(prev     : Option BlockLabel)
(framePtr : Nat)

instance frameInh : Inhabited frame :=
⟨{ locals := Std.RBMap.empty,
   func   :=
     { linkage  := none,
       retType  := PrimType.void,
       name     := ⟨""⟩,
       args     := Array.empty,
       varArgs  := false,
       attrs    := Array.empty,
       sec      := none,
       gc       := none,
       body     := Array.empty,
       metadata := Strmap.empty,
       comdat   := none
     },
   curr     := ⟨Ident.named ""⟩,
   prev     := none,
   framePtr := 0
  }⟩

structure State :=
(mem : Sim.memMap)
(mod : Module)
(dl  : DataLayout)
(heapAllocPtr : Nat)
(stackPtr : Nat)
(symmap : RBMap Symbol (bitvec 64) Ord.compare)
(revsymmap : RBMap (bitvec 64) Symbol Ord.compare)

structure SimConts (z:Type) :=
(kerr : IO.Error → z) /- error continuation -/
(kret : Option Sim.Value → State → z) /- return continuation -/
(kcall : (Option Sim.Value → State → z) → Symbol → List Sim.Value → State → z)
         /- call continuation -/
(kjump : BlockLabel → frame → State → z) /- jump continuation -/
(ktrace : trace_event -> z -> z ) /- trace operation -/

structure Sim (a:Type) :=
(runSim : ∀{z:Type}, SimConts z → (a → frame → State → z) → (frame → State → z))

namespace Sim

instance {a:Type} : Inhabited (Sim a) :=
  ⟨ ⟨λconts k f st => conts.kerr (IO.userError "black hole")⟩ ⟩

instance monad : Monad Sim :=
  { bind := λmx mf => Sim.mk (λconts k =>
       mx.runSim conts (λx => (mf x).runSim conts k))
  , pure := λx => Sim.mk (λ_ k => k x)
  }

instance monadExcept : MonadExcept IO.Error Sim :=
  { throw := λerr => Sim.mk (λconts _k _frm _st => conts.kerr err)
  , tryCatch := λm handle => Sim.mk (λconts k frm st =>
      let conts' := { conts with kerr := λerr => (handle err).runSim conts k frm st };
      m.runSim conts' k frm st)
  }

def setFrame (frm:frame) : Sim Unit :=
  Sim.mk (λ _ k _ st => k () frm st)

def getFrame : Sim frame :=
  Sim.mk (λ _ k frm st => k frm frm st)

def modifyFrame (f: frame → frame) : Sim Unit :=
  Sim.mk (λ _ k frm st => k () (f frm) st)

def getState : Sim State :=
  Sim.mk (λ _ k frm st => k st frm st)

def setState (st:State) : Sim Unit :=
  Sim.mk (λ _ k frm _ => k () frm st)

def assignReg (reg:Ident) (v:Value) : Sim Unit :=
  modifyFrame (λfrm => { frm with locals := Std.RBMap.insert frm.locals reg v })

def trace (ev:trace_event) : Sim Unit :=
  Sim.mk (λ conts k frm st => conts.ktrace ev (k () frm st))

def lookupReg (reg:Ident) : Sim Value := do
  let frm ← getFrame
  match Std.RBMap.find? frm.locals reg with
  | none     => throw (IO.userError ("unassigned register: " ++ reg.asString))
  | some v => pure v

def returnVoid {a} : Sim a :=
  Sim.mk (λ conts _k frm st => conts.kret none { st with stackPtr := frm.framePtr })

def returnValue {a} (v:Sim.Value) : Sim a :=
  Sim.mk (λ conts _k frm st => conts.kret (some v) { st with stackPtr := frm.framePtr })

def jump {a} (l:BlockLabel) : Sim a :=
  Sim.mk (λ conts _k frm st => conts.kjump l frm st)

def call (s:Symbol) (args:List Value) : Sim (Option Value) :=
  Sim.mk (λ conts k frm st => conts.kcall (λv => k v frm) s args st)

def eval_mem_type (t:LLVMType) : Sim mem_type := do
  let st ← Sim.getState
  match lift_mem_type st.dl st.mod.types t with
  | none => throw (IO.userError ("could not lift type: " ++ (pp t).render))
  | some mt => pure mt

partial def eval : mem_type → LLVM.Value → Sim Sim.Value
| _,              Value.ident i    => Sim.lookupReg i
| mem_type.int w, Value.integer n  => pure (Value.bv (bitvec.of_int w n))
| mem_type.int w, Value.bool true  => pure (Value.bv (bitvec.of_int w 1))
| mem_type.int w, Value.bool false => pure (Value.bv (bitvec.of_int w 0))
| mem_type.int w, Value.null       => pure (Value.bv (bitvec.of_int w 0))
| mem_type.int w, Value.zeroInit   => pure (Value.bv (bitvec.of_int w 0))
| mem_type.int w, Value.undef      => pure (Value.bv (bitvec.of_int w 0)) --???
| mem_type.ptr _, Value.symbol s   => do
  let st ← Sim.getState;
  match st.symmap.find? s with
  | some ptr => pure (Value.bv ptr)
  | none => throw (IO.userError ("could not resolve symbol: " ++ s.symbol))

| mem_type.array _n eltp, LLVM.Value.array _tp vs => do
  let vs' <- vs.mapM (eval eltp)
  pure (Value.array eltp vs')

| _, v => throw (IO.userError ("bad Value/type in evaluation: " ++ (pp v).render))

def eval_typed (tv:Typed LLVM.Value) : Sim Sim.Value := do
  let mt ← eval_mem_type tv.type
  eval mt tv.value

end Sim

-- Heap allocation counts up.  Find the next aligned Value and return it,
-- advancing the heap allocation pointer x bytes beyond.
def allocOnHeap (sz:Nat) (a:Alignment) (st:State) : bitvec 64 × State :=
  let ptr := padToAlignment st.heapAllocPtr a;
  (bitvec.of_nat 64 ptr, { st with heapAllocPtr := ptr + sz })

-- Stack allocation counts down.  Find the next aligned Value that provides
-- enough space and return it, advancing the stack pointer to this point.
def allocOnStack (sz:Nat) (a:Alignment) (st:State) : bitvec 64 × State :=
  let ptr := padDownToAlignment (st.stackPtr - sz) a;
  ( bitvec.of_nat 64 ptr, { st with stackPtr := ptr })

def allocFunctionSymbol (s:Symbol) (st:State) : State :=
  let (ptr, st') := allocOnHeap 16 align16 st; -- 16 bytes with 16 byte alignment, rather arbitrarily
  { st' with symmap := st.symmap.insert s ptr,
             revsymmap := st.revsymmap.insert ptr s,
  }


def linkSymbol (st:State) (x:Symbol × bitvec 64) : State :=
  let (s,ptr) := x;
   { st with symmap := st.symmap.insert s ptr,
             revsymmap := st.revsymmap.insert ptr s
   }

def initializeState (mod : Module) (dl:DataLayout) (ls:List (Symbol × bitvec 64)) : State :=
  ls.foldl linkSymbol
    { mem := Std.RBMap.empty
    , mod := mod
    , dl  := dl
    , heapAllocPtr := 0
    , stackPtr := 2^64
    , symmap := Std.RBMap.empty
    , revsymmap := Std.RBMap.empty
    }

end LLVM
