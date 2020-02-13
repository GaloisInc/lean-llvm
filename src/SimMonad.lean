import Init.Data.Array
import Init.Data.Int
import Init.Data.RBMap
import Init.Data.String

import LeanLLVM.AST
import LeanLLVM.BV
import LeanLLVM.PP
import LeanLLVM.TypeContext
import LeanLLVM.Value

namespace llvm.

inductive trace_event : Type
| load   (ptr : bv 64) (mt:mem_type) (val:sim.value) : trace_event
| store  (ptr : bv 64) (mt:mem_type) (val:sim.value) : trace_event
| alloca (ptr : bv 64) (sz : bytes) : trace_event

namespace trace_event.

def asString : trace_event -> String
| load ptr mt val  => "LOAD   " ++ ptr.asString ++ " " ++ pp.render val.pretty
| store ptr mt val => "STORE  " ++ ptr.asString ++ " " ++ pp.render val.pretty
| alloca ptr sz    => "ALLOCA " ++ ptr.asString ++ " " ++ sz.asString

end trace_event.



structure frame :=
  (locals   : sim.regMap)
  (func     : define)
  (curr     : block_label)
  (prev     : Option block_label)
  (framePtr : bytes).

instance frameInh : Inhabited frame := Inhabited.mk
  { locals := RBMap.empty
  , func   := llvm.define.mk none (llvm_type.prim_type prim_type.void) (symbol.mk "") Array.empty false Array.empty none none Array.empty (strmap_empty _) none
  , curr   := block_label.mk (ident.named "")
  , prev   := none
  , framePtr := bytes.mk 0
  }.

structure state :=
  (mem : sim.memMap)
  (mod : module)
  (dl  : data_layout)
  (heapAllocPtr : bytes)
  (stackPtr : bytes)
  (symmap : @RBMap symbol (bv 64) (λx y => decide (x < y)))
  (revsymmap : @RBMap (bv 64) symbol (λx y => decide (x < y)))
.

structure sim_conts (z:Type) :=
  (kerr : IO.Error → z) /- error continuation -/
  (kret : Option sim.value → state → z) /- return continuation -/
  (kcall : (Option sim.value → state → z) → symbol → List sim.value → state → z)
         /- call continuation -/
  (kjump : block_label → frame → state → z) /- jump continuation -/
  (ktrace : trace_event -> z -> z ) /- trace operation -/
.

structure sim (a:Type) :=
  (runSim :
     ∀{z:Type},
     (sim_conts z)           /- nonlocal continuations -/ →
     (a → frame → state → z) /- normal continuation -/ →
     (frame → state → z)).

namespace sim

instance simInh {a:Type} : Inhabited (sim a) :=
  ⟨ sim.mk (λz conts k f st => conts.kerr (IO.userError "black hole")) ⟩

instance monad : Monad sim :=
  { bind := λa b mx mf => sim.mk (λz conts k =>
       mx.runSim conts (λx => (mf x).runSim conts k))
  , pure := λa x => sim.mk (λz _ k => k x)
  }

instance monadExcept : MonadExcept IO.Error sim :=
  { throw := λa err => sim.mk (λz conts _k _frm _st => conts.kerr err)
  , catch := λa m handle => sim.mk (λz conts k frm st =>
      let conts' := { conts with kerr := λerr => (handle err).runSim conts k frm st };
      m.runSim conts' k frm st)
  }.

def setFrame (frm:frame) : sim Unit :=
  sim.mk (λz _ k _ st => k () frm st).

def getFrame : sim frame :=
  sim.mk (λz _ k frm st => k frm frm st).

def modifyFrame (f: frame → frame) : sim Unit :=
  sim.mk (λz _ k frm st => k () (f frm) st).

def getState : sim state :=
  sim.mk (λz _ k frm st => k st frm st).

def setState (st:state) : sim Unit :=
  sim.mk (λz _ k frm _ => k () frm st).

def assignReg (reg:ident) (v:value) : sim Unit :=
  modifyFrame (λfrm => { frm with locals := RBMap.insert frm.locals reg v }).

def trace (ev:trace_event) : sim Unit :=
  sim.mk (λz conts k frm st => conts.ktrace ev (k () frm st))

def lookupReg (reg:ident) : sim value :=
  do frm <- getFrame;
     match RBMap.find frm.locals reg with
     | none     => throw (IO.userError ("unassigned register: " ++ reg.asString))
     | (some v) => pure v

def returnVoid {a} : sim a :=
  sim.mk (λz conts _k frm st => conts.kret none { st with stackPtr := frm.framePtr }).

def returnValue {a} (v:sim.value) : sim a :=
  sim.mk (λz conts _k frm st => conts.kret (some v) { st with stackPtr := frm.framePtr }).

def jump {a} (l:block_label) : sim a :=
  sim.mk (λz conts _k frm st => conts.kjump l frm st).

def call (s:symbol) (args:List value) : sim (Option value) :=
  sim.mk (λz conts k frm st => conts.kcall (λv => k v frm) s args st).

def eval_mem_type (t:llvm_type) : sim mem_type :=
  do st <- sim.getState;
     (match lift_mem_type st.dl st.mod.types t with
      | none => throw (IO.userError ("could not lift type: " ++ pp.render (pp_type t)))
      | (some mt) => pure mt)

partial def eval : mem_type → llvm.value → sim sim.value
| _,              value.ident i    => sim.lookupReg i
| mem_type.int w, value.integer n  => pure (value.bv w (bv.from_int w n))
| mem_type.int w, value.bool true  => pure (value.bv w (bv.from_int w 1))
| mem_type.int w, value.bool false => pure (value.bv w (bv.from_int w 0))
| mem_type.int w, value.null       => pure (value.bv w (bv.from_int w 0))
| mem_type.int w, value.zero_init  => pure (value.bv w (bv.from_int w 0))
| mem_type.int w, value.undef      => pure (value.bv w (bv.from_int w 0)) --???
| mem_type.ptr _, value.symbol s  =>
   do st <- sim.getState;
      match st.symmap.find s with
      | (some ptr) => pure (value.bv 64 ptr)
      | none => throw (IO.userError ("could not resolve symbol: " ++ s.symbol))

| mem_type.array _n eltp, llvm.value.array _tp vs =>
   do vs' <- vs.mapM (eval eltp);
      pure (llvm.sim.value.array eltp vs')

| _, v => throw (IO.userError ("bad value/type in evaluation: " ++ pp.render (pp_value v)))


def eval_typed (tv:typed llvm.value) : sim sim.value :=
  do mt <- eval_mem_type tv.type;
     eval mt tv.value.

end sim.

-- Heap allocation counts up.  Find the next aligned value and return it,
-- advancing the heap allocation pointer x bytes beyond.
def allocOnHeap (x:bytes) (a:alignment) (st:state) : Prod (bv 64) state :=
  let ptr  := padToAlignment st.heapAllocPtr a;
  let ptr' := ptr.add x;
  ( bv.from_nat 64 ptr.val, { st with heapAllocPtr := ptr' } )

-- Stack allocation counts down.  Find the next aligned value that provides
-- enough space and return it, advancing the stack pointer to this point.
def allocOnStack (x:bytes) (a:alignment) (st:state) : Prod (bv 64) state :=
  let ptr := padDownToAlignment (st.stackPtr.sub x) a;
  ( bv.from_nat 64 ptr.val, { st with stackPtr := ptr })

def allocFunctionSymbol (s:symbol) (st:state) : state :=
  let (ptr, st') := allocOnHeap (bytes.mk 16) (alignment.mk 4) st; -- 16 bytes with 16 byte alignment, rather arbitrarily
  { st' with
    symmap := st.symmap.insert s ptr,
    revsymmap := st.revsymmap.insert ptr s
  }.


def linkSymbol (st:state) (x:symbol × bv 64) : state :=
  let (s,ptr) := x;
   { st with
       symmap := st.symmap.insert s ptr,
       revsymmap := st.revsymmap.insert ptr s
   }

def initializeState (mod : module) (dl:data_layout) (ls:List (symbol × bv 64)) : state :=
       ls.foldl linkSymbol
         { mem := RBMap.empty
         , mod := mod
         , dl  := dl
         , heapAllocPtr := bytes.mk 0
         , stackPtr := bytes.mk (2^64)
         , symmap := RBMap.empty
         , revsymmap := RBMap.empty
         }


end llvm.
