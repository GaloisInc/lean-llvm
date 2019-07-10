import init.data.array
import init.data.int
import init.data.rbmap

import .ast
import .bv
import .pp
import .type_context

namespace llvm.

inductive runtime_value
| int (w:Nat) : bv w → runtime_value
| symbol : symbol → runtime_value
.

@[reducible]
def memMap := @RBMap (bv 64) (bv 8) (λx y => decide (x < y)).

@[reducible]
def regMap := @RBMap ident runtime_value (λx y => decide (x < y)).

structure frame :=
  (locals : regMap)
  (func   : define)
  (curr   : block_label)
  (prev   : Option block_label)

instance frameInh : Inhabited frame := Inhabited.mk
  { locals := RBMap.empty
  , func   := llvm.define.mk none (llvm_type.prim_type prim_type.void) (symbol.mk "") Array.empty false Array.empty none none Array.empty (strmap_empty _) none
  , curr   := block_label.named ""
  , prev   := none
  }.

structure state :=
  (mem : memMap)
  (mod : module).

structure sim_conts (z:Type) :=
  (kerr : IO.Error → z) /- error continuation -/
  (kret : Option runtime_value → state → z) /- return continuation -/
  (kcall : (Option runtime_value → state → z) → symbol → List runtime_value → state → z)
         /- call continuation -/
  (kjump : block_label → frame → state → z) /- jump continuation -/
.

structure sim (a:Type) :=
  (runSim :
     ∀{z:Type},
     (sim_conts z)           /- nonlocal continuations -/ →
     (a → frame → state → z) /- normal continuation -/ →
     (frame → state → z)).

namespace sim.

instance functor : Functor sim :=
  { map := λa b f (m:sim a) => sim.mk (λz conts k =>
      m.runSim conts (λx => k (f x)))

  , mapConst := λa b x (m:sim b) => sim.mk (λz conts k =>
      m.runSim conts (λ_ => k x))
  }.

instance hasPure : HasPure sim :=
  { pure := λa x => sim.mk (λz _ k => k x) }.

instance hasSeq : HasSeq sim :=
  { seq := λa b mf mx => sim.mk (λz conts k =>
          mf.runSim conts (λf =>
          mx.runSim conts (λx =>
          k (f x))))
  }.

instance hasSeqLeft : HasSeqLeft sim :=
  { seqLeft := λa b mx my => sim.mk (λz conts k =>
       mx.runSim conts (λx =>
       my.runSim conts (λ_ =>
       k x)))
  }.

instance hasSeqRight : HasSeqRight sim :=
  { seqRight := λa b mx my => sim.mk (λz conts k =>
       mx.runSim conts (λ_ =>
       my.runSim conts (λy =>
       k y)))
  }.

instance hasBind : HasBind sim :=
  { bind := λa b mx mf => sim.mk (λz conts k =>
       mx.runSim conts (λx => (mf x).runSim conts k))
  }.

instance applicative : Applicative sim := Applicative.mk _.
instance monad : Monad sim := Monad.mk _.

instance monadExcept : MonadExcept IO.Error sim :=
  { throw := λa err => sim.mk (λz conts _k _frm _st => conts.kerr err)
  , catch := λa m handle => sim.mk (λz conts k frm st =>
      let conts' := { conts with kerr := λerr => (handle err).runSim conts k frm st }
      in m.runSim conts' k frm st)
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

def assignReg (reg:ident) (v:runtime_value) : sim Unit :=
  modifyFrame (λfrm => { frm with locals := RBMap.insert frm.locals reg v }).

def lookupReg (reg:ident) : sim runtime_value :=
  do frm <- getFrame;
     match RBMap.find frm.locals reg with
     | none     => throw (IO.userError ("unassigned register: " ++ reg.asString))
     | (some v) => pure v

def returnVoid {a} : sim a :=
  sim.mk (λz conts _k _frm st => conts.kret none st).

def returnValue {a} (v:runtime_value) : sim a :=
  sim.mk (λz conts _k _frm st => conts.kret (some v) st).

def jump {a} (l:block_label) : sim a :=
  sim.mk (λz conts _k frm st => conts.kjump l frm st).

def call (s:symbol) (args:List runtime_value) : sim (Option runtime_value) :=
  sim.mk (λz conts k frm st => conts.kcall (λv => k v frm) s args st).

end sim.

def unreachable {a} : sim a := throw (IO.userError "unreachable code!").

def eval_mem_type (t:llvm_type) : sim mem_type :=
  do st <- sim.getState;
     (match lift_mem_type st.mod.types t with
      | none => throw (IO.userError "could not lift type")
      | (some mt) => pure mt)


def eval : mem_type → value → sim runtime_value
| _                (value.ident i)    := sim.lookupReg i
| (mem_type.int w) (value.integer n)  := pure (runtime_value.int w (bv.from_int w n))
| (mem_type.int w) (value.bool true)  := pure (runtime_value.int w (bv.from_int w 1))
| (mem_type.int w) (value.bool false) := pure (runtime_value.int w (bv.from_int w 0))
| (mem_type.int w) (value.null)       := pure (runtime_value.int w (bv.from_int w 0))
| (mem_type.int w) (value.zero_init)  := pure (runtime_value.int w (bv.from_int w 0))
| (mem_type.int w) (value.undef)      := pure (runtime_value.int w (bv.from_int w 0)) --???

| _ _ := throw (IO.userError "bad value/type in evaluation")

def eval_typed (tv:typed value) : sim runtime_value :=
  do mt <- eval_mem_type tv.type;
     eval mt tv.value.

def int_op (f:∀w, bv w -> bv w -> sim runtime_value) : runtime_value -> runtime_value -> sim runtime_value
| (runtime_value.int wx vx) (runtime_value.int wy vy) :=
    (match decEq wy wx with
    | Decidable.isTrue p  => f wx vx (Eq.rec vy p)
    | Decidable.isFalse _ => throw (IO.userError "expected same-width integer values")
    )
| _ _ := throw (IO.userError "expected integer arguments to int_op")
.

-- TODO, implement overflow checks
def eval_arith (op:arith_op) (x:runtime_value) (y:runtime_value) : sim runtime_value :=
  match op with
  | (arith_op.add uof sof) => int_op (λ w a b => pure (runtime_value.int w (@bv.add w a b))) x y
  | (arith_op.sub uof sof) => int_op (λ w a b => pure (runtime_value.int w (@bv.sub w a b))) x y
  | (arith_op.mul uof sof) => int_op (λ w a b => pure (runtime_value.int w (@bv.mul w a b))) x y
  | _ => throw (IO.userError "NYE: unimplemented arithmetic operation").

def asPred : runtime_value → sim Bool
| (runtime_value.int _ v) := if v.to_nat = 0 then pure false else pure true
| _ := throw (IO.userError "expected integer value as predicate")

def eval_icmp (op:icmp_op) : runtime_value → runtime_value → sim runtime_value :=
  int_op (λw a b =>
    let t := (pure (runtime_value.int 1 (bv.from_nat 1 1)) : sim runtime_value) in
    let f := (pure (runtime_value.int 1 (bv.from_nat 1 0)) : sim runtime_value) in
    match op with
    | icmp_op.ieq  => if a.to_nat =  b.to_nat then t else f
    | icmp_op.ine  => if a.to_nat != b.to_nat then t else f

    | icmp_op.iule => if a.to_nat <= b.to_nat then t else f
    | icmp_op.iult => if a.to_nat <  b.to_nat then t else f
    | icmp_op.iuge => if a.to_nat >= b.to_nat then t else f
    | icmp_op.iugt => if a.to_nat >  b.to_nat then t else f

    | icmp_op.isle => if a.to_int <= b.to_int then t else f
    | icmp_op.islt => if a.to_int <  b.to_int then t else f
    | icmp_op.isge => if a.to_int >= b.to_int then t else f
    | icmp_op.isgt => if a.to_int >  b.to_int then t else f
  ).


def eval_bit (op:bit_op) : runtime_value → runtime_value → sim runtime_value :=
  int_op (λw a b =>
    match op with
    | bit_op.and  => pure (runtime_value.int w (@bv.bitwise_and w a b))
    | bit_op.or   => pure (runtime_value.int w (@bv.bitwise_or w a b))
    | bit_op.xor  => pure (runtime_value.int w (@bv.bitwise_xor w a b))
    | (bit_op.shl uov sov) => pure (runtime_value.int w (@bv.shl w a b))
    | (bit_op.lshr exact)  => pure (runtime_value.int w (@bv.lshr w a b))
    | (bit_op.ashr exact)  => pure (runtime_value.int w (@bv.ashr w a b))
  ).

def eval_conv : conv_op → mem_type → runtime_value → mem_type → sim runtime_value
| conv_op.trunc (mem_type.int w1) (runtime_value.int wx x) (mem_type.int w2) :=
    if w1 = wx ∧ w1 >= w2 then
      pure (runtime_value.int w2 (bv.from_nat w2 x.to_nat))
    else
      throw (IO.userError "invalid trunc operation")
| conv_op.trunc _ _ _ := throw (IO.userError "invalid trunc operation")

| conv_op.zext (mem_type.int w1) (runtime_value.int wx x) (mem_type.int w2) :=
    if w1 = wx ∧ w1 <= w2 then
      pure (runtime_value.int w2 (bv.from_nat w2 x.to_nat))
    else
      throw (IO.userError "invalid zext operation")
| conv_op.zext _ _ _ := throw (IO.userError "invalid zext operation")

| conv_op.sext (mem_type.int w1) (runtime_value.int wx x) (mem_type.int w2) :=
    if w1 = wx ∧ w1 <= w2 then
      pure (runtime_value.int w2 (bv.from_int w2 x.to_int))
    else
      throw (IO.userError "invalid sext operation")
| conv_op.sext _ _ _ := throw (IO.userError "invalid sext operation")

| _ _ _ _ := throw (IO.userError "NYI: conversion op")


def phi (t:mem_type) (prv:block_label) : List (value × block_label) → sim runtime_value
| [] := throw (IO.userError "phi node not defined for predecessor node")
| ((v,l)::xs) := if prv = l then eval t v else phi xs
.

def evalInstr : instruction → sim (Option runtime_value)
| (instruction.ret_void) := sim.returnVoid
| (instruction.ret v)    := eval_typed v >>= sim.returnValue

| (instruction.phi tp xs) :=
     do frm <- sim.getFrame;
        t  <- eval_mem_type tp;
        match frm.prev with
        | none => throw (IO.userError "phi nodes not allowed in entry block")
        | (some prv) => some <$> phi t prv xs.toList

| (instruction.arith op x y) :=
     do t  <- eval_mem_type x.type;
        xv <- eval t x.value;
        yv <- eval t y;
        some <$> eval_arith op xv yv

| (instruction.bit op x y) :=
     do t  <- eval_mem_type x.type;
        xv <- eval t x.value;
        yv <- eval t y;
        some <$> eval_bit op xv yv

| (instruction.conv op x outty) :=
     do t  <- eval_mem_type x.type;
        xv <- eval t x.value;
        t' <- eval_mem_type outty;
        some <$> eval_conv op t xv t'

| (instruction.icmp op x y) :=
     do t  <- eval_mem_type x.type;
        xv <- eval t x.value;
        yv <- eval t y;
        some <$> eval_icmp op xv yv

| (instruction.select c x y) :=
     do cv <- eval_typed c >>= asPred;
        t  <- eval_mem_type x.type;
        xv <- eval t x.value;
        yv <- eval t y;
        if cv then pure (some xv) else pure (some yv)

| (instruction.call _tail tp fn args) :=
     do t <- eval_mem_type tp;
        fnv <- eval t fn;
        match fnv with
        | runtime_value.symbol s => List.mmap eval_typed args >>= sim.call s
        | _ => throw (IO.userError "expected symbol value")

| (instruction.jump l) := sim.jump l

| (instruction.br c lt lf) :=
     do cv <- eval_typed c >>= asPred;
        if cv then sim.jump lt else sim.jump lf

| (instruction.unreachable) := unreachable

| _ := throw (IO.userError "NYE: unimplemented instruction")
.

def evalStmt (s:stmt) : sim Unit :=
  do res <- evalInstr s.instr;
     match (s.assign, res) with
     | (none, _)        => pure ()
     | (some i, some v) => sim.assignReg i v
     | (some _, none)   => throw (IO.userError "expected instruction to compute a value").

partial def evalStmts (stmts:Array stmt) : sim Unit := pure () -- FIXME
--  @Array.mfoldl Unit stmt sim (λ_ s => evalStmt s) Unit.unit stmts

def findBlock (l:block_label) (func:define) : sim (Array stmt) :=
  match Array.find func.body (λbb =>
    match block_label.decideEq bb.label l with
    | Decidable.isTrue _ => some bb.stmts
    | Decidable.isFalse _ => none) with
  | none => throw (IO.userError ("Could not find block: " ++ pp.render (pp_label l)))
  | some d => pure d.

def findFunc (s:symbol) (mod:module) : sim define :=
  match Array.find mod.defines (λd =>
    match decEq d.name.symbol s.symbol with
    | Decidable.isTrue _ => some d
    | Decidable.isFalse _ => none) with
  | none => throw (IO.userError ("Could not find function: " ++ s.symbol))
  | some d => pure d.

partial def execBlock {z}
    (_zinh:z)
    (kerr: IO.Error → z)
    (kret: Option runtime_value → state → z)
    (kcall: (Option runtime_value → state → z) → symbol → List runtime_value → state → z)
    : block_label → frame → state → z

| next frm st :=
   (findBlock next frm.func >>= evalStmts).runSim
      { kerr  := kerr
      , kret  := kret
      , kcall := kcall
      , kjump := execBlock
      }
      (λ_ _ _ => kerr (IO.userError ("expected block terminatror at the end of block: "
                                    ++ pp.render (pp_label next))))
      { frm with curr := next, prev := some frm.curr }
      st.

def assignArgs : List (typed ident) → List runtime_value → regMap → sim regMap
| [] [] regs := pure regs
| (f::fs) (a::as) regs := assignArgs fs as (RBMap.insert regs f.value a)
| _ _ _ := throw (IO.userError ("Acutal/formal argument mismatch")).

def entryLabel (d:define) : sim block_label :=
  match Array.getOpt d.body 0 with
  | (some bb) => pure bb.label
  | none      => throw (IO.userError "definition does not have entry block!").

partial def execFunc {z} (zinh:z) (kerr:IO.Error → z)
  : (Option runtime_value → state → z) → symbol → List runtime_value → state → z

| kret s args st :=
   (do func   <- findFunc s st.mod;
       locals <- assignArgs func.args.toList args RBMap.empty;
       lab    <- entryLabel func;
       sim.setFrame (frame.mk locals func lab none);
       findBlock lab func >>= evalStmts
   ).runSim
      { kerr  := kerr
      , kret  := kret
      , kcall := execFunc
      , kjump := execBlock zinh kerr kret execFunc
      }
      (λ_ _ _ => kerr (IO.userError "unreachable code!"))
      (default _)
      st.

def runFunc : symbol → List runtime_value → state → IO.Error ⊕ (Option runtime_value × state) :=
  execFunc (Sum.inl (IO.userError "bottom")) Sum.inl (λov st => Sum.inr (ov,st)).

end llvm.
