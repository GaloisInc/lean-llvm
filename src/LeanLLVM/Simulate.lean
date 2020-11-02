import Galois.Data.Bitvec

import LeanLLVM.AST
import LeanLLVM.Memory
import LeanLLVM.PP
import LeanLLVM.SimMonad
import LeanLLVM.TypeContext
import LeanLLVM.Value

namespace LLVM
namespace Sim

def unreachable {a} : Sim a := throw (IO.userError "unreachable code!")

def int_op (f:∀w, bitvec w -> bitvec w -> Sim Sim.Value) : Sim.Value -> Sim.Value -> Sim Sim.Value
| @Value.bv w v, @Value.bv w' v' =>
  if h : w' = w
  then
    let v'' : bitvec w := cast (congrArg bitvec h) v'
    f _ v v''
  else
    throw $ IO.userError "expected same-width integer values"
| _, _ => throw (IO.userError "expected integer arguments to int_op")

-- TODO, implement overflow checks
def eval_arith (op:ArithOp) (x:Sim.Value) (y:Sim.Value) : Sim Sim.Value :=
  match op with
  | ArithOp.add uof sof => int_op (λ w a b => pure (Value.bv (@bitvec.add w a b))) x y
  | ArithOp.sub uof sof => int_op (λ w a b => pure (Value.bv (@bitvec.sub w a b))) x y
  | ArithOp.mul uof sof => int_op (λ w a b => pure (Value.bv (@bitvec.mul w a b))) x y
  | _ => throw (IO.userError "NYE: unimplemented arithmetic operation")

def asPred : Sim.Value → Sim Bool
| Value.bv v => if v.to_nat = 0 then pure false else pure true
| _ => throw (IO.userError "expected integer value as predicate")

def eval_icmp (op:ICmpOp) : Sim.Value → Sim.Value → Sim Sim.Value :=
  int_op (λw a b =>
    let t := (pure (Value.bv (bitvec.of_nat 1 1)) : Sim Sim.Value);
    let f := (pure (Value.bv (bitvec.of_nat 1 0)) : Sim Sim.Value);
    match op with
    | ICmpOp.ieq  => if a.to_nat =  b.to_nat then t else f
    | ICmpOp.ine  => if a.to_nat != b.to_nat then t else f

    | ICmpOp.iule => if a.to_nat <= b.to_nat then t else f
    | ICmpOp.iult => if a.to_nat <  b.to_nat then t else f
    | ICmpOp.iuge => if a.to_nat >= b.to_nat then t else f
    | ICmpOp.iugt => if a.to_nat >  b.to_nat then t else f

    | ICmpOp.isle => if a.to_int <= b.to_int then t else f
    | ICmpOp.islt => if a.to_int <  b.to_int then t else f
    | ICmpOp.isge => if a.to_int >= b.to_int then t else f
    | ICmpOp.isgt => if a.to_int >  b.to_int then t else f
  )

def eval_bit (op:BitOp) : Sim.Value → Sim.Value → Sim Sim.Value :=
  int_op (λw a b =>
    match op with
    | BitOp.and  => pure (Value.bv (bitvec.and a b))
    | BitOp.or   => pure (Value.bv (bitvec.or  a b))
    | BitOp.xor  => pure (Value.bv (bitvec.xor a b))
    | BitOp.shl uov sov => pure (Value.bv (@bitvec.shl w a b.to_nat))
    | BitOp.lshr exact  => pure (Value.bv (@bitvec.ushr w a b.to_nat))
    | BitOp.ashr exact  => pure (Value.bv (@bitvec.sshr w a b.to_nat))
  )

def eval_conv : ConvOp → mem_type → Sim.Value → mem_type → Sim Sim.Value
| ConvOp.trunc, mem_type.int w1, @Value.bv wx x, mem_type.int w2 =>
    if w1 = wx ∧ w1 >= w2 then
      pure (Value.bv (bitvec.of_nat w2 x.to_nat))
    else
      throw (IO.userError "invalid trunc operation")
| ConvOp.trunc, _, _, _ => throw (IO.userError "invalid trunc operation")


| ConvOp.zext, mem_type.int w1, @Value.bv wx x, mem_type.int w2 =>
    if w1 = wx ∧ w1 <= w2 then
      pure (Value.bv (bitvec.of_nat w2 x.to_nat))
    else
      throw (IO.userError "invalid zext operation")
| ConvOp.zext, _, _, _ => throw (IO.userError "invalid zext operation")


| ConvOp.sext, mem_type.int w1, @Value.bv wx x, mem_type.int w2 =>
    if w1 = wx ∧ w1 <= w2 then
      pure (Value.bv (bitvec.of_int w2 x.to_int))
    else
      throw (IO.userError "invalid sext operation")
| ConvOp.sext, _, _, _ => throw (IO.userError "invalid sext operation")

| ConvOp.ptr_to_int, _, v, _ => pure v -- TODO, more checking
| ConvOp.int_to_ptr, _, v, _ => pure v -- TODO, more checking
| ConvOp.bit_cast, _, v, _ => pure v -- TODO, more checking!

| _, _, _, _ => throw (IO.userError "NYI: conversion op")


def phi (t:mem_type) (prv:BlockLabel) : List (LLVM.Value × BlockLabel) → Sim Sim.Value
| [] => throw (IO.userError "phi node not defined for predecessor node")
| (v,l)::xs => if prv = l then eval t v else phi t prv xs


def computeGEP {w} (dl:DataLayout) : bitvec w → List Sim.Value → mem_type → Sim (bitvec w)
| base, [], _ => pure base
| base, @Value.bv w' v :: offsets, ty =>
    match ty with
    | mem_type.array _n ty' =>
         if w = w' then
           let (sz,a) := mem_type.szAndAlign dl ty'
           let sz' := padToAlignment sz a;
           let idx := bitvec.of_int w (v.to_int * (Int.ofNat sz'))
           computeGEP dl (bitvec.add base idx) offsets ty'
         else
           throw (IO.userError "invalid array index value in GEP")

    | mem_type.struct si =>
         match si.fields.get? v.to_nat with
         | (some fi) => computeGEP dl (bitvec.add base (bitvec.of_nat w fi.offset)) offsets fi.value
         | none => throw (IO.userError "invalid struct index value in GEP")

    | _ => throw (IO.userError "Invalid GEP")

| _, _::_, _ => throw (IO.userError "invalid index value in GEP")


def evalInstr : Instruction → Sim (Option Sim.Value)
| Instruction.retVoid => Sim.returnVoid
| Instruction.ret v    => eval_typed v >>= Sim.returnValue
| Instruction.phi tp xs => do
  let frm ← Sim.getFrame
  let t  ← eval_mem_type tp
  match frm.prev with
  | none => throw (IO.userError "phi nodes not allowed in entry block")
  | some prv => some <$> phi t prv xs.toList

| Instruction.arith op x y => do
  let t  ← eval_mem_type x.type
  let xv ← eval t x.value
  let yv ← eval t y
  some <$> eval_arith op xv yv

| Instruction.bit op x y => do
  let t  ← eval_mem_type x.type
  let xv ← eval t x.value
  let yv ← eval t y
  some <$> eval_bit op xv yv

| Instruction.conv op x outty => do
  let t  ← eval_mem_type x.type
  let xv ← eval t x.value
  let t' ← eval_mem_type outty
  some <$> eval_conv op t xv t'

| Instruction.icmp op x y => do
  let t  ← eval_mem_type x.type;
  let xv ← eval t x.value;
  let yv ← eval t y;
  some <$> eval_icmp op xv yv

| Instruction.select c x y => do
  let cv ← eval_typed c >>= asPred
  let t  ← eval_mem_type x.type
  let xv ← eval t x.value
  let yv ← eval t y
  if cv then pure (some xv) else pure (some yv)

| Instruction.call _tail _rettp fn args => do
  let fnv ← eval (mem_type.ptr sym_type.void) fn -- TODO? more accurate type?
  let st ← Sim.getState;
  match fnv with
  | @Value.bv 64 bv =>
    match st.revsymmap.find? bv with
    | some s => List.mapM eval_typed args.toList >>= Sim.call s
    | none => throw (IO.userError "expected function pointer value in call")
  | _ => throw (IO.userError "expected pointer value in call")

| Instruction.jump l => Sim.jump l

| Instruction.br c lt lf => do
  let cv ← eval_typed c >>= asPred;
  if cv then Sim.jump lt else Sim.jump lf

| Instruction.unreachable => unreachable

| Instruction.load ptr _atomicordering _oalign => do
  let st ← Sim.getState
  let dl := st.dl
  let tds := st.mod.types
  let mt ← eval_mem_type ptr.type
  let pv ←  eval mt ptr.value
  match mt, pv with
  | mem_type.ptr st, @Value.bv 64 p =>
      match sym_type_to_mem_type dl tds st with
      | some loadtp => do
        let v ← Mem.load dl loadtp p;
        Sim.trace (trace_event.load p loadtp v);
        pure (some v)
      | none => throw $ IO.userError "expected loadable pointer type in load"
  | _, _ => throw (IO.userError "expected pointer value in load" )

| Instruction.store val ptr _align => do
   let st ← Sim.getState
   let pv ← eval_typed ptr
   match pv with
   | @Value.bv 64 p => do
     let mt ← eval_mem_type val.type;
     let v ← eval mt val.value;
     Mem.store st.dl mt p v;
     Sim.trace (trace_event.store p mt v);
     pure none
   | _ => throw (IO.userError "expected pointer value in store" )

| Instruction.alloca tp onum oalign => do
    let mt ← eval_mem_type tp;
    let dl ← State.dl <$> Sim.getState;
    let sz ← match onum with
             | none => pure (mt.sz dl)
             | some num => do
               let n ← eval_typed num
               match n with
               | Value.bv n' => pure $ (mt.sz dl).mul n'.to_nat
               | _ => throw $ IO.userError "expected integer value in alloca instruction"
     let a ← match oalign with
             | none => pure (mt.alignment dl)
             | some align =>
               match toAlignment align with
               | none => throw (IO.userError ("illegal alignment value in alloca: " ++ toString align))
               | some a => pure (maxAlignment (mt.alignment dl) a);
     let ptr ← do 
       let st ←  Sim.getState
       let (p,st') := allocOnStack sz a st
       Sim.setState st'
       pure p
     Sim.trace (trace_event.alloca ptr sz);
     pure (some (Value.bv ptr))


| Instruction.gep _bounds base offsets => do
  let dl ← State.dl <$> Sim.getState
  let tds ← (Module.types ∘ State.mod) <$> Sim.getState
  let baseType ← eval_mem_type base.type
  match baseType with
  | mem_type.ptr stp =>
    match sym_type_to_mem_type dl tds stp with
    | some mt => do
      let base' ← eval baseType base.value
      let offsets' ← Array.mapM eval_typed offsets
      match base' with
      | Value.bv baseptr =>
        (some ∘ Value.bv) <$> computeGEP dl baseptr offsets'.toList (mem_type.array 0 mt)
      | _ => throw $ IO.userError "Expected bitvector in GEP base value"
    | none => throw $ IO.userError "Invalid GEP, bad base type"
  | _ => throw $ IO.userError "Expected pointer type in GEP base"


| _ => throw $ IO.userError "NYE: unimplemented instruction"

def evalStmt (s:Stmt) : Sim Unit := do
  let res ← evalInstr s.instr
  match (s.assign, res) with
  | (none, _)        => pure ()
  | (some i, some v) => Sim.assignReg i v
  | (some _, none)   => throw $ IO.userError "expected instruction to compute a value"

def evalStmts (stmts:Array Stmt) : Sim Unit := do
  for s in stmts do
    evalStmt s

def findBlock (l:BlockLabel) (func:Define) : Sim (Array Stmt) :=
  match Array.find? func.body (λbb =>
    match BlockLabel.decideEq bb.label l with
    | Decidable.isTrue _ => true
    | Decidable.isFalse _ => false) with
  | none => throw (IO.userError ("Could not find block: " ++ (pp l).render))
  | some d => pure d.stmts

def findFunc (s:Symbol) (mod:Module) : Sim Define :=
  match Array.find? mod.defines (λd =>
    match decEq d.name.symbol s.symbol with
    | Decidable.isTrue _ => true
    | Decidable.isFalse _ => false) with
  | none => throw (IO.userError ("Could not find function: " ++ s.symbol))
  | some d => pure d

partial def execBlock {z}
    (_zinh:z)
    (kerr: IO.Error → z)
    (kret: Option Sim.Value → State → z)
    (kcall: (Option Sim.Value → State → z) → Symbol → List Sim.Value → State → z)
    (ktrace : trace_event → z → z)
    : BlockLabel → frame → State → z

| next, frm, st =>
   (findBlock next frm.func >>= evalStmts).runSim
      { kerr  := kerr
      , kret  := kret
      , kcall := kcall
      , kjump := execBlock _zinh kerr kret kcall ktrace
      , ktrace := ktrace
      }
      (λ _ _ _ => kerr $ IO.userError ("expected block terminatror at the end of block: "
                                    ++ (pp next).render))
      { frm with curr := next, prev := some frm.curr }
      st

def assignArgs : List (Typed Ident) → List Sim.Value → regMap → Sim regMap
| [], [], regs => pure regs
| f::fs, a::as, regs => assignArgs fs as (Std.RBMap.insert regs f.value a)
| _, _, _ => throw (IO.userError ("Acutal/formal argument mismatch"))

def entryLabel (d:Define) : Sim BlockLabel :=
  match Array.get? d.body 0 with
  | some bb => pure bb.label
  | none    => throw $ IO.userError ("definition does not have entry block! " ++ d.name.symbol)

partial def execFunc {z} (zinh:z) (kerr:IO.Error → z) (ktrace : trace_event → z → z)
  : (Option Sim.Value → State → z) → Symbol → List Sim.Value → State → z

| kret, s, args, st =>
  let kcall := execFunc zinh kerr ktrace
  let simulation : Sim Unit := do
    let func   ← findFunc s st.mod
    let locals ← assignArgs func.args.toList args Std.RBMap.empty
    let lab    ← entryLabel func
    Sim.setFrame (frame.mk locals func lab none st.stackPtr)
    findBlock lab func >>= evalStmts
  simulation.runSim
    { kerr  := kerr
    , kret  := kret
    , kcall := kcall
    , kjump := execBlock zinh kerr kret kcall ktrace
    , ktrace := ktrace
    }
    (λ_ _ _ => kerr (IO.userError "unterminated basic block!"))
    (arbitrary _)
    st

def runFunc : Symbol → List Sim.Value → State → Sum IO.Error (Option Sim.Value × State) :=
  execFunc (Sum.inl (IO.userError "bottom")) Sum.inl (λ_ z => z) (λov st => Sum.inr (ov,st))

def runFuncPrintTrace : Symbol → List Sim.Value → State → IO (Option Sim.Value × State) :=
  execFunc (throw (IO.userError "bottom"))
           throw
           (λev next => IO.println ev.asString >>= λ_ => next)
           (λov st => pure (ov, st))

end Sim
end LLVM
