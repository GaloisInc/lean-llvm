import init.data.array
import init.data.int
import init.data.rbmap
import init.data.string

import .ast
import .bv
import .memory
import .pp
import .type_context
import .value
import .simMonad

namespace llvm.
namespace sim.

def unreachable {a} : sim a := throw (IO.userError "unreachable code!").

def eval_mem_type (t:llvm_type) : sim mem_type :=
  do st <- sim.getState;
     (match lift_mem_type st.dl st.mod.types t with
      | none => throw (IO.userError "could not lift type")
      | (some mt) => pure mt)


def eval : mem_type → llvm.value → sim sim.value
| _                (value.ident i)    := sim.lookupReg i
| (mem_type.int w) (value.integer n)  := pure (value.bv w (bv.from_int w n))
| (mem_type.int w) (value.bool true)  := pure (value.bv w (bv.from_int w 1))
| (mem_type.int w) (value.bool false) := pure (value.bv w (bv.from_int w 0))
| (mem_type.int w) (value.null)       := pure (value.bv w (bv.from_int w 0))
| (mem_type.int w) (value.zero_init)  := pure (value.bv w (bv.from_int w 0))
| (mem_type.int w) (value.undef)      := pure (value.bv w (bv.from_int w 0)) --???
| (mem_type.int 64) (value.symbol s)  :=
   do st <- sim.getState;
      match st.symmap.find s with
      | (some ptr) => pure (value.bv 64 ptr)
      | none => throw (IO.userError ("could not resolve symbol: " ++ s.symbol))

| _ _ := throw (IO.userError "bad value/type in evaluation")


def eval_typed (tv:typed llvm.value) : sim sim.value :=
  do mt <- eval_mem_type tv.type;
     eval mt tv.value.

def int_op (f:∀w, bv w -> bv w -> sim sim.value) : sim.value -> sim.value -> sim sim.value
| (value.bv wx vx) (value.bv wy vy) :=
    (match decEq wy wx with
    | Decidable.isTrue p  => f wx vx (Eq.rec vy p)
    | Decidable.isFalse _ => throw (IO.userError "expected same-width integer values")
    )
| _ _ := throw (IO.userError "expected integer arguments to int_op")
.

-- TODO, implement overflow checks
def eval_arith (op:arith_op) (x:sim.value) (y:sim.value) : sim sim.value :=
  match op with
  | (arith_op.add uof sof) => int_op (λ w a b => pure (value.bv w (@bv.add w a b))) x y
  | (arith_op.sub uof sof) => int_op (λ w a b => pure (value.bv w (@bv.sub w a b))) x y
  | (arith_op.mul uof sof) => int_op (λ w a b => pure (value.bv w (@bv.mul w a b))) x y
  | _ => throw (IO.userError "NYE: unimplemented arithmetic operation").

def asPred : sim.value → sim Bool
| (value.bv _ v) := if v.to_nat = 0 then pure false else pure true
| _ := throw (IO.userError "expected integer value as predicate")

def eval_icmp (op:icmp_op) : sim.value → sim.value → sim sim.value :=
  int_op (λw a b =>
    let t := (pure (value.bv 1 (bv.from_nat 1 1)) : sim sim.value);
    let f := (pure (value.bv 1 (bv.from_nat 1 0)) : sim sim.value);
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


def eval_bit (op:bit_op) : sim.value → sim.value → sim sim.value :=
  int_op (λw a b =>
    match op with
    | bit_op.and  => pure (value.bv w (@bv.bitwise_and w a b))
    | bit_op.or   => pure (value.bv w (@bv.bitwise_or w a b))
    | bit_op.xor  => pure (value.bv w (@bv.bitwise_xor w a b))
    | (bit_op.shl uov sov) => pure (value.bv w (@bv.shl w a b))
    | (bit_op.lshr exact)  => pure (value.bv w (@bv.lshr w a b))
    | (bit_op.ashr exact)  => pure (value.bv w (@bv.ashr w a b))
  ).

def eval_conv : conv_op → mem_type → sim.value → mem_type → sim sim.value
| conv_op.trunc (mem_type.int w1) (value.bv wx x) (mem_type.int w2) :=
    if w1 = wx ∧ w1 >= w2 then
      pure (value.bv w2 (bv.from_nat w2 x.to_nat))
    else
      throw (IO.userError "invalid trunc operation")
| conv_op.trunc _ _ _ := throw (IO.userError "invalid trunc operation")

| conv_op.zext (mem_type.int w1) (value.bv wx x) (mem_type.int w2) :=
    if w1 = wx ∧ w1 <= w2 then
      pure (value.bv w2 (bv.from_nat w2 x.to_nat))
    else
      throw (IO.userError "invalid zext operation")
| conv_op.zext _ _ _ := throw (IO.userError "invalid zext operation")

| conv_op.sext (mem_type.int w1) (value.bv wx x) (mem_type.int w2) :=
    if w1 = wx ∧ w1 <= w2 then
      pure (value.bv w2 (bv.from_int w2 x.to_int))
    else
      throw (IO.userError "invalid sext operation")
| conv_op.sext _ _ _ := throw (IO.userError "invalid sext operation")

| _ _ _ _ := throw (IO.userError "NYI: conversion op")


def phi (t:mem_type) (prv:block_label) : List (llvm.value × block_label) → sim sim.value
| [] := throw (IO.userError "phi node not defined for predecessor node")
| ((v,l)::xs) := if prv = l then eval t v else phi xs
.

def computeGEP {w} (dl:data_layout) : bv w → List sim.value → mem_type → sim (bv w)
| base [] _ := pure base
| base (value.bv w' v :: offsets) ty :=
    match ty with
    | (mem_type.array n ty') =>
         if (w = w') then
           let (sz,a) := mem_type.szAndAlign dl ty';
           let sz' := padToAlignment sz a;
           let idx := bv.from_int w (v.to_int * (Int.ofNat sz'.val));
           computeGEP (bv.add base idx) offsets ty'
         else
           throw (IO.userError "invalid array index value in GEP")

    | (mem_type.struct si) =>
         match si.fields.getOpt v.to_nat with
         | (some fi) => computeGEP (bv.add base (bv.from_nat w fi.offset.val)) offsets fi.value
         | none => throw (IO.userError "invalid struct index value in GEP")

    | (mem_type.packed_struct si) =>
         match si.fields.getOpt v.to_nat with
         | (some fi) => computeGEP (bv.add base (bv.from_nat w fi.offset.val)) offsets fi.value
         | none => throw (IO.userError "invalid struct index value in GEP")

    | _ => throw (IO.userError "Invalid GEP")

| _ ( _ :: _) _ := throw (IO.userError "invalid index value in GEP")


def evalInstr : instruction → sim (Option sim.value)
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
        st <- sim.getState;
        match fnv with
        | (value.bv 64 bv) =>
          match st.revsymmap.find bv with
          | (some s) => List.mmap eval_typed args >>= sim.call s
          | none => throw (IO.userError "expected function pointer value in call")
        | _ => throw (IO.userError "expected pointer value in call")

| (instruction.jump l) := sim.jump l

| (instruction.br c lt lf) :=
     do cv <- eval_typed c >>= asPred;
        if cv then sim.jump lt else sim.jump lf

| (instruction.unreachable) := unreachable

| (instruction.load ptr _atomicordering _oalign) :=
   do st <- sim.getState;
      let dl := st.dl;
      let tds := st.mod.types;
      mt <- eval_mem_type ptr.type;
      pv <- eval mt ptr.value;
      match (mt,pv) with
      | (mem_type.ptr st, value.bv 64 p) =>
          match sym_type_to_mem_type dl tds st with
          | (some loadtp) => some <$> mem.load dl loadtp p
          | none => throw (IO.userError "expected loadable pointer type in load" )
      | _ => throw (IO.userError "expected pointer value in load" )

| (instruction.store val ptr _align) :=
   do st <- sim.getState;
      pv <- eval_typed ptr;
      match pv with
      | (value.bv 64 p) =>
         do mt <- eval_mem_type val.type;
            v <- eval mt val.value;
            mem.store st.dl mt p v;
            pure none
      | _ => throw (IO.userError "expected pointer value in store" )

| (instruction.alloca tp onum oalign) :=
    do mt <- eval_mem_type tp;
       dl <- state.dl <$> sim.getState;
       sz <- match onum with
             | none => pure (mt.sz dl)
             | (some num) =>
                 (do n <- eval_typed num;
                    match n with
                    | (value.bv _ n') => pure ((mt.sz dl).mul n'.to_nat)
                    | _ => throw (IO.userError "expected integer value in alloca instruction"));
       a <- match oalign with
            | none => pure (mt.alignment dl)
            | (some align) =>
              match toAlignment align with
              | none => throw (IO.userError ("illegal alignment value in alloca: " ++ toString align))
              | (some a) => pure (maxAlignment (mt.alignment dl) a);
       ptr <- (do st <- sim.getState;
                  let (p,st') := allocOnStack sz a st;
                  sim.setState st';
                  pure p);
       pure (some (value.bv 64 ptr))

| (instruction.gep _bounds base offsets) :=
     do dl <- state.dl <$> sim.getState;
        tds <- (module.types ∘ state.mod) <$> sim.getState;
        baseType <- eval_mem_type base.type;
        match baseType with
        | (mem_type.ptr stp) =>
          match sym_type_to_mem_type dl tds stp with
          | (some mt) =>
             do base' <- eval baseType base.value;
                offsets' <- Array.mmap eval_typed offsets;
                match base' with
                | value.bv w baseptr =>
                    (some ∘ value.bv w) <$> computeGEP dl baseptr offsets'.toList (mem_type.array 0 mt)
                | _ => throw (IO.userError "Expected bitvector in GEP base value")
          | none => throw (IO.userError "Invalid GEP, bad base type")
        | _ => throw (IO.userError "Expected pointer type in GEP base")

| _ := throw (IO.userError "NYE: unimplemented instruction")
.

def evalStmt (s:stmt) : sim Unit :=
  do res <- evalInstr s.instr;
     match (s.assign, res) with
     | (none, _)        => pure ()
     | (some i, some v) => sim.assignReg i v
     | (some _, none)   => throw (IO.userError "expected instruction to compute a value").

def evalStmts (stmts:Array stmt) : sim Unit :=
  Array.mfoldl (λ_ s => evalStmt s) () stmts

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
    (kret: Option sim.value → state → z)
    (kcall: (Option sim.value → state → z) → symbol → List sim.value → state → z)
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

def assignArgs : List (typed ident) → List sim.value → regMap → sim regMap
| [] [] regs := pure regs
| (f::fs) (a::as) regs := assignArgs fs as (RBMap.insert regs f.value a)
| _ _ _ := throw (IO.userError ("Acutal/formal argument mismatch")).

def entryLabel (d:define) : sim block_label :=
  match Array.getOpt d.body 0 with
  | (some bb) => pure bb.label
  | none      => throw (IO.userError "definition does not have entry block!").

partial def execFunc {z} (zinh:z) (kerr:IO.Error → z)
  : (Option sim.value → state → z) → symbol → List sim.value → state → z

| kret s args st :=
   (do func   <- findFunc s st.mod;
       locals <- assignArgs func.args.toList args RBMap.empty;
       lab    <- entryLabel func;
       sim.setFrame (frame.mk locals func lab none st.stackPtr);
       findBlock lab func >>= evalStmts
   ).runSim
      { kerr  := kerr
      , kret  := kret
      , kcall := execFunc
      , kjump := execBlock zinh kerr kret execFunc
      }
      (λ_ _ _ => kerr (IO.userError "unterminated basic block!"))
      (default _)
      st.

def runFunc : symbol → List sim.value → state → Sum IO.Error (Option sim.value × state) :=
  execFunc (Sum.inl (IO.userError "bottom")) Sum.inl (λov st => Sum.inr (ov,st)).

end sim.
end llvm.
