
import .ast
import .bv
import .memory
import .pp
import .sim_monad
import .type_context
import .value

namespace llvm.
namespace sim.

def unreachable {a} : sim a := throw (IO.userError "unreachable code!").

def int_op (f:∀w, bv w -> bv w -> sim sim.value) : sim.value -> sim.value -> sim sim.value
| value.bv wx vx, value.bv wy vy =>
    match decEq wy wx with
    | Decidable.isTrue p  => f wx vx (Eq.rec vy p)
    | Decidable.isFalse _ => throw (IO.userError "expected same-width integer values")
| _, _ => throw (IO.userError "expected integer arguments to int_op")

-- TODO, implement overflow checks
def eval_arith (op:arith_op) (x:sim.value) (y:sim.value) : sim sim.value :=
  match op with
  | (arith_op.add uof sof) => int_op (λ w a b => pure (value.bv w (@bv.add w a b))) x y
  | (arith_op.sub uof sof) => int_op (λ w a b => pure (value.bv w (@bv.sub w a b))) x y
  | (arith_op.mul uof sof) => int_op (λ w a b => pure (value.bv w (@bv.mul w a b))) x y
  | _ => throw (IO.userError "NYE: unimplemented arithmetic operation").

def asPred : sim.value → sim Bool
| value.bv _ v => if v.to_nat = 0 then pure false else pure true
| _ => throw (IO.userError "expected integer value as predicate")

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
| conv_op.trunc, mem_type.int w1, value.bv wx x, mem_type.int w2 =>
    if w1 = wx ∧ w1 >= w2 then
      pure (value.bv w2 (bv.from_nat w2 x.to_nat))
    else
      throw (IO.userError "invalid trunc operation")
| conv_op.trunc, _, _, _ => throw (IO.userError "invalid trunc operation")


| conv_op.zext, mem_type.int w1, value.bv wx x, mem_type.int w2 =>
    if w1 = wx ∧ w1 <= w2 then
      pure (value.bv w2 (bv.from_nat w2 x.to_nat))
    else
      throw (IO.userError "invalid zext operation")
| conv_op.zext, _, _, _ => throw (IO.userError "invalid zext operation")


| conv_op.sext, mem_type.int w1, value.bv wx x, mem_type.int w2 =>
    if w1 = wx ∧ w1 <= w2 then
      pure (value.bv w2 (bv.from_int w2 x.to_int))
    else
      throw (IO.userError "invalid sext operation")
| conv_op.sext, _, _, _ => throw (IO.userError "invalid sext operation")

| conv_op.ptr_to_int, _, v, _ => pure v -- TODO, more checking
| conv_op.int_to_ptr, _, v, _ => pure v -- TODO, more checking
| conv_op.bit_cast, _, v, _ => pure v -- TODO, more checking!

| _, _, _, _ => throw (IO.userError "NYI: conversion op")


def phi (t:mem_type) (prv:block_label) : List (llvm.value × block_label) → sim sim.value
| [] => throw (IO.userError "phi node not defined for predecessor node")
| (v,l)::xs => if prv = l then eval t v else phi xs


def computeGEP {w} (dl:data_layout) : bv w → List sim.value → mem_type → sim (bv w)
| base, [], _ => pure base
| base, value.bv w' v :: offsets, ty =>
    match ty with
    | mem_type.array _n ty' =>
         if (w = w') then
           let (sz,a) := mem_type.szAndAlign dl ty';
           let sz' := padToAlignment sz a;
           let idx := bv.from_int w (v.to_int * (Int.ofNat sz'.val));
           computeGEP (bv.add base idx) offsets ty'
         else
           throw (IO.userError "invalid array index value in GEP")

    | mem_type.struct si =>
         match si.fields.getOpt v.to_nat with
         | (some fi) => computeGEP (bv.add base (bv.from_nat w fi.offset.val)) offsets fi.value
         | none => throw (IO.userError "invalid struct index value in GEP")

    | _ => throw (IO.userError "Invalid GEP")

| _, _::_, _ => throw (IO.userError "invalid index value in GEP")


def evalInstr : instruction → sim (Option sim.value)
| instruction.ret_void => sim.returnVoid
| instruction.ret v    => eval_typed v >>= sim.returnValue

| instruction.phi tp xs =>
     do frm <- sim.getFrame;
        t  <- eval_mem_type tp;
        match frm.prev with
        | none => throw (IO.userError "phi nodes not allowed in entry block")
        | some prv => some <$> phi t prv xs.toList

| instruction.arith op x y =>
     do t  <- eval_mem_type x.type;
        xv <- eval t x.value;
        yv <- eval t y;
        some <$> eval_arith op xv yv

| instruction.bit op x y =>
     do t  <- eval_mem_type x.type;
        xv <- eval t x.value;
        yv <- eval t y;
        some <$> eval_bit op xv yv

| instruction.conv op x outty =>
     do t  <- eval_mem_type x.type;
        xv <- eval t x.value;
        t' <- eval_mem_type outty;
        some <$> eval_conv op t xv t'

| instruction.icmp op x y =>
     do t  <- eval_mem_type x.type;
        xv <- eval t x.value;
        yv <- eval t y;
        some <$> eval_icmp op xv yv

| instruction.select c x y =>
     do cv <- eval_typed c >>= asPred;
        t  <- eval_mem_type x.type;
        xv <- eval t x.value;
        yv <- eval t y;
        if cv then pure (some xv) else pure (some yv)

| instruction.call _tail _rettp fn args =>
     do fnv <- eval (mem_type.ptr sym_type.void) fn; -- TODO? more accurate type?
        st <- sim.getState;
        match fnv with
        | value.bv 64 bv =>
          match st.revsymmap.find bv with
          | some s => List.mmap eval_typed args.toList >>= sim.call s
          | none => throw (IO.userError "expected function pointer value in call")
        | _ => throw (IO.userError "expected pointer value in call")

| instruction.jump l => sim.jump l

| instruction.br c lt lf =>
     do cv <- eval_typed c >>= asPred;
        if cv then sim.jump lt else sim.jump lf

| instruction.unreachable => unreachable

| instruction.load ptr _atomicordering _oalign =>
   do st <- sim.getState;
      let dl := st.dl;
      let tds := st.mod.types;
      mt <- eval_mem_type ptr.type;
      pv <- eval mt ptr.value;
      match mt, pv with
      | mem_type.ptr st, value.bv 64 p =>
          match sym_type_to_mem_type dl tds st with
          | some loadtp =>
               do v <- mem.load dl loadtp p;
                  sim.trace (trace_event.load p loadtp v);
                  pure (some v)
          | none => throw (IO.userError "expected loadable pointer type in load" )
      | _, _ => throw (IO.userError "expected pointer value in load" )

| instruction.store val ptr _align =>
   do st <- sim.getState;
      pv <- eval_typed ptr;
      match pv with
      | value.bv 64 p =>
            do mt <- eval_mem_type val.type;
               v <- eval mt val.value;
               mem.store st.dl mt p v;
               sim.trace (trace_event.store p mt v);
               pure none
      | _ => throw (IO.userError "expected pointer value in store" )

| instruction.alloca tp onum oalign =>
    do mt <- eval_mem_type tp;
       dl <- state.dl <$> sim.getState;
       sz <- match onum with
             | none => pure (mt.sz dl)
             | some num =>
                 (do n <- eval_typed num;
                    match n with
                    | value.bv _ n' => pure ((mt.sz dl).mul n'.to_nat)
                    | _ => throw (IO.userError "expected integer value in alloca instruction"));
       a <- match oalign with
            | none => pure (mt.alignment dl)
            | some align =>
              match toAlignment (bytes.mk align) with
              | none => throw (IO.userError ("illegal alignment value in alloca: " ++ toString align))
              | some a => pure (maxAlignment (mt.alignment dl) a);
       ptr <- (do st <- sim.getState;
                  let (p,st') := allocOnStack sz a st;
                  sim.setState st';
                  pure p);
       sim.trace (trace_event.alloca ptr sz);
       pure (some (value.bv 64 ptr))


| instruction.gep _bounds base offsets =>
     do dl <- state.dl <$> sim.getState;
        tds <- (module.types ∘ state.mod) <$> sim.getState;
        baseType <- eval_mem_type base.type;
        match baseType with
        | mem_type.ptr stp =>
          match sym_type_to_mem_type dl tds stp with
          | some mt =>
             do base' <- eval baseType base.value;
                offsets' <- Array.mmap eval_typed offsets;
                match base' with
                | value.bv w baseptr =>
                    (some ∘ value.bv w) <$> computeGEP dl baseptr offsets'.toList (mem_type.array 0 mt)
                | _ => throw (IO.userError "Expected bitvector in GEP base value")
          | none => throw (IO.userError "Invalid GEP, bad base type")
        | _ => throw (IO.userError "Expected pointer type in GEP base")


| _ => throw (IO.userError "NYE: unimplemented instruction")

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
    (ktrace : trace_event → z → z)
    : block_label → frame → state → z

| next, frm, st =>
   (findBlock next frm.func >>= evalStmts).runSim
      { kerr  := kerr
      , kret  := kret
      , kcall := kcall
      , kjump := execBlock
      , ktrace := ktrace
      }
      (λ _ _ _ => kerr $ IO.userError ("expected block terminatror at the end of block: "
                                    ++ pp.render (pp_label next)))
      { frm with curr := next, prev := some frm.curr }
      st

def assignArgs : List (typed ident) → List sim.value → regMap → sim regMap
| [], [], regs => pure regs
| f::fs, a::as, regs => assignArgs fs as (RBMap.insert regs f.value a)
| _, _, _ => throw (IO.userError ("Acutal/formal argument mismatch")).

def entryLabel (d:define) : sim block_label :=
  match Array.getOpt d.body 0 with
  | some bb => pure bb.label
  | none    => throw $ IO.userError ("definition does not have entry block! " ++ d.name.symbol)

partial def execFunc {z} (zinh:z) (kerr:IO.Error → z) (ktrace : trace_event → z → z)
  : (Option sim.value → state → z) → symbol → List sim.value → state → z

| kret, s, args, st =>
   (do func   <- findFunc s st.mod;
       locals <- assignArgs func.args.toList args RBMap.empty;
       lab    <- entryLabel func;
       sim.setFrame (frame.mk locals func lab none st.stackPtr);
       findBlock lab func >>= evalStmts
   ).runSim
      { kerr  := kerr
      , kret  := kret
      , kcall := execFunc
      , kjump := execBlock zinh kerr kret execFunc ktrace
      , ktrace := ktrace
      }
      (λ_ _ _ => kerr (IO.userError "unterminated basic block!"))
      (default _)
      st.

def runFunc : symbol → List sim.value → state → Sum IO.Error (Option sim.value × state) :=
  execFunc (Sum.inl (IO.userError "bottom")) Sum.inl (λ_ z => z) (λov st => Sum.inr (ov,st)).

def runFuncPrintTrace : symbol → List sim.value → state → IO (Option sim.value × state) :=
  execFunc (throw (IO.userError "bottom"))
           throw
           (λev next => IO.println ev.asString >>= λ_ => next)
           (λov st => pure (ov, st)).

end sim.
end llvm.
