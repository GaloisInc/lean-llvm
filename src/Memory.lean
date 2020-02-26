import Init.Data.Array
import Init.Data.Int
import Init.Data.RBMap

import Galois.Data.Bitvec

import LeanLLVM.AST
import LeanLLVM.PP
import LeanLLVM.TypeContext
import LeanLLVM.SimMonad
import LeanLLVM.Value

namespace llvm.
open sim.

namespace mem.

partial def decomposeIntLE : Nat → Nat → List (bitvec 8)
| w, v =>
  if w <= 8 then
    [ bitvec.of_nat 8 v ]
  else
    (bitvec.of_nat 8 v) :: decomposeIntLE (w - 8) (v / ((2:Nat) ^ (8:Nat)))

partial def decomposeIntBE : Nat → Nat → List (bitvec 8) → List (bitvec 8)
| w, v, bs =>
  if w <= 8 then
    (bitvec.of_nat 8 v :: bs)
  else
    decomposeIntBE (w - 8) (v / (2 ^ (8:Nat))) (bitvec.of_nat 8 v :: bs)

def decomposeInt : endian → Nat → Nat → List (bitvec 8)
| endian.big, w, v    => decomposeIntBE w v []
| endian.little, w, v => decomposeIntLE w v
.

def storeBytes : bitvec 64 → List (bitvec 8) → sim.memMap → sim.memMap
| _, [], m    => m
| p, b::bs, m => storeBytes (p.add (bitvec.of_nat 64 1)) bs (m.insert p b)

def loadBytes : bitvec 64 → Nat → sim.memMap → Option (List (bitvec 8))
| _p, 0, _mem => pure []
|  p, Nat.succ n, mem =>
     do b <- mem.find? p;
        bs <- loadBytes (p.add (bitvec.of_nat 64 1)) n mem;
        pure (b::bs)

def composeIntBE (w:Nat) : List (bitvec 8) → bitvec w → bitvec w
| [],    x => x
| b::bs, x => composeIntBE bs (bitvec.of_nat w ((x.to_nat * 2^(8:Nat)) + b.to_nat))

def composeIntLE (w:Nat) : List (bitvec 8) → bitvec w
| []    => bitvec.of_nat w 0
| b::bs => bitvec.of_nat w ((composeIntLE bs).to_nat * 2^(8:Nat) + b.to_nat)

def composeInt (w:Nat) : endian → List (bitvec 8) → bitvec w
| endian.big,    bs => composeIntBE w bs (bitvec.of_nat w 0)
| endian.little, bs => composeIntLE w bs


def store_int (w:Nat) (e:endian) (p:bitvec 64) (v:bitvec w) : sim Unit :=
  do st <- getState;
     let m' := storeBytes p (decomposeInt e w v.to_nat) st.mem;
     setState {st with mem := m' }.

def load_int (w:Nat) (e:endian) (p:bitvec 64) : sim (bitvec w) :=
  do st <- getState;
     match loadBytes p ((w+7)/8) st.mem with
     | none    => throw (IO.userError "Failed to load integer value")
     | some bs => pure (composeInt w e bs)

def load (dl:data_layout) : mem_type → bitvec 64 → sim sim.value
| mem_type.ptr _, p => sim.value.bv 64 <$> load_int 64 dl.int_layout p
| mem_type.int w, p => sim.value.bv w  <$> load_int w dl.int_layout p
| _, _ => throw (IO.userError "load: NYI!")

partial def store (dl:data_layout) : mem_type → bitvec 64 → sim.value → sim Unit
| mem_type.ptr _, p, value.bv 64 v => store_int 64 dl.int_layout p v

| mem_type.int w, p, value.bv w' v =>
    if w = w' then store_int w' dl.int_layout p v
    else throw (IO.userError ("Integer width mismatch in store: " ++ toString w ++ " " ++ toString w'))

| mem_type.struct si, p, sim.value.struct fs =>
   si.fields.iterateM () (λidx f _ =>
     match fs.get? idx.val with
     | some fv => store f.value (p.add (bitvec.of_nat 64 f.offset.val)) fv.value
     | none    => throw (IO.userError "Struct type mismatch in store!"))

| mem_type.vector n _, p, value.vec mt vs =>
    let (sz,a) := mem_type.szAndAlign dl mt;
    let sz' := bitvec.of_nat 64 (padToAlignment sz a).val;
    if vs.size = n then
      () <$ Array.iterateM vs p (λ_idx v p' =>
        do store mt p' v;
           pure (p'.add sz'))
    else throw (IO.userError
           ("Expected vector value with " ++ toString n ++ " elements, but got " ++ toString vs.size))

| mem_type.array n _, p, sim.value.array mt vs =>
 do let (sz,a) := mem_type.szAndAlign dl mt;
    let sz' := bitvec.of_nat 64 (padToAlignment sz a).val;
    if vs.size = n then
      () <$ Array.iterateM vs p (λ_idx v p' =>
        do store mt p' v;
           pure (p'.add sz'))
    else throw (IO.userError
           ("Expected array value with " ++ toString n ++ " elements, but got " ++ toString vs.size))


| _, _, _ => throw (IO.userError "Type/value mismatch in store!")
.

end mem.

def allocGlobalVariable (gv:global) : sim Unit :=
   do st <- sim.getState;
      mt <- sim.eval_mem_type gv.type;
      ptr <- 
        (match st.symmap.find? gv.sym with
         | some ptr => pure ptr
         | none =>
             do let (sz, align) := mem_type.szAndAlign st.dl mt;
                let (ptr, st') := allocOnHeap sz align st;
                sim.setState (linkSymbol st' (gv.sym, ptr));
                pure ptr);

      match gv.value with
      | none => pure ()
      | some val =>
         do v <- sim.eval mt val;
            mem.store st.dl mt ptr v

def allocGlobalSymbols (mod:module) : sim Unit :=
  do st0 <- getState;  
     setState (List.foldr allocFunctionSymbol st0
        (List.map declare.name mod.declares.toList ++ List.map define.name mod.defines.toList));
     mod.globals.iterateM () (λ_ gv _ => allocGlobalVariable gv)
  
def runInitializers (mod:module) (dl:data_layout) (ls:List (symbol × bitvec 64)): IO state :=
  runSim 
    (allocGlobalSymbols mod) 
    { kerr := throw
    , kret := λ _ _ => throw (IO.userError "No return point")
    , kcall := λ _ _ _ _ => throw (IO.userError "no calls")
    , kjump := λ _ _ _ => throw (IO.userError "no jumps")
    , ktrace := λ _ a => a
    }
    (λ _u _frm st => pure st)
    (arbitrary _)
    (initializeState mod dl ls)

end llvm.
