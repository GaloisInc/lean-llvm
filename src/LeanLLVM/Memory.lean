import Init.Data.Array
import Init.Data.Int
import Std.Data.RBMap

import Galois.Data.Bitvec

import LeanLLVM.AST
import LeanLLVM.PP
import LeanLLVM.TypeContext
import LeanLLVM.SimMonad
import LeanLLVM.Value

open Std (RBMap)

namespace LLVM
open Sim

namespace Mem

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

def decomposeInt : Endian → Nat → Nat → List (bitvec 8)
| Endian.big, w, v    => decomposeIntBE w v []
| Endian.little, w, v => decomposeIntLE w v

def storeBytes : bitvec 64 → List (bitvec 8) → Sim.memMap → Sim.memMap
| _, [], m    => m
| p, b::bs, m => storeBytes (p.add (bitvec.of_nat 64 1)) bs (m.insert p b)

def loadBytes : bitvec 64 → Nat → Sim.memMap → Option (List (bitvec 8))
| _p, 0, _mem => pure []
| p, Nat.succ n, mem => do
  let b ← mem.find? p
  let bs ← loadBytes (p.add (bitvec.of_nat 64 1)) n mem
  pure (b::bs)

def composeIntBE (w:Nat) : List (bitvec 8) → bitvec w → bitvec w
| [],    x => x
| b::bs, x => composeIntBE w bs (bitvec.of_nat w ((x.to_nat * 2^(8:Nat)) + b.to_nat))

def composeIntLE (w:Nat) : List (bitvec 8) → bitvec w
| []    => bitvec.of_nat w 0
| b::bs => bitvec.of_nat w ((composeIntLE w bs).to_nat * 2^(8:Nat) + b.to_nat)

def composeInt (w:Nat) : Endian → List (bitvec 8) → bitvec w
| Endian.big,    bs => composeIntBE w bs (bitvec.of_nat w 0)
| Endian.little, bs => composeIntLE w bs

def store_int (w:Nat) (e:Endian) (p:bitvec 64) (v:bitvec w) : Sim Unit := do
  let st ←  getState
  let m' := storeBytes p (decomposeInt e w v.to_nat) st.mem;
  setState {st with mem := m' }

def load_int (w:Nat) (e:Endian) (p:bitvec 64) : Sim (bitvec w) := do
  let st ←  getState
  match loadBytes p ((w+7)/8) st.mem with
  | none    => throw (IO.userError "Failed to load integer value")
  | some bs => pure (composeInt w e bs)

def load (dl:DataLayout) : mem_type → bitvec 64 → Sim Sim.Value
| mem_type.ptr _, p => Sim.Value.bv <$> load_int 64 dl.intLayout p
| mem_type.int w, p => Sim.Value.bv <$> load_int w dl.intLayout p
| _, _ => throw (IO.userError "load: NYI!")

partial def store (dl:DataLayout) : mem_type → bitvec 64 → Sim.Value → Sim Unit
| mem_type.ptr _, p, @Value.bv 64 v => store_int 64 dl.intLayout p v

| mem_type.int w, p, @Value.bv w' v =>
  if w = w' then
    store_int w' dl.intLayout p v
  else
    throw (IO.userError ("Integer width mismatch in store: " ++ toString w ++ " " ++ toString w'))

| mem_type.struct si, p, Sim.Value.struct fs => do
  let mut i := 0
  for f in si.fields do
    match fs.get? i with
    | some fv =>
      store dl f.value (p.add (bitvec.of_nat 64 f.offset)) fv.value
      i := i+1
    | none    => throw (IO.userError "Struct type mismatch in store!")

| mem_type.vector n _, p, Sim.Value.vec mt vs =>
  let (sz,a) := mem_type.szAndAlign dl mt;
  let sz' := bitvec.of_nat 64 (padToAlignment sz a);
  if vs.size = n then do
    let mut p' := p;
    for v in vs do
      store dl mt p' v
      p' := p'.add sz'
  else
    throw (IO.userError
           ("Expected vector value with " ++ toString n ++ " elements, but got " ++ toString vs.size))

| mem_type.array n _, p, Sim.Value.array mt vs => do
  let (sz,a) := mem_type.szAndAlign dl mt;
  let sz' := bitvec.of_nat 64 (padToAlignment sz a);
  if vs.size = n then do
    let mut p' := p;
    for v in vs do
      store dl mt p' v
      p' := p'.add sz'
   else
    throw (IO.userError
           ("Expected array value with " ++ toString n ++ " elements, but got " ++ toString vs.size))
| _, _, _ => throw (IO.userError "Type/value mismatch in store!")

end Mem

def allocGlobalVariable (gv:Global) : Sim Unit := do
  let st ←  Sim.getState
  let mt ← Sim.eval_mem_type gv.type
  let ptr ← match st.symmap.find? gv.sym with
            | some ptr => pure ptr
            | none => do
              let (sz, align) := mem_type.szAndAlign st.dl mt
              let (ptr, st') := allocOnHeap sz align st
              Sim.setState (linkSymbol st' (gv.sym, ptr))
              pure ptr
  match gv.value with
  | none => pure ()
  | some val => do
    let v ←  Sim.eval mt val
    Mem.store st.dl mt ptr v

def allocGlobalSymbols (mod:Module) : Sim Unit := do
  let st0 <- getState
  let declNames := mod.declares.toList.map (λd => d.name)
  let defiNames := mod.defines.toList.map (λd => d.name)
  setState (List.foldr allocFunctionSymbol st0 (declNames ++ defiNames))
  for gv in mod.globals do
    allocGlobalVariable gv

def runInitializers (mod:Module) (dl:DataLayout) (ls:List (Symbol × bitvec 64)): IO State :=
  runSim
    (allocGlobalSymbols mod)
    { kerr := throw
    , kret := λ _ _ => throw (IO.userError "No return point")
    , kcall := λ _ _ _ _ => throw (IO.userError "no calls")
    , kjump := λ _ _ _ => throw (IO.userError "no jumps")
    , ktrace := λ _ a => a
    }
    (λ _u _frm st => pure st)
    arbitrary
    (initializeState mod dl ls)

end LLVM
