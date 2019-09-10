
import init.data.array
import init.data.int
import init.data.rbmap

import .ast
import .bv
import .pp
import .type_context
import .sim_monad
import .value

namespace llvm.
open sim.

namespace mem.

partial def decomposeIntLE : Nat → Nat → List (bv 8)
| w, v =>
  if w <= 8 then
    [ bv.from_nat 8 v ]
  else
    (bv.from_nat 8 v) :: decomposeIntLE (w - 8) (v / ((2:Nat) ^ (8:Nat)))

partial def decomposeIntBE : Nat → Nat → List (bv 8) → List (bv 8)
| w, v, bs =>
  if w <= 8 then
    (bv.from_nat 8 v :: bs)
  else
    decomposeIntBE (w - 8) (v / (2 ^ (8:Nat))) (bv.from_nat 8 v :: bs)

def decomposeInt : endian → Nat → Nat → List (bv 8)
| endian.big, w, v    => decomposeIntBE w v []
| endian.little, w, v => decomposeIntLE w v
.

def storeBytes : bv 64 → List (bv 8) → sim.memMap → sim.memMap
| _, [], m    => m
| p, b::bs, m => storeBytes (p.add (bv.from_nat 64 1)) bs (m.insert p b)

def loadBytes : bv 64 → Nat → sim.memMap → Option (List (bv 8))
| _p, 0, _mem => pure []
|  p, Nat.succ n, mem =>
     do b <- mem.find p;
        bs <- loadBytes (p.add (bv.from_nat 64 1)) n mem;
        pure (b::bs)

def composeIntBE (w:Nat) : List (bv 8) → bv w → bv w
| [],    x => x
| b::bs, x => composeIntBE bs (bv.from_nat w ((x.to_nat * 2^(8:Nat)) + b.to_nat))

def composeIntLE (w:Nat) : List (bv 8) → bv w
| []    => bv.from_nat w 0
| b::bs => bv.from_nat w ((composeIntLE bs).to_nat * 2^(8:Nat) + b.to_nat)

def composeInt (w:Nat) : endian → List (bv 8) → bv w
| endian.big,    bs => composeIntBE w bs (bv.from_nat w 0)
| endian.little, bs => composeIntLE w bs


def store_int (w:Nat) (e:endian) (p:bv 64) (v:bv w) : sim Unit :=
  do st <- getState;
     let m' := storeBytes p (decomposeInt e w v.to_nat) st.mem;
     setState {st with mem := m' }.

def load_int (w:Nat) (e:endian) (p:bv 64) : sim (bv w) :=
  do st <- getState;
     match loadBytes p ((w+7)/8) st.mem with
     | none    => throw (IO.userError "Failed to load integer value")
     | some bs => pure (composeInt w e bs)

def load (dl:data_layout) : mem_type → bv 64 → sim sim.value
| mem_type.ptr _, p => sim.value.bv 64 <$> load_int 64 dl.int_layout p
| mem_type.int w, p => sim.value.bv w  <$> load_int w dl.int_layout p
| _, _ => throw (IO.userError "load: NYI!")

partial def store (dl:data_layout) : mem_type → bv 64 → sim.value → sim Unit
| mem_type.ptr _, p, value.bv 64 v => store_int 64 dl.int_layout p v

| mem_type.int w, p, value.bv w' v =>
    if w = w' then store_int w' dl.int_layout p v
    else throw (IO.userError ("Integer width mismatch in store: " ++ toString w ++ " " ++ toString w'))

| mem_type.struct si, p, sim.value.struct fs =>
   si.fields.miterate () (λidx f _ =>
     match fs.getOpt idx.val with
     | some fv => store f.value (p.add (bv.from_nat 64 f.offset.val)) fv.value
     | none    => throw (IO.userError "Struct type mismatch in store!"))

| mem_type.vector n _, p, value.vec mt vs =>
    let (sz,a) := mem_type.szAndAlign dl mt;
    let sz' := bv.from_nat 64 (padToAlignment sz a).val;
    if vs.size = n then
      () <$ Array.miterate vs p (λ_idx v p' =>
        do store mt p' v;
           pure (p'.add sz'))
    else throw (IO.userError
           ("Expected vector value with " ++ toString n ++ " elements, but got " ++ toString vs.size))

| mem_type.array n _, p, sim.value.array mt vs =>
    let (sz,a) := mem_type.szAndAlign dl mt;
    let sz' := bv.from_nat 64 (padToAlignment sz a).val;
    if vs.size = n then
      () <$ Array.miterate vs p (λ_idx v p' =>
        do store mt p' v;
           pure (p'.add sz'))
    else throw (IO.userError
           ("Expected array value with " ++ toString n ++ " elements, but got " ++ toString vs.size))

| _, _, _ => throw (IO.userError "Type/value mismatch in store!")
.

end mem.
end llvm.
