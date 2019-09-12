import init.data.rbmap
import init.control.except

import .ast
import .bv
import .pp
import .data_layout
import .llvm_lib
import .sim_monad
import .simulate

open llvm.

def readmain (xs : List String) : IO UInt32 := do
  ctx ← ffi.newContext;
  mb ← ffi.newMemoryBufferFromFile xs.head;
  m ← ffi.parseBitcodeFile mb ctx >>= loadModule;
  dl <- match computeDataLayout m.data_layout with
        | (Except.error msg) => throw (IO.userError msg)
        | (Except.ok dl) => pure dl;

  IO.println (pp.render (pp_module m));

  let st0 := initializeState m dl;

  -- let res :=
  --    sim.runFunc (symbol.mk "add_offset")
  --            [ sim.value.bv 64 (bv.from_nat 64 8)
  --            , sim.value.bv 32 (bv.from_nat 32 8)
  --            ]
  --            st0;

  let res :=
     sim.runFunc (symbol.mk "foo")
             [ sim.value.bv 32 (bv.from_nat 32 8)
             ]
             st0;

  match res with
  | (Sum.inl err) => throw err
  | (Sum.inr (sim.value.bv _ x, _)) =>
       do IO.println ("0x" ++ (Nat.toDigits 16 x.to_nat).asString);
          pure 0
  | _ => pure 0

def buildmain (xs : List String) : IO UInt32 := do
  ctx <- ffi.newContext;
  mod <- ffi.newModule ctx "testmodule.bc";
  ffi.printModule mod;
  pure 0

--def main := buildmain
def main := readmain
