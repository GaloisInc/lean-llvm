import init.data.rbmap
import init.control.except

import .ast
import .bv
import .pp
import .data_layout
import .llvm_lib
import .llvm_output
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

  st0 <- runInitializers m dl 
             [(symbol.mk "arr", bv.from_nat 64 0x202000) ];

  --let st0 := initializeState m dl;

  -- let res :=
  --    sim.runFunc (symbol.mk "add_offset")
  --            [ sim.value.bv 64 (bv.from_nat 64 8)
  --            , sim.value.bv 32 (bv.from_nat 32 8)
  --            ]
  --            st0;

  res <-
     sim.runFuncPrintTrace (symbol.mk "run_test")
             [
             ]
             st0;

  match res with
  | (sim.value.bv _ x, _) =>
       do IO.println ("0x" ++ (Nat.toDigits 16 x.to_nat).asString);
          pure 0
  | _ => pure 0

def testModule : llvm.module :=
  llvm.module.mk
     (some "testmodule")
     []
     Array.empty -- types
     Array.empty -- named md
     Array.empty -- unnamed md
     RBMap.empty -- comdat
     Array.empty -- globals
     Array.empty -- declares
     Array.empty -- defines
     Array.empty -- inline ASM
     Array.empty -- global aliases


def buildmain (xs : List String) : IO UInt32 := do
  ctx <- ffi.newContext;
  (_,mod) <- output.run (outputModule ctx testModule);
  ffi.printModule mod;
  pure 0

--def main := buildmain
def main := readmain
