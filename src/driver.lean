import init.data.rbmap

import .ast
import .bv
import .pp
import .llvm_lib
import .simulate

open llvm.

def main (xs : List String) : IO UInt32 := do

  ctx ← newLLVMContext,
  mb ← newMemoryBufferFromFile xs.head,
  m ← parseBitcodeFile mb ctx >>= extractModule,

  IO.println (pp.render (pp_module m)),

  (v,st) <- runFunc (symbol.mk "blshr")
             [ runtime_value.int 32 (bv.from_nat 32 16)
             , runtime_value.int 32 (bv.from_nat 32 4)
             ]
             (state.mk RBMap.empty m),

  (match v with
   | (runtime_value.int _ x) := IO.println ("0x" ++ (Nat.toDigits 16 x.to_nat).asString)
   | _ := pure ()),

  pure 0
  
