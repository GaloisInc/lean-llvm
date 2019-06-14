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

  Array.miterate m.defines () (λ_i dfn _m,
        IO.println (pp.render (llvm.pp_define dfn))),

  (v,st) <- runFunc (symbol.mk "fib")
             [ runtime_value.int 32 (bv.from_nat 32 20)
             ]
             (state.mk RBMap.empty m),

  (match v with
   | (runtime_value.int _ x) := IO.println ("0x" ++ (Nat.toDigits 16 x.to_nat).asString)
   | _ := pure ()),

  pure 0
  
