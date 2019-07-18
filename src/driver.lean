import init.data.rbmap
import init.control.except

import .ast
import .bv
import .pp
import .data_layout
import .llvm_lib
import .simulate

open llvm.

def main (xs : List String) : IO UInt32 := do
  ctx ← newLLVMContext;
  mb ← newMemoryBufferFromFile xs.head;
  m ← parseBitcodeFile mb ctx >>= extractModule;
  dl <- match computeDataLayout m.data_layout with
        | (Except.error msg) => throw (IO.userError msg)
        | (Except.ok dl) => pure dl;



  IO.println (pp.render (pp_module m));

  let res :=
     runFunc (symbol.mk "fib")
             [ runtime_value.int 32 (bv.from_nat 32 8)
             ]
             (state.mk RBMap.empty m dl) in
  match res with
  | (Sum.inl err) => throw err
  | (Sum.inr (runtime_value.int _ x, _)) =>
       do IO.println ("0x" ++ (Nat.toDigits 16 x.to_nat).asString);
          pure 0
  | _ => pure 0
