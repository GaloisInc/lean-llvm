import LeanLLVM.LLVMFFI
import LeanLLVM.DataLayout
import LeanLLVM.PP

namespace LLVM

def parseBitcodeFile (buffer : FFI.MemoryBuffer) (ctx : FFI.Context) : IO (Except String FFI.Module) :=
MonadExcept.catch
  ((FFI.Prim.parseBitcodeFile buffer ctx) >>= (pure ∘ Except.ok))
  (λ e =>
    match e with
    | IO.Error.userError msg => pure $ Except.error msg
    | _ => throw e
  )


-- FIXME should we instead take a DataLayout and render it? No such rendering exists currently,
-- and there are a few subtleties in doing so (e.g., parsing of a data layout expects `aNAT:NAT`
-- in the input string but only saves a single natural number, default values probably don't need
-- emitted, etc).
def parseAssembly (buffer : FFI.MemoryBuffer) (ctx : FFI.Context) (llvmDataLayouStr : String) : IO (Except String FFI.Module) :=
MonadExcept.catch
  (FFI.Prim.parseAssembly buffer ctx llvmDataLayouStr >>= (pure ∘ Except.ok))
  (λ e =>
    match e with
    | IO.Error.userError msg => pure $ Except.error msg
    | _ => throw e
  )

end LLVM
