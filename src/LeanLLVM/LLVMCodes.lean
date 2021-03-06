namespace LLVM
namespace Code

-- C.F. <llvm/IR/Type.h>, Type::TypeID
inductive TypeID : Type
| void
| half
| float
| double
| x86FP80
| fp128
| ppcFP128
| label
| metadata
| x86mmx
| token
| integer
| function
| struct
| array
| pointer
| vector

namespace TypeID
def asString : TypeID -> String
| void => "void"
| half => "half"
| float => "float"
| double => "double"
| x86FP80 => "x86_fp80"
| fp128 => "fp128"
| ppcFP128 => "ppc_fp128"
| label => "label"
| metadata => "metadata"
| x86mmx => "x86_mmx"
| token => "token"
| integer => "integer"
| function => "function"
| struct => "struct"
| array => "array"
| pointer => "pointer"
| vector => "vector"

end TypeID

-- | Instruction type tag
--
-- Note. Constructor names are generated from LLVM files and capitalized
-- according to names in files.
inductive Instr : Type
| Unused -- Burn constructor number 0, which is not used for any instruction value


| Ret
| Br
| Switch
| IndirectBr
| Invoke
| Resume
| Unreachable
| CleanupRet
| CatchRet
| CatchSwitch




| FNeg




| Add
| FAdd
| Sub
| FSub
| Mul
| FMul
| UDiv
| SDiv
| FDiv
| URem
| SRem
| FRem


| Shl
| LShr
| AShr
| And
| Or
| Xor




| Alloca
| Load
| Store
| GetElementPtr
| Fence
| AtomicCmpXchg
| AtomicRMW






| Trunc
| ZExt
| SExt
| FPToUI
| FPToSI
| UIToFP
| SIToFP
| FPTrunc
| FPExt
| PtrToInt
| IntToPtr
| BitCast
| AddrSpaceCast



| CleanupPad
| CatchPad




| ICmp
| FCmp
| PHI
| Call
| Select
| UserOp1
| UserOp2
| VAArg
| ExtractElement
| InsertElement
| ShuffleVector
| ExtractValue
| InsertValue
| LandingPad

namespace Instr
def asString : Instr -> String
| Unused => "Unused"


| Ret => "Ret"
| Br => "Br"
| Switch => "Switch"
| IndirectBr => "IndirectBr"
| Invoke => "Invoke"
| Resume => "Resume"
| Unreachable => "Unreachable"
| CleanupRet => "CleanupRet"
| CatchRet => "CatchRet"
| CatchSwitch => "CatchSwitch"




| FNeg => "FNeg"




| Add => "Add"
| FAdd => "FAdd"
| Sub => "Sub"
| FSub => "FSub"
| Mul => "Mul"
| FMul => "FMul"
| UDiv => "UDiv"
| SDiv => "SDiv"
| FDiv => "FDiv"
| URem => "URem"
| SRem => "SRem"
| FRem => "FRem"


| Shl => "Shl"
| LShr => "LShr"
| AShr => "AShr"
| And => "And"
| Or => "Or"
| Xor => "Xor"




| Alloca => "Alloca"
| Load => "Load"
| Store => "Store"
| GetElementPtr => "GetElementPtr"
| Fence => "Fence"
| AtomicCmpXchg => "AtomicCmpXchg"
| AtomicRMW => "AtomicRMW"






| Trunc => "Trunc"
| ZExt => "ZExt"
| SExt => "SExt"
| FPToUI => "FPToUI"
| FPToSI => "FPToSI"
| UIToFP => "UIToFP"
| SIToFP => "SIToFP"
| FPTrunc => "FPTrunc"
| FPExt => "FPExt"
| PtrToInt => "PtrToInt"
| IntToPtr => "IntToPtr"
| BitCast => "BitCast"
| AddrSpaceCast => "AddrSpaceCast"



| CleanupPad => "CleanupPad"
| CatchPad => "CatchPad"




| ICmp => "ICmp"
| FCmp => "FCmp"
| PHI => "PHI"
| Call => "Call"
| Select => "Select"
| UserOp1 => "UserOp1"
| UserOp2 => "UserOp2"
| VAArg => "VAArg"
| ExtractElement => "ExtractElement"
| InsertElement => "InsertElement"
| ShuffleVector => "ShuffleVector"
| ExtractValue => "ExtractValue"
| InsertValue => "InsertValue"
| LandingPad => "LandingPad"

end Instr

-- | Const type tag
--
-- Note. Constructor names are generated from LLVM files and capitalized
-- according to names in files.
inductive Const : Type


| Function
| GlobalAlias
| GlobalIFunc
| GlobalVariable
| BlockAddress
| ConstantExpr


| ConstantArray
| ConstantStruct
| ConstantVector


| UndefValue
| ConstantAggregateZero
| ConstantDataArray
| ConstantDataVector
| ConstantInt
| ConstantFP
| ConstantPointerNull
| ConstantTokenNone

namespace Const
def asString : Const -> String


| Function => "Function"
| GlobalAlias => "GlobalAlias"
| GlobalIFunc => "GlobalIFunc"
| GlobalVariable => "GlobalVariable"
| BlockAddress => "BlockAddress"
| ConstantExpr => "ConstantExpr"


| ConstantArray => "ConstantArray"
| ConstantStruct => "ConstantStruct"
| ConstantVector => "ConstantVector"


| UndefValue => "UndefValue"
| ConstantAggregateZero => "ConstantAggregateZero"
| ConstantDataArray => "ConstantDataArray"
| ConstantDataVector => "ConstantDataVector"
| ConstantInt => "ConstantInt"
| ConstantFP => "ConstantFP"
| ConstantPointerNull => "ConstantPointerNull"
| ConstantTokenNone => "ConstantTokenNone"

end Const

-- C.F. llvm/IR/InstrTypes.h, enum Predicate
inductive FCmp
| false
| oeq
| ogt
| oge
| olt
| ole
| one
| ord
| uno
| ueq
| ugt
| uge
| ult
| ule
| une
| true

namespace FCmp
def asString : FCmp -> String
| false => "false"
| oeq => "oeq"
| ogt => "ogt"
| oge => "oge"
| olt => "olt"
| ole => "ole"
| one => "one"
| ord => "ord"
| uno => "uno"
| ueq => "ueq"
| ugt => "ugt"
| uge => "uge"
| ult => "ult"
| ule => "ule"
| une => "une"
| true => "true"

end FCmp


-- C.F. llvm/IR/InstrTypes.h, enum Predicate
inductive ICmp
| eq
| ne
| ugt
| uge
| ult
| ule
| sgt
| sge
| slt
| sle

namespace ICmp

def asString : ICmp -> String
| eq => "eq"
| ne => "ne"
| ugt => "ugt"
| uge => "uge"
| ult => "ult"
| ule => "ule"
| sgt => "sgt"
| sge => "sge"
| slt => "slt"
| sle => "sle"

end ICmp

end Code
end LLVM
