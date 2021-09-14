
import Std.Data.RBMap

namespace LLVM
namespace Code

open Std (RBMap)

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
-- according to names in files. C.F. llvm/IR/Instruction.def
inductive Instr : Type
-- Terminators
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
| CallBr
-- Standard unary operators
| FNeg
-- Standard binary operators
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
-- Logical operators
| Shl
| LShr
| AShr
| And
| Or
| Xor
-- Memory instructions
| Alloca
| Load
| Store
| GetElementPtr
| Fence
| AtomicCmpXchg
| AtomicRMW
-- Convert instructions
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
-- Pad instructions
| CleanupPad
| CatchPad
-- Other instructions
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
| Freeze
  deriving Repr

namespace Instr

/-- Names associated with Instr, C.F. llvm::Instruction::getOpcodeName in the C++ source.-/
def opcodeName : Instr → String
  | Ret => "ret"
  | Br => "br"
  | Switch => "switch"
  | IndirectBr => "indirectbr"
  | Invoke => "invoke"
  | Resume => "resume"
  | Unreachable => "unreachable"
  | CleanupRet => "cleanupret"
  | CatchRet => "catchret"
  | CatchPad => "catchpad"
  | CatchSwitch => "catchswitch"
  | CallBr => "callbr"
  | FNeg => "fneg"
  | Add => "add"
  | FAdd => "fadd"
  | Sub => "sub"
  | FSub => "fsub"
  | Mul => "mul"
  | FMul => "fmul"
  | UDiv => "udiv"
  | SDiv => "sdiv"
  | FDiv => "fdiv"
  | URem => "urem"
  | SRem => "srem"
  | FRem => "frem"
  | And => "and"
  | Or => "or"
  | Xor => "xor"
  | Alloca => "alloca"
  | Load => "load"
  | Store => "store"
  | AtomicCmpXchg => "cmpxchg"
  | AtomicRMW => "atomicrmw"
  | Fence => "fence"
  | GetElementPtr => "getelementptr"
  | Trunc => "trunc"
  | ZExt => "zext"
  | SExt => "sext"
  | FPTrunc => "fptrunc"
  | FPExt => "fpext"
  | FPToUI => "fptoui"
  | FPToSI => "fptosi"
  | UIToFP => "uitofp"
  | SIToFP => "sitofp"
  | IntToPtr => "inttoptr"
  | PtrToInt => "ptrtoint"
  | BitCast => "bitcast"
  | AddrSpaceCast => "addrspacecast"
  | ICmp => "icmp"
  | FCmp => "fcmp"
  | PHI => "phi"
  | Select => "select"
  | UserOp1 => "<Invalid operator>" -- May be used internally in a pass
  | UserOp2 => "<Invalid operator>" -- Internal to passes only
  | Call => "call"
  | Shl => "shl"
  | LShr => "lshr"
  | AShr => "ashr"
  | VAArg => "va_arg"
  | ExtractElement => "extractelement"
  | InsertElement => "insertelement"
  | ShuffleVector => "shufflevector"
  | ExtractValue => "extractvalue"
  | InsertValue => "insertvalue"
  | LandingPad => "landingpad"
  | CleanupPad => "cleanuppad"
  | Freeze => "freeze"

private
def opcadeNameMap : RBMap String Instr Ord.compare :=
  RBMap.fromList
    (cmp := Ord.compare)
    [("ret", Ret),
     ("br", Br),
     ("switch", Switch),
     ("indirectbr", IndirectBr),
     ("invoke", Invoke),
     ("resume", Resume),
     ("unreachable", Unreachable),
     ("cleanupret", CleanupRet),
     ("catchret", CatchRet),
     ("catchpad", CatchPad),
     ("catchswitch", CatchSwitch),
     ("callbr", CallBr),
     ("fneg", FNeg),
     ("add", Add),
     ("fadd", FAdd),
     ("sub", Sub),
     ("fsub", FSub),
     ("mul", Mul),
     ("fmul", FMul),
     ("udiv", UDiv),
     ("sdiv", SDiv),
     ("fdiv", FDiv),
     ("urem", URem),
     ("srem", SRem),
     ("frem", FRem),
     ("and", And),
     ("or", Or),
     ("xor", Xor),
     ("alloca", Alloca),
     ("load", Load),
     ("store", Store),
     ("cmpxchg", AtomicCmpXchg),
     ("atomicrmw", AtomicRMW),
     ("fence", Fence),
     ("getelementptr", GetElementPtr),
     ("trunc", Trunc),
     ("zext", ZExt),
     ("sext", SExt),
     ("fptrunc", FPTrunc),
     ("fpext", FPExt),
     ("fptoui", FPToUI),
     ("fptosi", FPToSI),
     ("uitofp", UIToFP),
     ("sitofp", SIToFP),
     ("inttoptr", IntToPtr),
     ("ptrtoint", PtrToInt),
     ("bitcast", BitCast),
     ("addrspacecast", AddrSpaceCast),
     ("icmp", ICmp),
     ("fcmp", FCmp),
     ("phi", PHI),
     ("select", Select),
     ("call", Call),
     ("shl", Shl),
     ("lshr", LShr),
     ("ashr", AShr),
     ("va_arg", VAArg),
     ("extractelement", ExtractElement),
     ("insertelement", InsertElement),
     ("shufflevector", ShuffleVector),
     ("extractvalue", ExtractValue),
     ("insertvalue", InsertValue),
     ("landingpad", LandingPad),
     ("cleanuppad", CleanupPad),
     ("freeze", Freeze)]


def fromOpcodeName (nm : String) : Option Instr :=
  opcadeNameMap.find? nm

def asString : Instr -> String
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
| CallBr => "CallBr"

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
| Freeze => "Freeze"

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
