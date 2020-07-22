/-
Copyright (c) 2019 Galois, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Dockins, Joe Hendrix

Lean declarations to link against LLVM C++ declarations.
-/

import Init.Core
import LeanLLVM.LLVMCodes

namespace LLVM
namespace FFI

constant Context := Unit
constant Type_ := Unit

constant Value := Unit
def Function := Value
def BasicBlock := Value
def Instruction := Value
def Constant := Value
def GlobalVar := Value

constant Module := Unit
constant MemoryBuffer := Unit

def Triple := Unit
instance Triple.inhabited : Inhabited Triple := inferInstanceAs (Inhabited Unit)

------------------------------------------------------------------------
-- Context

@[extern 1 "lean_llvm_newContext"]
def newContext : IO Context := arbitrary _

------------------------------------------------------------------------
-- Types

@[extern 2 "lean_llvm_getTypeTag"]
def getTypeTag : @& Type_ -> IO Code.TypeID := arbitrary _

@[extern 2 "lean_llvm_getTypeName"]
def getTypeName : @& Type_ -> IO (Option String) := arbitrary _

@[extern 2 "lean_llvm_typeIsOpaque"]
def typeIsOpaque : @& Type_ -> IO Bool := arbitrary _

@[extern 2 "lean_llvm_getIntegerTypeWidth"]
def getIntegerTypeWidth : @& Type_ -> IO Nat := arbitrary _

@[extern 2 "lean_llvm_getPointerElementType"]
def getPointerElementType : @& Type_ -> IO (Option Type_) := arbitrary _

@[extern 2 "lean_llvm_getSequentialTypeData"]
def getSequentialTypeData : @&Type_ -> IO (Option (Nat × Type_)) := arbitrary _

@[extern 2 "lean_llvm_getStructTypeData"]
def getStructTypeData : @&Type_ -> IO (Option (Bool × Array Type_)) := arbitrary _

@[extern 2 "lean_llvm_getFunctionTypeData"]
def getFunctionTypeData : @&Type_ -> IO (Option (Type_ × (Array Type_ × Bool))) := arbitrary _

@[extern 3 "lean_llvm_newPrimitiveType"]
def newPrimitiveType : @& Context → @& Code.TypeID → IO Type_ := arbitrary _

@[extern 3 "lean_llvm_newIntegerType"]
def newIntegerType : @& Context → @& Nat → IO Type_ := arbitrary _

@[extern 3 "lean_llvm_newArrayType"]
def newArrayType : @& Nat → @& Type_ → IO Type_ := arbitrary _

@[extern 3 "lean_llvm_newVectorType"]
def newVectorType : @& Nat → @& Type_ → IO Type_ := arbitrary _

@[extern 2 "lean_llvm_newPointerType"]
def newPointerType : @& Type_ → IO Type_ := arbitrary _

@[extern 4 "lean_llvm_newFunctionType"]
def newFunctionType : @& Type_ → @& Array Type_ → Bool → IO Type_ := arbitrary _

@[extern 3 "lean_llvm_newLiteralStructType"]
def newLiteralStructType : @& Bool → @& Array Type_ → IO Type_ := arbitrary _

@[extern 2 "lean_llvm_newOpaqueStructType"]
def newOpaqueStructType : @& Context → @& String → IO Type_ := arbitrary _

@[extern 4 "lean_llvm_setStructTypeBody"]
def setStructTypeBody : @& Type_ → @& Bool → @& Array Type_ → IO Unit := arbitrary _

------------------------------------------------------------------------
-- Value

@[extern 2 "lean_llvm_getValueType"]
def getValueType : @& Value -> IO Type_ := arbitrary _

inductive ValueView
| unknown
| constantView (c:Constant)
| argument (a:Nat)
| block (b:BasicBlock)
| instruction (i:Instruction)

@[extern 2 "lean_llvm_decomposeValue"]
def decomposeValue : @& Value -> IO ValueView := arbitrary _

def functionToValue (f:Function)       : Value := f
def basicBlockToValue (bb:BasicBlock)  : Value := bb
def instructionToValue (i:Instruction) : Value := i
def constantToValue (c:Constant)       : Value := c

------------------------------------------------------------------------
-- Constant

@[extern 2 "lean_llvm_getConstantName"]
def getConstantName : @& Constant -> IO (Option String) := arbitrary _

@[extern 2 "lean_llvm_getConstantTag"]
def getConstantTag : @&Constant -> IO Code.Const := arbitrary _

-- return bitwidth and value
@[extern 2 "lean_llvm_getConstIntData"]
def getConstIntData : @& Constant -> IO (Option (Nat × Nat)) := arbitrary _

@[extern 2 "lean_llvm_getConstExprData"]
def getConstExprData : @& Constant -> IO (Option (Code.Instr × Array Constant)) := arbitrary _

@[extern 2 "lean_llvm_getConstArrayData"]
def getConstArrayData : @& Constant -> IO (Option (Type_ × Array Constant)) := arbitrary _

------------------------------------------------------------------------
-- Instruction

@[extern 2 "lean_llvm_instructionLt"]
def instructionLt : @& Instruction -> @&Instruction -> Bool := arbitrary _

@[extern 2 "lean_llvm_getInstructionName"]
def getInstructionName : @& Instruction -> IO (Option String) := arbitrary _

@[extern 2 "lean_llvm_getInstructionType"]
def getInstructionType : @& Instruction -> IO Type_ := arbitrary _

@[extern 2 "lean_llvm_getInstructionOpcode"]
def getInstructionOpcode : @& Instruction -> IO Code.Instr := arbitrary _

@[extern 2 "lean_llvm_getInstructionReturnValue"]
def getInstructionReturnValue : @& Instruction -> IO (Option Value) := arbitrary _

@[extern 2 "lean_llvm_getBinaryOperatorValues"]
def getBinaryOperatorValues : @& Instruction -> IO (Option (Value × Value)) := arbitrary _

@[extern 2 "lean_llvm_hasNoSignedWrap"]
def hasNoSignedWrap : @& Instruction -> IO Bool := arbitrary _

@[extern 2 "lean_llvm_hasNoUnsignedWrap"]
def hasNoUnsignedWrap : @& Instruction -> IO Bool := arbitrary _

@[extern 2 "lean_llvm_isExact"]
def isExact : @&Instruction -> IO Bool := arbitrary _

@[extern 2 "lean_llvm_getICmpInstData"]
def getICmpInstData : @& Instruction -> IO (Option (Code.ICmp × (Value × Value))) := arbitrary _

@[extern 2 "lean_llvm_getSelectInstData"]
def getSelectInstData : @& Instruction -> IO (Option (Value × (Value × Value))) := arbitrary _

inductive BranchView
| unconditional (b:BasicBlock)
| conditional (c:Value) (t f : BasicBlock)

@[extern 2 "lean_llvm_getBranchInstData"]
def getBranchInstData : @& Instruction -> IO (Option BranchView) := arbitrary _

@[extern 2 "lean_llvm_getPhiData"]
def getPhiData : @& Instruction -> IO (Option (Array (Value × BasicBlock))) := arbitrary _

@[extern 2 "lean_llvm_getCastInstData"]
def getCastInstData : @& Instruction -> IO (Option (Nat × Value)) := arbitrary _

@[extern 2 "lean_llvm_getAllocaData"]
def getAllocaData : @& Instruction -> IO (Option (Type_ × (Option Value × Option Nat))) := arbitrary _

@[extern 2 "lean_llvm_getStoreData"]
def getStoreData : @& Instruction -> IO (Option (Value × (Value × Option Nat))) := arbitrary _

@[extern 2 "lean_llvm_getLoadData"]
def getLoadData : @& Instruction -> IO (Option (Value × Option Nat)) := arbitrary _

@[extern 2 "lean_llvm_getGEPData"]
def getGEPData : @& Instruction -> IO (Option (Bool × (Value × Array Value))) := arbitrary _

@[extern 2 "lean_llvm_getCallInstData"]
def getCallInstData : @& Instruction -> IO (Option (Bool × (Type_ × (Value × Array Value)))) := arbitrary _

------------------------------------------------------------------------
-- Basic block

@[extern 2 "lean_llvm_basicBlockLt"]
def basicBlockLt : @& BasicBlock -> @& BasicBlock -> Bool := arbitrary _

@[extern 2 "lean_llvm_getBBName"]
def getBBName : @& BasicBlock -> IO (Option String) := arbitrary _

@[extern 2 "lean_llvm_getInstructionArray"]
def getInstructionArray : @& BasicBlock -> IO (Array Instruction) := arbitrary _

------------------------------------------------------------------------
-- Function

@[extern 3 "lean_llvm_newFunction"]
def newFunction : Module → @&Type_ → @&String → IO Function := arbitrary _

@[extern 2 "lean_llvm_getFunctionName"]
def getFunctionName : @& Function -> IO String := arbitrary _

@[extern 2 "lean_llvm_getFunctionArgs"]
def getFunctionArgs : @& Function -> IO (Array (Option String × Type_)) := arbitrary _

@[extern 2 "lean_llvm_getReturnType"]
def getReturnType : @& Function -> IO Type_ := arbitrary _

@[extern 2 "lean_llvm_getBasicBlockArray"]
def getBasicBlockArray : @& Function -> IO (Array BasicBlock) := arbitrary _

------------------------------------------------------------------------
-- GlobalVar

@[extern 2 "lean_llvm_getGlobalVarData"]
def getGlobalVarData : @& GlobalVar → IO (Option (String × (Option Value × Nat))) := arbitrary _


------------------------------------------------------------------------
-- File Parsing

namespace Prim
-- The non-"Prim" versions of these functions appear in `Load.lean`

@[extern 3 "lean_llvm_parseBitcodeFile"]
def parseBitcodeFile : @&MemoryBuffer → Context → IO Module := arbitrary _

@[extern 4 "lean_llvm_parseAssembly"]
def parseAssembly :
@&MemoryBuffer
→ Context
 → String -- ^ data layout string
 → IO Module := arbitrary _

end Prim



------------------------------------------------------------------------
-- Module

@[extern 2 "lean_llvm_printModule"]
def printModule : @& Module -> IO Unit := arbitrary _

@[extern 3 "lean_llvm_newModule"]
def newModule : Context → @&String → IO Module := arbitrary _

@[extern 2 "lean_llvm_getModuleIdentifier"]
def getModuleIdentifier : @&Module → IO String := arbitrary _

@[extern 3 "lean_llvm_setModuleIdentifier"]
def setModuleIdentifier : @&Module → @&String → IO Unit := arbitrary _

@[extern 2 "lean_llvm_getModuleDataLayoutStr"]
def getModuleDataLayoutStr : @& Module → IO String := arbitrary _

@[extern 2 "lean_llvm_getFunctionArray"]
def getFunctionArray : @& Module -> IO (Array Function) := arbitrary _

@[extern 2 "lean_llvm_getGlobalArray"]
def getGlobalArray : @& Module -> IO (Array GlobalVar) := arbitrary _

------------------------------------------------------------------------
-- Other

/-- Initialize machine code functions for the current architecture. -/
@[extern 1 "lean_llvm_initNativeFns"]
def initNativeFns : IO Unit := arbitrary _

@[extern 2 "lean_llvm_newMemoryBufferFromFile"]
def newMemoryBufferFromFile : String → IO MemoryBuffer := arbitrary _

------------------------------------------------------------------------
-- Triple

@[extern "lean_llvm_getProcessTriple"]
def processTriple : Unit → String := arbitrary _

/-- This constructs a compiler session and frees it when done. -/
@[extern "lean_llvm_newTriple"]
constant newTriple : String → Triple := arbitrary _

end FFI
end LLVM
