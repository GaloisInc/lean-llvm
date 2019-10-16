/-
Copyright (c) 2019 Galois, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Dockins, Joe Hendrix

Lean declarations to link against LLVM C++ declarations.
-/

import .llvm_codes

namespace llvm.ffi.

constant Context := Unit
constant Type_ := Unit

constant Value := Unit
def Function := Value
def BasicBlock := Value
def Instruction := Value
def Constant := Value

constant Module := Unit
constant MemoryBuffer := Unit

def Triple := Unit
instance Triple.inhabited : Inhabited Triple := inferInstanceAs (Inhabited Unit)

------------------------------------------------------------------------
-- Context

@[extern 1 "lean_llvm_newContext"]
def newContext : IO Context := default _

------------------------------------------------------------------------
-- Types

@[extern 2 "lean_llvm_getTypeTag"]
def getTypeTag : @& Type_ -> IO llvm.code.type := default _

@[extern 2 "lean_llvm_getTypeName"]
def getTypeName : @& Type_ -> IO (Option String) := default _

@[extern 2 "lean_llvm_typeIsOpaque"]
def typeIsOpaque : @& Type_ -> IO Bool := default _

@[extern 2 "lean_llvm_getIntegerTypeWidth"]
def getIntegerTypeWidth : @& Type_ -> IO Nat := default _

@[extern 2 "lean_llvm_getPointerElementType"]
def getPointerElementType : @& Type_ -> IO (Option Type_) := default _

@[extern 2 "lean_llvm_getSequentialTypeData"]
def getSequentialTypeData : @&Type_ -> IO (Option (Nat × Type_)) := default _

@[extern 2 "lean_llvm_getStructTypeData"]
def getStructTypeData : @&Type_ -> IO (Option (Bool × Array Type_)) := default _

@[extern 2 "lean_llvm_getFunctionTypeData"]
def getFunctionTypeData : @&Type_ -> IO (Option (Type_ × (Array Type_ × Bool))) := default _

@[extern 3 "lean_llvm_newPrimitiveType"]
def newPrimitiveType : @& Context → @& llvm.code.type → IO Type_ := default _

@[extern 3 "lean_llvm_newIntegerType"]
def newIntegerType : @& Context → @& Nat → IO Type_ := default _

@[extern 3 "lean_llvm_newArrayType"]
def newArrayType : @& Nat → @& Type_ → IO Type_ := default _

@[extern 3 "lean_llvm_newVectorType"]
def newVectorType : @& Nat → @& Type_ → IO Type_ := default _

@[extern 2 "lean_llvm_newPointerType"]
def newPointerType : @& Type_ → IO Type_ := default _

@[extern 4 "lean_llvm_newFunctionType"]
def newFunctionType : @& Type_ → @& Array Type_ → Bool → IO Type_ := default _

@[extern 3 "lean_llvm_newLiteralStructType"]
def newLiteralStructType : @& Bool → @& Array Type_ → IO Type_ := default _

@[extern 2 "lean_llvm_newOpaqueStructType"]
def newOpaqueStructType : @& Context → @& String → IO Type_ := default _

@[extern 4 "lean_llvm_setStructTypeBody"]
def setStructTypeBody : @& Type_ → @& Bool → @& Array Type_ → IO Unit := default _

------------------------------------------------------------------------
-- Value

@[extern 2 "lean_llvm_getValueType"]
def getValueType : @& Value -> IO Type_ := default _

inductive value_decomposition
| unknown_value     : value_decomposition
| constant_value    : Constant -> value_decomposition
| argument_value    : Nat -> value_decomposition
| block_value       : BasicBlock -> value_decomposition
| instruction_value : Instruction -> value_decomposition

@[extern 2 "lean_llvm_decomposeValue"]
def decomposeValue : @& Value -> IO value_decomposition := default _

def functionToValue (f:Function)       : Value := f
def basicBlockToValue (bb:BasicBlock)  : Value := bb
def instructionToValue (i:Instruction) : Value := i
def constantToValue (c:Constant)       : Value := c

------------------------------------------------------------------------
-- Constant

@[extern 2 "lean_llvm_getConstantName"]
def getConstantName : @& Constant -> IO (Option String) := default _

@[extern 2 "lean_llvm_getConstantTag"]
def getConstantTag : @&Constant -> IO llvm.code.const := default _

-- return bitwidth and value
@[extern 2 "lean_llvm_getConstIntData"]
def getConstIntData : @& Constant -> IO (Option (Nat × Nat)) := default _

@[extern 2 "lean_llvm_getConstExprData"]
def getConstExprData : @& Constant -> IO (Option (llvm.code.instr × Array Constant)) := default _

------------------------------------------------------------------------
-- Instruction

@[extern 2 "lean_llvm_instructionLt"]
def instructionLt : @& Instruction -> @&Instruction -> Bool := default _

@[extern 2 "lean_llvm_getInstructionName"]
def getInstructionName : @& Instruction -> IO (Option String) := default _

@[extern 2 "lean_llvm_getInstructionType"]
def getInstructionType : @& Instruction -> IO Type_ := default _

@[extern 2 "lean_llvm_getInstructionOpcode"]
def getInstructionOpcode : @& Instruction -> IO llvm.code.instr := default _

@[extern 2 "lean_llvm_getInstructionReturnValue"]
def getInstructionReturnValue : @& Instruction -> IO (Option Value) := default _

@[extern 2 "lean_llvm_getBinaryOperatorValues"]
def getBinaryOperatorValues : @& Instruction -> IO (Option (Value × Value)) := default _

@[extern 2 "lean_llvm_hasNoSignedWrap"]
def hasNoSignedWrap : @& Instruction -> IO Bool := default _

@[extern 2 "lean_llvm_hasNoUnsignedWrap"]
def hasNoUnsignedWrap : @& Instruction -> IO Bool := default _

@[extern 2 "lean_llvm_isExact"]
def isExact : @&Instruction -> IO Bool := default _

@[extern 2 "lean_llvm_getICmpInstData"]
def getICmpInstData : @& Instruction -> IO (Option (llvm.code.icmp × (Value × Value))) := default _

@[extern 2 "lean_llvm_getSelectInstData"]
def getSelectInstData : @& Instruction -> IO (Option (Value × (Value × Value))) := default _


inductive branch_decomposition
| unconditional : BasicBlock → branch_decomposition
| conditional : Value → BasicBlock → BasicBlock → branch_decomposition

@[extern 2 "lean_llvm_getBranchInstData"]
def getBranchInstData : @& Instruction -> IO (Option branch_decomposition) := default _

@[extern 2 "lean_llvm_getPhiData"]
def getPhiData : @& Instruction -> IO (Option (Array (Value × BasicBlock))) := default _

@[extern 2 "lean_llvm_getCastInstData"]
def getCastInstData : @& Instruction -> IO (Option (Nat × Value)) := default _

@[extern 2 "lean_llvm_getAllocaData"]
def getAllocaData : @& Instruction -> IO (Option (Type_ × (Option Value × Option Nat))) := default _

@[extern 2 "lean_llvm_getStoreData"]
def getStoreData : @& Instruction -> IO (Option (Value × (Value × Option Nat))) := default _

@[extern 2 "lean_llvm_getLoadData"]
def getLoadData : @& Instruction -> IO (Option (Value × Option Nat)) := default _

@[extern 2 "lean_llvm_getGEPData"]
def getGEPData : @& Instruction -> IO (Option (Bool × (Value × Array Value))) := default _

@[extern 2 "lean_llvm_getCallInstData"]
def getCallInstData : @& Instruction -> IO (Option (Bool × (Type_ × (Value × Array Value)))) := default _

------------------------------------------------------------------------
-- Basic block

@[extern 2 "lean_llvm_basicBlockLt"]
def basicBlockLt : @& BasicBlock -> @& BasicBlock -> Bool := default _

@[extern 2 "lean_llvm_getBBName"]
def getBBName : @& BasicBlock -> IO (Option String) := default _

@[extern 2 "lean_llvm_getInstructionArray"]
def getInstructionArray : @& BasicBlock -> IO (Array Instruction) := default _

------------------------------------------------------------------------
-- Function

@[extern 3 "lean_llvm_newFunction"]
def newFunction : Module → @&Type_ → @&String → IO Function := default _

@[extern 2 "lean_llvm_getFunctionName"]
def getFunctionName : @& Function -> IO String := default _

@[extern 2 "lean_llvm_getFunctionArgs"]
def getFunctionArgs : @& Function -> IO (Array (Option String × Type_)) := default _

@[extern 2 "lean_llvm_getReturnType"]
def getReturnType : @& Function -> IO Type_ := default _

@[extern 2 "lean_llvm_getBasicBlockArray"]
def getBasicBlockArray : @& Function -> IO (Array BasicBlock) := default _

------------------------------------------------------------------------
-- Module

@[extern 3 "lean_llvm_parseBitcodeFile"]
def parseBitcodeFile : @&MemoryBuffer → Context → IO Module := default _

@[extern 2 "lean_llvm_printModule"]
def printModule : @& Module -> IO Unit := default _

@[extern 3 "lean_llvm_newModule"]
def newModule : Context → @&String → IO Module := default _

@[extern 2 "lean_llvm_getModuleIdentifier"]
def getModuleIdentifier : @&Module → IO String := default _

@[extern 3 "lean_llvm_setModuleIdentifier"]
def setModuleIdentifier : @&Module → @&String → IO Unit := default _

@[extern 2 "lean_llvm_getModuleDataLayoutStr"]
def getModuleDataLayoutStr : @& Module → IO String := default _

@[extern 2 "lean_llvm_getFunctionArray"]
def getFunctionArray : @& Module -> IO (Array Function) := default _

------------------------------------------------------------------------
-- Other

/-- Initialize machine code functions for the current architecture. -/
@[extern 1 "lean_llvm_initNativeFns"]
def initNativeFns : IO Unit := default _

@[extern 2 "lean_llvm_newMemoryBufferFromFile"]
def newMemoryBufferFromFile : String → IO MemoryBuffer := default _

------------------------------------------------------------------------
-- Triple

@[extern "lean_llvm_getProcessTriple"]
def processTriple : Unit → String := default _

/-- This constructs a compiler session and frees it when done. -/
@[extern "lean_llvm_newTriple"]
constant newTriple : String → Triple := default _

end llvm.ffi.
