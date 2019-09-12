/-
Copyright (c) 2019 Galois, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Dockins, Joe Hendrix

Lean declarations to link against LLVM C++ declarations.
-/

import .llvm_codes


/- A LLVM context.
   TODO: mark opaque -/
def LLVMContext := Unit

instance LLVMContext.inhabited : Inhabited LLVMContext := inferInstanceAs (Inhabited Unit)

/-- This constructs a LLVM Context and frees it when done. -/
@[extern 1 "lean_llvm_newLLVMContext"]
def newLLVMContext : IO LLVMContext := default _


------------------------------------------------------------------------
-- Types

constant LLVMType := Unit

------------------------------------------------------------------------
-- Basic block

constant BasicBlock := Unit

@[extern 2 "lean_llvm_getBBName"]
def getBBName : @& BasicBlock -> IO (Option String) := default _

------------------------------------------------------------------------
-- Function

constant LLVMFunction := Unit

@[extern 2 "lean_llvm_getFunctionName"]
def getFunctionName : @& LLVMFunction -> IO String := default _

@[extern 2 "lean_llvm_getFunctionArgs"]
def getFunctionArgs : @& LLVMFunction -> IO (Array (Option String × LLVMType)) := default _

@[extern 2 "lean_llvm_getReturnType"]
def getReturnType : @& LLVMFunction -> IO LLVMType := default _

@[extern 2 "lean_llvm_getBasicBlockArray"]
def getBasicBlockArray : @& LLVMFunction -> IO (Array BasicBlock) := default _

------------------------------------------------------------------------
-- Other

/-- Initialize machine code functions for the current architecture. -/
@[extern 1 "lean_llvm_initNativeFns"]
def initNativeFns : IO Unit := default _

constant MemoryBuffer := Unit

@[extern 2 "lean_llvm_newMemoryBufferFromFile"]
def newMemoryBufferFromFile : String → IO MemoryBuffer := default _

constant Instruction := Unit
constant LLVMValue := Unit
constant LLVMConstant := Unit

constant Module := Unit

@[extern 3 "lean_llvm_parseBitcodeFile"]
def parseBitcodeFile : @&MemoryBuffer → LLVMContext → IO Module := default _

@[extern 3 "lean_llvm_newModule"]
def newModule : LLVMContext → @&String → IO Module := default _

@[extern 2 "lean_llvm_printModule"]
def printModule : @& Module -> IO Unit := default _

@[extern 2 "lean_llvm_getModuleIdentifier"]
def getModuleIdentifier : @&Module → IO String := default _

@[extern 3 "lean_llvm_setModuleIdentifier"]
def setModuleIdentifier : @&Module → @&String → IO Unit := default _

@[extern 2 "lean_llvm_getModuleDataLayoutStr"]
def getModuleDataLayoutStr : @& Module → IO String := default _

@[extern 2 "lean_llvm_getFunctionArray"]
def getFunctionArray : @& Module -> IO (Array LLVMFunction) := default _

@[extern 2 "lean_llvm_getTypeTag"]
def getTypeTag : @& LLVMType -> IO llvm.code.type := default _

@[extern 2 "lean_llvm_getTypeName"]
def getTypeName : @& LLVMType -> IO (Option String) := default _

@[extern 2 "lean_llvm_typeIsOpaque"]
def typeIsOpaque : @& LLVMType -> IO Bool := default _

@[extern 2 "lean_llvm_getIntegerTypeWidth"]
def getIntegerTypeWidth : @& LLVMType -> IO Nat := default _

@[extern 2 "lean_llvm_getPointerElementType"]
def getPointerElementType : @& LLVMType -> IO (Option LLVMType) := default _

@[extern 2 "lean_llvm_getSequentialTypeData"]
def getSequentialTypeData : @&LLVMType -> IO (Option (Nat × LLVMType)) := default _

@[extern 2 "lean_llvm_getStructTypeData"]
def getStructTypeData : @&LLVMType -> IO (Option (Bool × Array LLVMType)) := default _

@[extern 2 "lean_llvm_getFunctionTypeData"]
def getFunctionTypeData : @&LLVMType -> IO (Option (LLVMType × (Array LLVMType × Bool))) := default _

@[extern 2 "lean_llvm_getInstructionArray"]
def getInstructionArray : @& BasicBlock -> IO (Array Instruction) := default _

@[extern 2 "lean_llvm_instructionLt"]
def instructionLt : @& Instruction -> @&Instruction -> Bool := default _

@[extern 2 "lean_llvm_basicBlockLt"]
def basicBlockLt : @& BasicBlock -> @& BasicBlock -> Bool := default _

@[extern 2 "lean_llvm_getInstructionName"]
def getInstructionName : @& Instruction -> IO (Option String) := default _

@[extern 2 "lean_llvm_getConstantName"]
def getConstantName : @& LLVMConstant -> IO (Option String) := default _

@[extern 2 "lean_llvm_getInstructionType"]
def getInstructionType : @& Instruction -> IO LLVMType := default _

@[extern 2 "lean_llvm_getInstructionOpcode"]
def getInstructionOpcode : @& Instruction -> IO llvm.code.instr := default _

@[extern 2 "lean_llvm_getInstructionReturnValue"]
def getInstructionReturnValue : @& Instruction -> IO (Option LLVMValue) := default _

@[extern 2 "lean_llvm_getValueType"]
def getValueType : @& LLVMValue -> IO LLVMType := default _

@[extern 2 "lean_llvm_getBinaryOperatorValues"]
def getBinaryOperatorValues : @& Instruction -> IO (Option (LLVMValue × LLVMValue)) := default _

@[extern 2 "lean_llvm_hasNoSignedWrap"]
def hasNoSignedWrap : @& Instruction -> IO Bool := default _

@[extern 2 "lean_llvm_hasNoUnsignedWrap"]
def hasNoUnsignedWrap : @& Instruction -> IO Bool := default _

@[extern 2 "lean_llvm_isExact"]
def isExact : @&Instruction -> IO Bool := default _

@[extern 2 "lean_llvm_getConstantTag"]
def getConstantTag : @&LLVMConstant -> IO llvm.code.const := default _

inductive value_decomposition
| unknown_value  : value_decomposition
| constant_value : LLVMConstant -> value_decomposition
| argument_value : Nat -> value_decomposition
| block_value : BasicBlock -> value_decomposition
| instruction_value : Instruction -> value_decomposition

@[extern 2 "lean_llvm_decomposeValue"]
def decomposeValue : @& LLVMValue -> IO value_decomposition := default _

@[extern 2 "lean_llvm_getICmpInstData"]
def getICmpInstData : @& Instruction -> IO (Option (llvm.code.icmp × (LLVMValue × LLVMValue))) := default _

@[extern 2 "lean_llvm_getSelectInstData"]
def getSelectInstData : @& Instruction -> IO (Option (LLVMValue × (LLVMValue × LLVMValue))) := default _

-- return bitwidth and value
@[extern 2 "lean_llvm_getConstIntData"]
def getConstIntData : @& LLVMConstant -> IO (Option (Nat × Nat)) := default _

inductive branch_decomposition
| unconditional : BasicBlock → branch_decomposition
| conditional : LLVMValue → BasicBlock → BasicBlock → branch_decomposition

@[extern 2 "lean_llvm_getBranchInstData"]
def getBranchInstData : @& Instruction -> IO (Option branch_decomposition) := default _

@[extern 2 "lean_llvm_getPhiData"]
def getPhiData : @& Instruction -> IO (Option (Array (LLVMValue × BasicBlock))) := default _

@[extern 2 "lean_llvm_getCastInstData"]
def getCastInstData : @& Instruction -> IO (Option (Nat × LLVMValue)) := default _

@[extern 2 "lean_llvm_getAllocaData"]
def getAllocaData : @& Instruction -> IO (Option (LLVMType × (Option LLVMValue × Option Nat))) := default _

@[extern 2 "lean_llvm_getStoreData"]
def getStoreData : @& Instruction -> IO (Option (LLVMValue × (LLVMValue × Option Nat))) := default _

@[extern 2 "lean_llvm_getLoadData"]
def getLoadData : @& Instruction -> IO (Option (LLVMValue × Option Nat)) := default _

@[extern 2 "lean_llvm_getGEPData"]
def getGEPData : @& Instruction -> IO (Option (Bool × (LLVMValue × Array LLVMValue))) := default _

@[extern 2 "lean_llvm_getCallInstData"]
def getCallInstData : @& Instruction -> IO (Option (Bool × (LLVMType × (LLVMValue × Array LLVMValue)))) := default _

------------------------------------------------------------------------
-- Triple

@[extern "lean_llvm_getProcessTriple"]
def processTriple : Unit → String := default _

def Triple := Unit

instance Triple.inhabited : Inhabited Triple := inferInstanceAs (Inhabited Unit)

/-- This constructs a compiler session and frees it when done. -/
@[extern "lean_llvm_newTriple"]
constant newTriple : String → Triple := default _
