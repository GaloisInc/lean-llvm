/-
Copyright (c) 2019 Galois, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Dockins, Joe Hendrix

Lean declarations to link against LLVM C++ declarations.
-/

constant LLVMContext := Unit
constant MemoryBuffer := Unit
constant Module := Unit
constant LLVMFunction := Unit
constant LLVMType := Unit
constant BasicBlock := Unit
constant Instruction := Unit
constant LLVMValue := Unit
constant LLVMConstant := Unit

inductive value_decomposition
| unknown_value  : value_decomposition
| argument_value : Nat -> value_decomposition
| instruction_value : Instruction -> value_decomposition
| constant_value : LLVMConstant -> value_decomposition
.

inductive branch_decomposition
| unconditional : BasicBlock → branch_decomposition
| conditional : LLVMValue → BasicBlock → BasicBlock → branch_decomposition.

/-- This constructs a LLVM Context and frees it when done. -/
@[extern 1 cpp "lean_llvm::newLLVMContext"]
constant newLLVMContext : IO LLVMContext := default _

@[extern 2 cpp "lean_llvm::newMemoryBufferFromFile"]
def newMemoryBufferFromFile : String → IO MemoryBuffer := default _

@[extern 3 cpp "lean_llvm::parseBitcodeFile"]
def parseBitcodeFile : MemoryBuffer → LLVMContext → IO Module := default _

@[extern 2 cpp "lean_llvm::getModuleIdentifier"]
def getModuleIdentifier : @& Module → IO String := default _

@[extern 3 cpp "lean_llvm::setModuleIdentifier"]
def setModuleIdentifier : @& Module → String → IO Unit := default _

@[extern 2 cpp "lean_llvm::getModuleDataLayoutStr"]
def getModuleDataLayoutStr : @& Module → IO String := default _

@[extern 1 cpp "lean_llvm::mkSomeList"]
def mkSomeList : @& Nat → List Nat := default _

@[extern 2 cpp "lean_llvm::getFunctionArray"]
def getFunctionArray : @& Module -> IO (Array LLVMFunction) := default _

@[extern 2 cpp "lean_llvm::getFunctionName"]
def getFunctionName : @& LLVMFunction -> IO String := default _

@[extern 2 cpp "lean_llvm::getReturnType"]
def getReturnType : @& LLVMFunction -> IO LLVMType := default _

@[extern 2 cpp "lean_llvm::getFunctionArgs"]
def getFunctionArgs : @& LLVMFunction -> IO (Array (Option String × LLVMType)) := default _

@[extern 2 cpp "lean_llvm::getBasicBlockArray"]
def getBasicBlockArray : @& LLVMFunction -> IO (Array BasicBlock) := default _

@[extern 2 cpp "lean_llvm::getBBName"]
def getBBName : @& BasicBlock -> IO (Option String) := default _

@[extern 2 cpp "lean_llvm::getTypeTag"]
def getTypeTag : @& LLVMType -> IO Nat := default _

@[extern 2 cpp "lean_llvm::getIntegerTypeWidth"]
def getIntegerTypeWidth : @& LLVMType -> IO Nat := default _

@[extern 2 cpp "lean_llvm::getPointerElementType"]
def getPointerElementType : @& LLVMType -> IO (Option LLVMType) := default _

@[extern 2 cpp "lean_llvm::getInstructionArray"]
def getInstructionArray : @& BasicBlock -> IO (Array Instruction) := default _

@[extern 2 cpp "lean_llvm::instructionLt"]
def instructionLt : @& Instruction -> @&Instruction -> Bool := default _

@[extern 2 cpp "lean_llvm::basicBlockLt"]
def basicBlockLt : @& BasicBlock -> @& BasicBlock -> Bool := default _

@[extern 2 cpp "lean_llvm::getInstructionName"]
def getInstructionName : @& Instruction -> IO (Option String) := default _

@[extern 2 cpp "lean_llvm::getInstructionType"]
def getInstructionType : @& Instruction -> IO LLVMType := default _

@[extern 2 cpp "lean_llvm::getInstructionOpcode"]
def getInstructionOpcode : @& Instruction -> IO Nat := default _

@[extern 2 cpp "lean_llvm::getInstructionReturnValue"]
def getInstructionReturnValue : @& Instruction -> IO (Option LLVMValue) := default _

@[extern 2 cpp "lean_llvm::getValueType"]
def getValueType : @& LLVMValue -> IO LLVMType := default _

@[extern 2 cpp "lean_llvm::getBinaryOperatorValues"]
def getBinaryOperatorValues : @& Instruction -> IO (Option (LLVMValue × LLVMValue)) := default _

@[extern 2 cpp "lean_llvm::hasNoSignedWrap"]
def hasNoSignedWrap : @& Instruction -> IO Bool := default _

@[extern 2 cpp "lean_llvm::hasNoUnsignedWrap"]
def hasNoUnsignedWrap : @& Instruction -> IO Bool := default _

@[extern 2 cpp "lean_llvm::isExact"]
def isExact : @& Instruction -> IO Bool := default _

@[extern 2 cpp "lean_llvm::decomposeValue"]
def decomposeValue : @& LLVMValue -> IO value_decomposition := default _

@[extern 2 cpp "lean_llvm::getCmpInstData"]
def getCmpInstData : @& Instruction -> IO (Option (Nat × (LLVMValue × LLVMValue))) := default _

@[extern 2 cpp "lean_llvm::getSelectInstData"]
def getSelectInstData : @& Instruction -> IO (Option (LLVMValue × (LLVMValue × LLVMValue))) := default _

-- return bitwidth and value
@[extern 2 cpp "lean_llvm::getConstIntData"]
def getConstIntData : @& LLVMConstant -> IO (Option (Nat × Nat)) := default _

@[extern 2 cpp "lean_llvm::getBranchInstData"]
def getBranchInstData : @& Instruction -> IO (Option branch_decomposition) := default _

@[extern 2 cpp "lean_llvm::getPhiData"]
def getPhiData : @& Instruction -> IO (Option (Array (LLVMValue × BasicBlock))) := default _

@[extern 2 cpp "lean_llvm::getCastInstData"]
def getCastInstData : @& Instruction -> IO (Option (Nat × LLVMValue)) := default _

@[extern 2 cpp "lean_llvm::getAllocaData"]
def getAllocaData : @& Instruction -> IO (Option (LLVMType × (Option LLVMValue × Option Nat))) := default _

@[extern 2 cpp "lean_llvm::getStoreData"]
def getStoreData : @& Instruction -> IO (Option (LLVMValue × (LLVMValue × Option Nat))) := default _

@[extern 2 cpp "lean_llvm::getLoadData"]
def getLoadData : @& Instruction -> IO (Option (LLVMValue × Option Nat)) := default _
