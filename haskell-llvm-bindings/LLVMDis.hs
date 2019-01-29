{-# LANGUAGE CPP #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE PatternSynonyms #-}
module Main where

import Control.Exception (bracket)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Foreign (Ptr, alloca, peek, nullPtr, peekArray, allocaArray)
import Foreign.C (CString, withCStringLen, CSize(..), CInt(..), CUInt(..)
                 , peekCString, peekCStringLen, withCString)
import Control.Monad
import System.IO


------------------------------------------------------------------------
-- Common definitions

type LLVMBool = CInt

foreign import ccall unsafe "LLVMDisposeMessage" disposeMessage :: CString -> IO ()

------------------------------------------------------------------------
-- Utilities

getNameWithLength :: (Ptr CSize -> IO CString) -> IO String
getNameWithLength f = do
  alloca $ \szPtr -> do
    ptr <- f szPtr
    sz <- peek szPtr
    peekCStringLen (ptr, fromIntegral sz)

------------------------------------------------------------------------
-- Memory buffers

data OpaqueMemoryBuffer

type MemoryBufferRef = Ptr OpaqueMemoryBuffer

foreign import ccall unsafe "LLVMCreateMemoryBufferWithContentsOfFile"
  createMemoryBufferWithContentsOfFile :: CString
                                       -> Ptr MemoryBufferRef
                                       -> Ptr CString
                                       -> IO LLVMBool


foreign import ccall unsafe "LLVMDisposeMemoryBuffer"
  disposeMemoryBuffer :: MemoryBufferRef -> IO ()

-- | This reads from the given filename, and provides either an error message
-- or buffer to the action.
withMemoryBufferFromFile :: String
                         -> (Either String MemoryBufferRef -> IO a)
                         -> IO a
withMemoryBufferFromFile path act =
  withCString path $ \cpath ->
    alloca $ \bufPtr ->
      alloca $ \errPtr -> do
        res <- createMemoryBufferWithContentsOfFile cpath bufPtr errPtr
        if res == 0 then
          bracket (peek bufPtr) disposeMemoryBuffer (act . Right)
        else
          bracket (peek errPtr) disposeMessage $ \err ->
             act . Left =<< peekCString err

------------------------------------------------------------------------
-- Context

data OpaqueContextRef

type ContextRef = Ptr OpaqueContextRef

foreign import ccall unsafe "LLVMContextCreate"
  llvmContextCreate :: IO ContextRef

foreign import ccall unsafe "LLVMContextDispose"
  llvmContextDispose :: ContextRef -> IO ()

-- | Run code with an LLVM context before freeing it.
withLLVMContext :: (ContextRef -> IO a) -> IO a
withLLVMContext = bracket llvmContextCreate llvmContextDispose

------------------------------------------------------------------------
-- TypeKind

-- | Enum for
newtype TypeKind = TypeKind CInt


------------------------------------------------------------------------
-- Types

data OpaqueType

type TypeRef = Ptr OpaqueType

------------------------------------------------------------------------
-- Values

data OpaqueValue

type ValueRef = Ptr OpaqueValue

foreign import ccall unsafe "LLVMGetValueName2"
 getValueName2 :: ValueRef -> Ptr CSize -> IO CString

getValueName :: ValueRef -> IO String
getValueName r = getNameWithLength (getValueName2 r)

foreign import ccall unsafe "LLVMTypeOf" typeOf :: ValueRef -> IO TypeRef

-- Dump a representation of a value to stderr.
foreign import ccall unsafe "LLVMDumpValue"
  dumpValue :: ValueRef -> IO ()


foreign import ccall unsafe "LLVMPrintValueToString"
  ffiPrintValueToString :: ValueRef -> IO CString

printValueToString :: ValueRef -> IO String
printValueToString ref = bracket (ffiPrintValueToString ref) disposeMessage peekCString


foreign import ccall unsafe "LLVMGetNumOperands"
  getNumOperands :: ValueRef -> CInt

foreign import ccall unsafe "LLVMGetOperand"
  getOperand :: ValueRef -> CUInt -> ValueRef

------------------------------------------------------------------------
-- Opcode

newtype Opcode = Opcode CInt

pattern LLVMRet :: Opcode
pattern LLVMRet = Opcode 1

pattern LLVMBr :: Opcode
pattern LLVMBr = Opcode 2

opcodeNames :: [(String, CInt)]
opcodeNames =
  [ (,) "Ret" 1
  , (,) "Br"  2
  , (,) "Switch" 3
  , (,) "IndirectBr" 4
  , (,) "Invoke" 5
  -- removed 6 due to API changes
  , (,) "Unreachable" 7

  -- Standard Binary Operators
  , (,) "Add" 8
  , (,) "FAdd" 9
  , (,) "Sub" 10
  , (,) "FSub" 11
  , (,) "Mul" 12
  , (,) "FMul" 13
  , (,) "UDiv" 14
  , (,) "SDiv" 15
  , (,) "FDiv" 16
  , (,) "URem" 17
  , (,) "SRem" 18
  , (,) "FRem" 19

  -- Logical Operators
  , (,) "Shl" 20
  , (,) "LShr" 21
  , (,) "AShr" 22
  , (,) "And" 23
  , (,) "Or" 24
  , (,) "Xor" 25

  -- Memory Operators
  , (,) "Alloca" 26
  , (,) "Load" 27
  , (,) "Store" 28
  , (,) "GetElementPtr" 29

  -- Cast Operators
  , (,) "Trunc" 30
  , (,) "ZExt" 31
  , (,) "SExt" 32
  , (,) "FPToUI" 33
  , (,) "FPToSI" 34
  , (,) "UIToFP" 35
  , (,) "SIToFP" 36
  , (,) "FPTrunc" 37
  , (,) "FPExt" 38
  , (,) "PtrToInt" 39
  , (,) "IntToPtr" 40
  , (,) "BitCast" 41
  , (,) "AddrSpaceCast" 60

  -- Other Operators
  , (,) "ICmp" 42
  , (,) "FCmp" 43
  , (,) "PHI" 44
  , (,) "Call" 45
  , (,) "Select" 46
  , (,) "UserOp1" 47
  , (,) "UserOp2" 48
  , (,) "VAArg" 49
  , (,) "ExtractElement" 50
  , (,) "InsertElement" 51
  , (,) "ShuffleVector" 52
  , (,) "ExtractValue" 53
  , (,) "InsertValue" 54

  -- Atomic operators
  , (,) "Fence" 55
  , (,) "AtomicCmpXchg" 56
  , (,) "AtomicRMW" 57

  -- Exception Handling Operators
  , (,) "Resume" 58
  , (,) "LandingPad" 59
  , (,) "CleanupRet" 61
  , (,) "CatchRet" 62
  , (,) "CatchPad" 63
  , (,) "CleanupPad" 64
  , (,) "CatchSwitch" 65
  ]

opcodeNameMap :: Map CInt String
opcodeNameMap = Map.fromList [ (i, "LLVM" ++ nm) | (nm,i) <- opcodeNames ]

instance Show Opcode where
  show (Opcode i) =
    case Map.lookup i opcodeNameMap of
      Nothing -> "(Opcode " ++ show i ++ ")"
      Just nm -> nm

------------------------------------------------------------------------
-- Instructions

foreign import ccall unsafe "LLVMGetInstructionOpcode"
  getInstructionOpcode :: ValueRef -> Opcode

------------------------------------------------------------------------
-- Globals

foreign import ccall unsafe "LLVMIsDeclaration"
 ffiIsDeclaration :: ValueRef -> IO LLVMBool

isDeclaration :: ValueRef -> IO Bool
isDeclaration r = (/= 0) <$> ffiIsDeclaration r


------------------------------------------------------------------------
-- Functions

data OpaqueBasicBlock

type BasicBlockRef = Ptr OpaqueBasicBlock

foreign import ccall unsafe "LLVMCountBasicBlocks"
  countBasicBlocks :: ValueRef -> IO CUInt

foreign import ccall unsafe "LLVMGetBasicBlocks"
  ffiGetBasicBlocks :: ValueRef -> Ptr BasicBlockRef -> IO ()

getBasicBlocks :: ValueRef -> IO [BasicBlockRef]
getBasicBlocks ref = do
  cnt <- countBasicBlocks ref
  allocaArray (fromIntegral cnt) $ \ptr -> do
    ffiGetBasicBlocks ref ptr
    peekArray (fromIntegral cnt) ptr


foreign import ccall unsafe "LLVMGetBasicBlockName"
  ffiGetBasicBlockName :: BasicBlockRef -> IO CString

--  Return the name of the block
getBasicBlockName :: BasicBlockRef -> IO String
getBasicBlockName ref = peekCString =<< ffiGetBasicBlockName ref

foreign import ccall unsafe "LLVMGetFirstInstruction"
  getFirstInstruction :: BasicBlockRef -> IO ValueRef

foreign import ccall unsafe "LLVMGetLastInstruction"
  getLastInstruction :: BasicBlockRef -> IO ValueRef

foreign import ccall unsafe "LLVMGetNextInstruction"
  getNextInstruction :: ValueRef -> IO ValueRef

foreign import ccall unsafe "LLVMGetPreviousInstruction"
  getPreviousInstruction :: ValueRef -> IO ValueRef

-- Get list of instructions from block.
getInstructions :: BasicBlockRef -> IO [ValueRef]
getInstructions r = getLastInstruction r >>= go []
  where go :: [ValueRef] -> ValueRef -> IO [ValueRef]
        go l vr
          | vr == nullPtr = pure l
          | otherwise = getPreviousInstruction vr >>= go (vr:l)

------------------------------------------------------------------------
-- Modules

data OpaqueModule

type ModuleRef = Ptr OpaqueModule

foreign import ccall unsafe "LLVMDisposeModule"
  disposeModule ::  ModuleRef -> IO ()

foreign import ccall unsafe "LLVMGetModuleIdentifier"
  ffiGetModuleIdentifier :: ModuleRef -> Ptr CSize -> IO CString

foreign import ccall unsafe "LLVMSetModuleIdentifier"
  ffiSetModuleIdentifier :: ModuleRef -> CString -> CSize -> IO ()

getModuleIdentifier :: ModuleRef -> IO String
getModuleIdentifier ref = getNameWithLength (ffiGetModuleIdentifier ref)

setModuleIdentifier :: ModuleRef -> String -> IO ()
setModuleIdentifier ref nm =
  withCStringLen nm $ \(ptr,sz) -> ffiSetModuleIdentifier ref ptr (fromIntegral sz)

foreign import ccall unsafe "LLVMGetFirstFunction"
  getFirstFunction :: ModuleRef -> IO ValueRef

foreign import ccall unsafe "LLVMGetLastFunction"
  getLastFunction :: ModuleRef -> IO ValueRef

foreign import ccall unsafe "LLVMGetNextFunction"
  getNextFunction :: ValueRef -> IO ValueRef

foreign import ccall unsafe "LLVMGetPreviousFunction"
  getPreviousFunction :: ValueRef -> IO ValueRef

getFunctions :: ModuleRef -> IO [ValueRef]
getFunctions m =   getLastFunction m >>= go []
  where go :: [ValueRef] -> ValueRef -> IO [ValueRef]
        go l vr
          | vr == nullPtr = pure l
          | otherwise = getPreviousFunction vr >>= go (vr:l)

foreign import ccall unsafe "LLVMParseBitcodeInContext2"
  parseBitcodeInContext2 :: ContextRef -> MemoryBufferRef -> Ptr ModuleRef -> IO LLVMBool

-- | Parse module from a memory buffer.
parseBitcode :: ContextRef -> MemoryBufferRef -> (Maybe ModuleRef -> IO a) -> IO a
parseBitcode ctx buf act =
  alloca $ \ptr -> do
    res <- parseBitcodeInContext2 ctx buf ptr
    if res == 0 then
      bracket (peek ptr) disposeModule (act . Just)
    else
      act Nothing

------------------------------------------------------------------------
-- Test case


main :: IO ()
main = do
  withMemoryBufferFromFile "main.bc" $ \mb -> do
    buf <- case mb of
             Left err -> fail $ "Error creating buffer: " ++ err
             Right b -> pure b
    withLLVMContext $ \ctx -> do
      parseBitcode ctx buf $ \mmod -> do
        m <- case mmod of
               Just m -> pure m
               Nothing -> fail $ "Error parsing bitcode."
        putStrLn =<< getModuleIdentifier m
        setModuleIdentifier m (replicate 100 'a')
        putStrLn =<< getModuleIdentifier m
        fns <- getFunctions m
        forM_ fns $ \f -> do
          putStrLn . ("Function: " ++) =<< getValueName f
          isDef <- not <$> isDeclaration f
          when isDef $ do
            blocks <- getBasicBlocks f
            forM_ blocks $ \blk -> do
              nm <- getBasicBlockName blk
              putStrLn ("  label " ++ nm ++ ":")
              insnList <- getInstructions blk
              forM_ insnList $ \insn -> do
                fmt <- printValueToString insn
                hPutStrLn stderr $ "  " ++ fmt
                putStr "      "
                case getInstructionOpcode insn of
                  LLVMRet -> do
                    arg <- printValueToString (getOperand insn 0)
                    putStrLn $ "ret " ++ arg
                  opc -> putStrLn $ show opc
