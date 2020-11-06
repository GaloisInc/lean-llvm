import Std.Data.RBMap

import LeanLLVM.Alignment
import LeanLLVM.AST
import LeanLLVM.Parser

open Std (RBMap)

namespace LLVM
namespace parse

section Mangling

open Mangling

def mangling_spec : parse Mangling :=
  parse.describe "mangling spec" $
  parse.choosePrefix
  [ ("e", pure elf)
  , ("m", pure mips)
  , ("o", pure mach_o)
  , ("w", pure windows_coff)
  , ("x", pure windows_coff_x86)
  ]

end Mangling


section LayoutSpec
open LayoutSpec

def pointer_spec : parse LayoutSpec :=
  parse.describe "pointer spec spec" $ do
     let addrSpace <- parse.opt 0 parse.nat;
     let sz   <- parse.textThen ":" parse.nat;
     let abi  <- parse.textThen ":" parse.nat;
     let pref <- parse.textThen ":" parse.nat;
     let idx  <- parse.opt' (parse.textThen ":" parse.nat);
     pure (pointerSize addrSpace sz abi pref idx)

def size_spec (t:AlignType) : parse LayoutSpec :=
  parse.describe "size spec" $ do
     let sz  <- parse.nat;
     let abi  <- parse.textThen ":" parse.nat;
     let pref <- parse.opt' (parse.textThen ":" parse.nat);
     pure (alignSize t sz abi pref)

def layout_spec : parse LayoutSpec :=
  parse.describe "layout spec" $
  parse.choosePrefix
  [ ("E", pure (endianness Endian.big))
  , ("e", pure (endianness Endian.little))
  , ("p", pointer_spec)
  , ("i", size_spec AlignType.integer)
  , ("v", size_spec AlignType.vector)
  , ("f", size_spec AlignType.float)
  , ("a", aggregateAlign <$> (parse.textThen ":" parse.nat) <*> (parse.textThen ":" parse.nat))
  , ("n", nativeIntSize <$> parse.sepBy parse.nat (parse.text ":"))
  , ("S", stackAlign <$> parse.nat)
  , ("P", functionAddressSpace <$> parse.nat)
  , ("A", stackAlloca <$> parse.nat)
  , ("m", mangling <$> (parse.textThen ":" mangling_spec))
  ]

end LayoutSpec

def data_layout : parse (List LayoutSpec) :=
  parse.describe "data layout" $
    parse.sepBy layout_spec (parse.text "-")

end parse
end LLVM

namespace LLVM

structure DataLayout :=
  (intLayout          : Endian)
  (stackAlignment     : Alignment)
  (aggregateAlignment : Alignment)
  (ptrSize            : Nat) -- size in bytes
  (ptrAlign           : Alignment)
  (integerInfo        : AlignInfo)
  (vectorInfo         : AlignInfo)
  (floatInfo          : AlignInfo)

def default_data_layout : DataLayout :=
  { intLayout := Endian.big
  , stackAlignment := unaligned
  , aggregateAlignment := unaligned
  , ptrSize := 8 -- 8 bytes, 64 bits
  , ptrAlign := align8
  , integerInfo := Std.RBMap.fromList
       [ ( 1, unaligned)
       , ( 8, unaligned)
       , (16, align2)
       , (32, align4)
       , (64, align8)
       ] _
  , floatInfo := Std.RBMap.fromList
       [ ( 16, align2)
       , ( 32, align4)
       , ( 64, align8)
       , (128, align16)
       ] _
  , vectorInfo := Std.RBMap.fromList
       [ ( 64, align8)
       , (128, align16)
       ] _
  }

def updateAlign (x:Nat) (a:Alignment) (ai:AlignInfo) : AlignInfo := ai.insert x a

def addIntegerAlignment (x:Nat) (a:Alignment) (dl:DataLayout) : DataLayout :=
  { dl with integerInfo := updateAlign x a dl.integerInfo }

def addFloatAlignment (x:Nat) (a:Alignment) (dl:DataLayout) : DataLayout :=
  { dl with floatInfo := updateAlign x a dl.floatInfo }

def addVectorAlignment (x:Nat) (a:Alignment) (dl:DataLayout) : DataLayout :=
  { dl with vectorInfo := updateAlign x a dl.vectorInfo }

section LayoutSpec
open LayoutSpec
open AlignType

def addLayoutSpec (dl:DataLayout) : LayoutSpec → Except String DataLayout
| endianness e => pure { dl with intLayout := e }
| stackAlign sa =>
  match toAlignment sa with
  | none   => throw ("invalid stack alignment: " ++ (Nat.toDigits 10 sa).asString)
  | some a => pure { dl with stackAlignment := a }
| aggregateAlign abi pref =>
  match toAlignment abi with
  | none   => throw ("invalid aggregate alignment: " ++ (Nat.toDigits 10 abi).asString)
  | some a => pure { dl with aggregateAlignment := a }
| pointerSize addr sz abi _pref _idx =>
  match toAlignment abi with
  | none   => throw $ "invalid pointer alignment: " ++ (Nat.toDigits 10 abi).asString
  | some a => pure { dl with ptrSize := sz, ptrAlign := a }
| alignSize tp sz abi _pref =>
  match toAlignment abi with
  | none   => throw $ "invalid alignment: " ++ (Nat.toDigits 10 abi).asString
  | some a =>
    match tp with
    | integer   => pure (addIntegerAlignment sz a dl)
    | vector    => pure (addVectorAlignment  sz a dl)
    | float     => pure (addFloatAlignment   sz a dl)
| _ => pure dl -- ignore other layout specs

end LayoutSpec

def computeDataLayout (ls:List LayoutSpec) : Except String DataLayout :=
  List.foldlM addLayoutSpec default_data_layout ls

end LLVM
