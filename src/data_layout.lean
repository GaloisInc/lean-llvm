import init.control.combinators
import init.data.rbmap

import .alignment
import .ast
import .parser


namespace llvm.parse.

def pointer_spec : parse llvm.layout_spec :=
  parse.describe "pointer spec spec" $
  do addrSpace <- parse.opt 0 parse.nat;
     sz   <- parse.text ":" *> parse.nat;
     abi  <- parse.text ":" *> parse.nat;
     pref <- parse.text ":" *> parse.nat;
     idx  <- parse.opt' (parse.text ":" *> parse.nat);
     pure (llvm.layout_spec.pointer_size addrSpace sz abi pref idx).

def size_spec (t:llvm.align_type) : parse llvm.layout_spec :=
  parse.describe "size spec" $
  do sz   <- parse.nat;
     abi  <- parse.text ":" *> parse.nat;
     pref <- parse.opt' (parse.text ":" *> parse.nat);
     pure (llvm.layout_spec.align_size t sz abi pref).

def mangling_spec : parse llvm.mangling :=
  parse.describe "mangling spec" $
  parse.choosePrefix
  [ ("e", pure llvm.mangling.elf)
  , ("m", pure llvm.mangling.mips)
  , ("o", pure llvm.mangling.mach_o)
  , ("w", pure llvm.mangling.windows_coff)
  , ("x", pure llvm.mangling.windows_coff_x86)
  ]

def layout_spec : parse llvm.layout_spec :=
  parse.describe "layout spec" $
  parse.choosePrefix
  [ ("E", pure (llvm.layout_spec.endianness llvm.endian.big))
  , ("e", pure (llvm.layout_spec.endianness llvm.endian.little))
  , ("p", pointer_spec)
  , ("i", size_spec llvm.align_type.integer)
  , ("v", size_spec llvm.align_type.vector)
  , ("f", size_spec llvm.align_type.float)
  , ("a", llvm.layout_spec.aggregate_align <$> (parse.text ":" *> parse.nat) <*> (parse.text ":" *> parse.nat))
  , ("n", llvm.layout_spec.native_int_size <$> parse.sepBy parse.nat (parse.text ":"))
  , ("S", llvm.layout_spec.stack_align <$> parse.nat)
  , ("P", llvm.layout_spec.function_address_space <$> parse.nat)
  , ("A", llvm.layout_spec.stack_alloca <$> parse.nat)
  , ("m", llvm.layout_spec.mangling <$> (parse.text ":" *> mangling_spec))
  ].

def data_layout : parse (List llvm.layout_spec) :=
  parse.describe "data layout" $
    parse.sepBy layout_spec (parse.text "-").

end llvm.parse.

namespace llvm.

structure data_layout :=
  ( int_layout : endian )
  ( stack_alignment : alignment )
  ( aggregate_alignment : alignment )
  ( ptr_size : bytes ) -- size in bytes
  ( ptr_align : alignment )
  ( integer_info : alignInfo )
  ( vector_info : alignInfo )
  ( float_info : alignInfo )
.

def default_data_layout : data_layout :=
  { int_layout := endian.big
  , stack_alignment := noAlignment
  , aggregate_alignment := noAlignment
  , ptr_size := bytes.mk 8 -- 8 bytes, 64 bits
  , ptr_align := alignment.mk 3
  , integer_info := RBMap.fromList
       [ ( 1, noAlignment)
       , ( 8, noAlignment)
       , (16, alignment.mk 1)
       , (32, alignment.mk 2)
       , (64, alignment.mk 3)
       ] _
  , float_info := RBMap.fromList
       [ ( 16, alignment.mk 1)
       , ( 32, alignment.mk 2)
       , ( 64, alignment.mk 3)
       , (128, alignment.mk 4)
       ] _
  , vector_info := RBMap.fromList
       [ ( 64, alignment.mk 3)
       , (128, alignment.mk 4)
       ] _
  }.

def updateAlign (x:Nat) (a:alignment) (ai:alignInfo) : alignInfo :=
  ai.insert x a.

def addIntegerAlignment (x:Nat) (a:alignment) (dl:data_layout) : data_layout :=
  { dl with integer_info := updateAlign x a dl.integer_info }

def addFloatAlignment (x:Nat) (a:alignment) (dl:data_layout) : data_layout :=
  { dl with float_info := updateAlign x a dl.float_info }

def addVectorAlignment (x:Nat) (a:alignment) (dl:data_layout) : data_layout :=
  { dl with vector_info := updateAlign x a dl.vector_info }


def addLayoutSpec (dl:data_layout) : layout_spec → Except String data_layout

| (layout_spec.endianness e) := pure { dl with int_layout := e }

| (layout_spec.stack_align sa) :=
     match toAlignment sa with
     | none => throw ("invalid stack alignment: " ++ (Nat.toDigits 10 sa).asString)
     | (some a) => pure { dl with stack_alignment := a }

| (layout_spec.aggregate_align abi _pref) :=
     match toAlignment abi with
     | none => throw ("invalid aggregate alignment: " ++ (Nat.toDigits 10 abi).asString)
     | (some a) => pure { dl with aggregate_alignment := a }

| (layout_spec.pointer_size addr sz abi _pref _idx) :=
     match toAlignment abi with
     | none => throw ("invalid pointer alignment: " ++ (Nat.toDigits 10 abi).asString)
     | (some a) => pure { dl with ptr_size := toBytes sz, ptr_align := a }

| (layout_spec.align_size tp sz abi _pref) :=
     match toAlignment abi with
     | none => throw ("invalid alignment: " ++ (Nat.toDigits 10 abi).asString)
     | (some a) =>
       match tp with
       | align_type.integer   => pure (addIntegerAlignment sz a dl)
       | align_type.vector    => pure (addVectorAlignment sz a dl)
       | align_type.float     => pure (addFloatAlignment sz a dl)

| _ := pure dl -- ignore other layout specs

def computeDataLayout (ls:List layout_spec) : Except String data_layout :=
  List.mfoldl addLayoutSpec default_data_layout ls.

end llvm.
