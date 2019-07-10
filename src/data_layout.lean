
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
  , ("a", size_spec llvm.align_type.aggregate)
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
.



end llvm.
