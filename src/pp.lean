import init.data.list
import init.data.to_string

import data.bitvec
import data.rbmap

import .ast

import tactic.linarith

namespace sized

def map {a b:Type} [has_sizeof a] (sz:ℕ) (f : Πx:a, sizeof x < sz → b) : Πxs:list a, (sizeof xs <= sz) → list b
| [] _      := []
| (x::xs) H :=
   have Hx  : sizeof x  <  sz, by { unfold sizeof has_sizeof.sizeof list.sizeof at *, linarith },
   have Hxs : sizeof xs <= sz, by { unfold sizeof has_sizeof.sizeof list.sizeof at *, linarith },
   f x Hx :: map xs Hxs
.

@[reducible]
def map_over {a b:Type} [has_sizeof a] (xs:list a) (f : Πx:a, sizeof x < sizeof xs → b) : list b :=
  map (sizeof xs) f xs (nat.less_than_or_equal.refl _).

end sized

namespace pp

reserve infixl ` <> `: 50
reserve infixl ` <+> `: 50
reserve infixl ` <$> `: 60

structure doc : Type := (compose : string → string).

def text (x:string) := doc.mk (λz, x ++ z).
def render (x:doc) : string := x.compose "".
def to_doc {a:Type} [has_to_string a] : a → doc := text ∘ to_string.

def empty : doc := doc.mk (λ z, z).
def next_to (x y : doc) : doc := doc.mk (x.compose ∘ y.compose).
infix <>  := next_to.

def spacesep (x y:doc) : doc  := x <> text " " <> y
def linesep (x y:doc)  : doc  := x <> text "\n" <> y.

infix <+> := spacesep.
infix <$> := linesep.

def hcat (xs:list doc) : doc := list.foldr next_to empty xs.
def vcat (xs:list doc) : doc := list.foldr linesep empty xs.

def punctuate (p:doc) : list doc → list doc
| [ ]     := []
| (x::xs) := x :: (list.foldr (λ a b, p :: a :: b) [] xs)
.

def nat : ℕ → doc := text ∘ to_string
def int : ℤ → doc := text ∘ to_string

def pp_nonzero : ℕ → doc
| nat.zero := empty
| n := nat n
.

def surrounding (first last : string) (x:doc) : doc :=
  text first <> x <> text last

def parens   : doc → doc := surrounding "(" ")"
def brackets : doc → doc := surrounding "[" "]"
def angles   : doc → doc := surrounding "<" ">"
def braces   : doc → doc := surrounding "{" "}"

def comma : doc := text ","
def commas : list doc → doc := hcat ∘ punctuate comma

end pp


namespace llvm
open pp

section layout_spec.
open layout_spec.

def pp_layout_body (sz abi:ℕ) (pref: option ℕ) : doc :=
  nat sz <> text ":" <> nat abi <>
    (option.rec empty (λx, text ":" <> nat x) pref)
.

def pp_align_type : align_type → doc
| align_type.integer := text "i"
| align_type.vector  := text "v"
| align_type.float   := text "f"
| align_type.aggregate := text "a"
.

def pp_mangling : mangling → doc
| mangling.elf := text "e"
| mangling.mips := text "m"
| mangling.mach_o := text "o"
| mangling.windows_coff     := text "w"
| mangling.windows_coff_x86 := text "x"
.

def pp_layout_spec : layout_spec → doc
| big_endian     := text "E"
| little_endian  := text "e"
| (pointer_size addr_space sz abi pref _idx) :=
     text "p" <> pp_nonzero addr_space <> text ":" <> pp_layout_body sz abi pref
| (align_size tp sz abi pref) :=
     pp_align_type tp <> pp_layout_body sz abi pref
| (native_int_size szs) := text "n" <> hcat (punctuate (text ":") (list.map nat szs))
| (stack_align n) := text "S" <> nat n
| (layout_spec.mangling m)     := text "m:" <> pp_mangling m
| (function_address_space n)  := text "P" <> nat n
| (stack_alloca n) := text "A" <> nat n
.

def pp_layout (xs:data_layout) : doc
  := hcat (punctuate (text "-") (list.map pp_layout_spec xs))
.

def l1 : data_layout :=
  [ big_endian,
    layout_spec.mangling mangling.mach_o,
    pointer_size 0 64 64 none 0,
    align_size align_type.integer 64 64 none,
    align_size align_type.float   80 128 none,
    align_size align_type.float   64 64 none,
    native_int_size [8,16,32,64],
    stack_align 128
  ]

end layout_spec.


def pp_ident (n:ident) : doc :=
  text "%" <> text (n.ident)  -- FIXME! deal with the 'validIdentifier' question
.

def pp_symbol (n:symbol) : doc :=
  text "@" <> text (n.symbol)
.

def pp_label : block_label → doc
| (block_label.named i) := pp_ident i
| (block_label.anon n)  := text "%" <> to_doc n
.

def packed_braces : doc → doc := surrounding "<{" "}>"

def pp_type : llvm_type → doc := λ_, empty.


meta def pp_tac :=
  `[unfold has_well_founded_of_has_sizeof has_well_founded.r sizeof_measure measure
      inv_image sizeof has_sizeof.sizeof psum.sizeof typed.sizeof const_expr.sizeof value.sizeof
      at *,
      repeat { rw llvm.typed.sizeof_spec' at *, unfold sizeof has_sizeof.sizeof at * },
      try { linarith }
   ].

def pp_conv_op : conv_op → doc
| conv_op.trunc      := text "trunc"
| conv_op.zext       := text "zext"
| conv_op.sext       := text "sext"
| conv_op.fp_trunc   := text "fptrunc"
| conv_op.fp_ext     := text "fpext"
| conv_op.fp_to_ui   := text "fptoui"
| conv_op.fp_to_si   := text "fptosi"
| conv_op.ui_to_fp   := text "uitofp"
| conv_op.si_to_fp   := text "sitofp"
| conv_op.ptr_to_int := text "ptrtoint"
| conv_op.int_to_ptr := text "inttoptr"
| conv_op.bit_cast   := text "bitcast"
.

mutual def pp_value, pp_const_expr
with pp_value : value → doc
| value.null           := text "null"
| value.undef          := text "undef"
| value.zero_init      := text "0"
| (value.integer i)    := to_doc i
| (value.bool b)       := to_doc b
| (value.ident n)      := pp_ident n
| (value.symbol n)     := pp_symbol n
| (value.const_expr e) := pp_const_expr e
| (value.label l)      := pp_label l
| (value.array tp vs)  := brackets (commas (sized.map_over vs (λv H, pp_type tp <+> pp_value v)))
| (value.vector tp vs) := angles (commas (sized.map_over vs (λv H, pp_type tp <+> pp_value v)))
| (value.struct fs)    := braces (commas (sized.map_over fs (λf H, pp_type (f.type) <+> pp_value (f.value))))
| (value.packed_struct fs) := packed_braces (commas (sized.map_over fs (λf H, pp_type (f.type) <+> pp_value (f.value))))

with pp_const_expr : const_expr → doc
| (const_expr.select cond x y) :=
     text "select" <+>
     pp_type (typed.type cond) <+> pp_value (typed.value cond) <+>
     text "," <+>
     pp_type (typed.type x) <+> pp_value (typed.value x) <+> text "," <+>
     pp_value (typed.value y)
| (const_expr.gep inbounds inrange tp vs) :=
    text "getelementpointer" <+>
    (if inbounds then text "inbounds " else empty) <>
    parens ( pp_type tp <> comma <+> commas (sized.map_over vs (λ v H, pp_type (typed.type v) <+> pp_value (typed.value v))))

| (const_expr.conv op x tp) :=
    pp_conv_op op <+> parens (pp_type (typed.type x) <+> pp_value (typed.value x) <+> text "to" <+> pp_type tp)

using_well_founded ⟨λ _ _, `[exact (has_well_founded_of_has_sizeof _)] , pp_tac⟩
.


end llvm.
