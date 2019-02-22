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

@[reducible]
def psum_size {A B:Type} (f:A → ℕ) (g:B → ℕ) : psum A B → ℕ
| (psum.inl x) := f x
| (psum.inr y) := g y
.

@[reducible]
def psum3_has_wf {A B C:Type} [has_sizeof A] [has_sizeof B] [has_sizeof C] : has_well_founded (psum A (psum B C)) :=
  ⟨ measure (psum_size sizeof (psum_size sizeof sizeof))
  , measure_wf _
  ⟩.

@[reducible]
def psum4_has_wf {A B C D:Type} [has_sizeof A] [has_sizeof B] [has_sizeof C] [has_sizeof D]: has_well_founded (psum A (psum B (psum C D))) :=
  ⟨ measure (psum_size sizeof (psum_size sizeof (psum_size sizeof sizeof)))
  , measure_wf _
  ⟩.


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

def quotes : doc → doc := surrounding "\'" "\'"
def dquotes : doc → doc := surrounding "\"" "\""

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


-- FIXME! We need to handle escaping...
def pp_string_literal : string → doc := dquotes ∘ text

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

def pp_float_type : float_type → doc
| float_type.half      := text "half"
| float_type.float     := text "float"
| float_type.double    := text "double"
| float_type.fp128     := text "fp128"
| float_type.x86_fp80  := text "x86_fp80"
| float_type.ppc_fp128 := text "ppcfp128"
.

def pp_prim_type : prim_type → doc
| prim_type.label          := text "label"
| prim_type.void           := text "void"
| prim_type.x86mmx         := text "x86mmx"
| prim_type.metadata       := text "metadata"
| (prim_type.float_type f) := pp_float_type f
| (prim_type.integer n)    := text "i" <> int n
.

def pp_arg_list (va:bool) (xs:list doc) : doc :=
  parens (commas (xs ++ if va then [text "..."] else []))

meta def pp_type_tac :=
  `[unfold has_well_founded.r measure inv_image sizeof has_sizeof.sizeof
      llvm_type.sizeof
      at *,
    try { linarith }
   ].

def pp_type : llvm_type → doc
| (llvm_type.prim_type pt)       := pp_prim_type pt
| (llvm_type.alias n)            := pp_ident n
| (llvm_type.array len ty)       := brackets (int len <+> text "x" <+> pp_type ty)
| (llvm_type.ptr_to ty)          := pp_type ty <> text "*"
| (llvm_type.struct ts)          := braces (commas (sized.map_over ts (λ t H, pp_type t)))
| (llvm_type.packed_struct ts)   := packed_braces (commas (sized.map_over ts (λ t H, pp_type t)))
| (llvm_type.fun_ty ret args va) := pp_type ret <> pp_arg_list va (sized.map_over args (λ a H, pp_type a))
| (llvm_type.vector len ty)      := angles (int len <+> text "x" <+> pp_type ty)
| (llvm_type.opaque)             := text "opaque"

using_well_founded ⟨λ _ _, `[exact ⟨measure sizeof, measure_wf _⟩] , pp_type_tac⟩
.


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

def pp_wrap_bits (nuw nsw:bool) : doc :=
  (if nuw then text " nuw" else empty) <>
  (if nsw then text " nsw" else empty)

def pp_exact_bit (exact:bool) : doc :=
  if exact then text " exact" else empty

def pp_arith_op : arith_op → doc
| (arith_op.add nuw nsw)  := text "add" <> pp_wrap_bits nuw nsw
| (arith_op.sub nuw nsw)  := text "sub" <> pp_wrap_bits nuw nsw
| (arith_op.mul nuw nsw)  := text "mul" <> pp_wrap_bits nuw nsw
| (arith_op.udiv exact)   := text "udiv" <> pp_exact_bit exact
| (arith_op.sdiv exact)   := text "sdiv" <> pp_exact_bit exact
| (arith_op.urem)         := text "urem"
| (arith_op.srem)         := text "srem"
| (arith_op.fadd)         := text "fadd"
| (arith_op.fsub)         := text "fsub"
| (arith_op.fmul)         := text "fmul"
| (arith_op.fdiv)         := text "fdiv"
| (arith_op.frem)         := text "frem"
.

def pp_icmp_op : icmp_op → doc
| (icmp_op.ieq)           := text "eq"
| (icmp_op.ine)           := text "ne"
| (icmp_op.iugt)          := text "ugt"
| (icmp_op.iult)          := text "ult"
| (icmp_op.iuge)          := text "uge"
| (icmp_op.iule)          := text "ule"
| (icmp_op.isgt)          := text "sgt"
| (icmp_op.islt)          := text "slt"
| (icmp_op.isge)          := text "sge"
| (icmp_op.isle)          := text "sle"
.

def pp_fcmp_op : fcmp_op → doc
| (fcmp_op.ffalse)        := text "false"
| (fcmp_op.ftrue)         := text "true"
| (fcmp_op.foeq)          := text "oeq"
| (fcmp_op.fogt)          := text "ogt"
| (fcmp_op.foge)          := text "oge"
| (fcmp_op.folt)          := text "olt"
| (fcmp_op.fole)          := text "ole"
| (fcmp_op.fone)          := text "one"
| (fcmp_op.ford)          := text "ord"
| (fcmp_op.fueq)          := text "ueq"
| (fcmp_op.fugt)          := text "ugt"
| (fcmp_op.fuge)          := text "uge"
| (fcmp_op.fult)          := text "ult"
| (fcmp_op.fule)          := text "ule"
| (fcmp_op.fune)          := text "une"
| (fcmp_op.funo)          := text "uno"
.

def pp_bit_op : bit_op → doc
| (bit_op.shl nuw nsw)    := text "shl" <> pp_wrap_bits nuw nsw
| (bit_op.lshr exact)     := text "lshr" <> pp_exact_bit exact
| (bit_op.ashr exact)     := text "ashr" <> pp_exact_bit exact
| (bit_op.and)            := text "and"
| (bit_op.or)             := text "or"
| (bit_op.xor)            := text "xor"
.


meta def pp_val_tac :=
  `[unfold has_well_founded.r measure inv_image sized.psum_size sizeof has_sizeof.sizeof
      typed.sizeof const_expr.sizeof value.sizeof val_md.sizeof debug_loc.sizeof option.sizeof
      at *,
    repeat { rw llvm.typed.sizeof_spec' at *, unfold sizeof has_sizeof.sizeof at * },
    try { linarith }
   ].

mutual def pp_value, pp_const_expr, pp_md, pp_debug_loc
with pp_value : value → doc
| value.null               := text "null"
| value.undef              := text "undef"
| value.zero_init          := text "0"
| (value.integer i)        := to_doc i
| (value.bool b)           := to_doc b
| (value.string s)         := text "c" <> pp_string_literal s
| (value.ident n)          := pp_ident n
| (value.symbol n)         := pp_symbol n
| (value.const_expr e)     := pp_const_expr e
| (value.label l)          := pp_label l
| (value.array tp vs)      := brackets (commas (sized.map_over vs (λv H, pp_type tp <+> pp_value v)))
| (value.vector tp vs)     := angles (commas (sized.map_over vs (λv H, pp_type tp <+> pp_value v)))
| (value.struct fs)        := braces (commas (sized.map_over fs (λf H, pp_type (f.type) <+> pp_value (f.value))))
| (value.packed_struct fs) := packed_braces (commas (sized.map_over fs (λf H, pp_type (f.type) <+> pp_value (f.value))))
| (value.md md)            := pp_md md

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

| (const_expr.arith op x y) :=
    pp_arith_op op <+> parens (pp_type (typed.type x) <+> pp_value (typed.value x) <> comma <+> pp_value y)

| (const_expr.fcmp op x y) :=
    text "fcmp" <+> pp_fcmp_op op <+>
        parens (pp_type (typed.type x) <+> pp_value (typed.value x) <> comma <+>
                pp_type (typed.type y) <+> pp_value (typed.value y))

| (const_expr.icmp op x y) :=
    text "icmp" <+> pp_icmp_op op <+>
        parens (pp_type (typed.type x) <+> pp_value (typed.value x) <> comma <+>
                pp_type (typed.type y) <+> pp_value (typed.value y))

| (const_expr.bit op x y) :=
    pp_bit_op op <+> parens (pp_type (typed.type x) <+> pp_value (typed.value x) <> comma <+> pp_value y)

| (const_expr.block_addr sym lab) :=
    text "blockaddress" <+> parens (pp_symbol sym <> comma <+> pp_label lab)

with pp_md : val_md → doc
| (val_md.string s)  := text "!" <> pp_string_literal s
| (val_md.value x)   := pp_type (typed.type x) <+> pp_value (typed.value x)
| (val_md.ref i)     := text "!" <> int i
| (val_md.node xs)   := text "!" <> braces (commas 
      (sized.map_over xs (λ mx,
        match mx with
        | none   := (λ _, text "null")
        | some x := (λ H, pp_md x)
        end )))
| (val_md.md_loc loc) := pp_debug_loc loc

with pp_debug_loc : debug_loc → doc
| (debug_loc.debug_loc line col scope none) := text "!DILocation" <> parens (commas
    [ text "line:"   <+> int line
    , text "column:" <+> int col
    , text "scope:"  <+> pp_md scope
    ])
| (debug_loc.debug_loc line col scope (some ia)) := text "!DILocation" <> parens (commas
    [ text "line:"      <+> int line
    , text "column:"    <+> int col
    , text "scope:"     <+> pp_md scope
    , text "inlinedAt:" <+> pp_md ia
    ])

using_well_founded ⟨λ _ _, `[exact (sized.psum4_has_wf)] , pp_val_tac⟩
.


end llvm.
