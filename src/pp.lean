import init.data.list
import init.data.rbmap
import init.data.string

--import data.bitvec
--import tactic.linarith

import .ast
--import .sized

namespace pp

reserve infixl ` <> `: 50
reserve infixl ` <+> `: 50
reserve infixl ` $+$ `: 60

structure doc : Type := (compose : String → String).

def text (x:String) := doc.mk (fun z => x ++ z).
def render (x:doc) : String := x.compose "".
def to_doc {a:Type} [HasToString a] : a → doc := text ∘ toString.

def empty : doc := doc.mk id.
def next_to (x y : doc) : doc := doc.mk (x.compose ∘ y.compose).
infix <>  := next_to.

instance : Inhabited doc := ⟨empty⟩

def spacesep (x y:doc) : doc  := x <> text " " <> y
def linesep (x y:doc)  : doc  := x <> text "\n" <> y.

infix <+> := spacesep.
infix $+$ := linesep.

def hcat (xs:List doc) : doc := List.foldr next_to empty xs.
def hsep (xs:List doc) : doc := List.foldr spacesep empty xs.
def vcat (xs:List doc) : doc := List.foldr linesep empty xs.

def punctuate (p:doc) : List doc → List doc
| [ ]     => []
| (x::xs) => x :: (List.foldr (fun a b => p :: a :: b) [] xs)
.

def nat : Nat → doc := text ∘ toString
def int : Int → doc := text ∘ toString

def pp_nonzero : Nat → doc
| Nat.zero => empty
| n => nat n
.

def surrounding (first last : String) (x:doc) : doc :=
  text first <> x <> text last

def parens   : doc → doc := surrounding "(" ")"
def brackets : doc → doc := surrounding "[" "]"
def angles   : doc → doc := surrounding "<" ">"
def braces   : doc → doc := surrounding "{" "}"

def comma : doc := text ","
def commas : List doc → doc := hcat ∘ punctuate comma

def quotes : doc → doc := surrounding "\'" "\'"
def dquotes : doc → doc := surrounding "\"" "\""

def pp_opt {A:Type} (f:A → doc) : Option A → doc
| (some a) => f a
| none     => empty
.

end pp


namespace llvm
open pp

section layout_spec.
open layout_spec.

def pp_layout_body (sz abi:Nat) (pref: Option Nat) : doc :=
  nat sz <> text ":" <> nat abi <>
  pp_opt (λx => text ":" <> nat x) pref.

def pp_align_type : align_type → doc
| align_type.integer => text "i"
| align_type.vector  => text "v"
| align_type.float   => text "f"
.

def pp_mangling : mangling → doc
| mangling.elf => text "e"
| mangling.mips => text "m"
| mangling.mach_o => text "o"
| mangling.windows_coff     => text "w"
| mangling.windows_coff_x86 => text "x"
.

def pp_layout_spec : layout_spec → doc
| (endianness endian.big)    => text "E"
| (endianness endian.little) => text "e"
| (pointer_size addr_space sz abi pref idx) =>
     text "p" <> pp_nonzero addr_space <> text ":"
     <> nat sz <> text ":"
     <> nat abi <> text ":"
     <> nat pref <> text ":"
     <> pp_opt (λi => text ":" <> nat i) idx

| (align_size tp sz abi pref) =>
     pp_align_type tp <> pp_layout_body sz abi pref
| (native_int_size szs) => text "n" <> hcat (punctuate (text ":") (List.map nat szs))
| (stack_align n) => text "S" <> nat n
| (aggregate_align abi pref) => text "a:" <> nat abi <> text ":" <> nat pref
| (layout_spec.mangling m)     => text "m:" <> pp_mangling m
| (function_address_space n)  => text "P" <> nat n
| (stack_alloca n) => text "A" <> nat n
.

def pp_layout (xs:List layout_spec) : doc
  := hcat (punctuate (text "-") (List.map pp_layout_spec xs))
.

def l1 : List layout_spec :=
  [ endianness endian.big,
    layout_spec.mangling mangling.mach_o,
    pointer_size 0 64 64 64 none,
    align_size align_type.integer 64 64 none,
    align_size align_type.float   80 128 none,
    align_size align_type.float   64 64 none,
    native_int_size [8,16,32,64],
    stack_align 128
  ]

end layout_spec.


-- FIXME! We need to handle escaping...
def pp_string_literal : String → doc := dquotes ∘ text

def pp_ident : ident → doc
| ident.named nm => text "%" <> text nm  -- FIXME! deal with the 'validIdentifier' question
| ident.anon i   => text "%" <> to_doc i
.

def pp_symbol (n:symbol) : doc :=
  text "@" <> text (n.symbol)
.

def pp_label : block_label → doc
| block_label.mk i => pp_ident i
.

def packed_braces : doc → doc := surrounding "<{" "}>"

def pp_float_type : float_type → doc
| float_type.half      => text "half"
| float_type.float     => text "float"
| float_type.double    => text "double"
| float_type.fp128     => text "fp128"
| float_type.x86_fp80  => text "x86_fp80"
| float_type.ppc_fp128 => text "ppcfp128"
.

def pp_prim_type : prim_type → doc
| prim_type.label          => text "label"
| prim_type.token          => text "token"
| prim_type.void           => text "void"
| prim_type.x86mmx         => text "x86mmx"
| prim_type.metadata       => text "metadata"
| (prim_type.float_type f) => pp_float_type f
| (prim_type.integer n)    => text "i" <> int n
.

def pp_arg_list (va:Bool) (xs:List doc) : doc :=
  parens (commas (xs ++ if va then [text "..."] else []))

/-
meta def pp_type_tac :=
  `[unfold has_well_founded.r measure inv_image sizeof has_sizeof.sizeof
      llvm_type.sizeof
      at *,
    try { linarith }
   ].
-/

partial def pp_type : llvm_type → doc
| (llvm_type.prim_type pt)       => pp_prim_type pt
| (llvm_type.alias nm)           => text "%" <> text nm
| (llvm_type.array len ty)       => brackets (int len <+> text "x" <+> pp_type ty)
| (llvm_type.ptr_to ty)          => pp_type ty <> text "*"
| (llvm_type.struct false ts)    => braces (commas (List.map pp_type ts.toList))
| (llvm_type.struct true  ts)    => packed_braces (commas (List.map pp_type ts.toList))
| (llvm_type.fun_ty ret args va) => pp_type ret <> pp_arg_list va (List.map pp_type args.toList)
| (llvm_type.vector len ty)      => angles (int len <+> text "x" <+> pp_type ty)
.


def pp_conv_op : conv_op → doc
| conv_op.trunc      => text "trunc"
| conv_op.zext       => text "zext"
| conv_op.sext       => text "sext"
| conv_op.fp_trunc   => text "fptrunc"
| conv_op.fp_ext     => text "fpext"
| conv_op.fp_to_ui   => text "fptoui"
| conv_op.fp_to_si   => text "fptosi"
| conv_op.ui_to_fp   => text "uitofp"
| conv_op.si_to_fp   => text "sitofp"
| conv_op.ptr_to_int => text "ptrtoint"
| conv_op.int_to_ptr => text "inttoptr"
| conv_op.bit_cast   => text "bitcast"
.

def pp_wrap_bits (nuw nsw:Bool) : doc :=
  (if nuw then text " nuw" else empty) <>
  (if nsw then text " nsw" else empty)

def pp_exact_bit (exact:Bool) : doc :=
  if exact then text " exact" else empty

def pp_arith_op : arith_op → doc
| (arith_op.add nuw nsw)  => text "add" <> pp_wrap_bits nuw nsw
| (arith_op.sub nuw nsw)  => text "sub" <> pp_wrap_bits nuw nsw
| (arith_op.mul nuw nsw)  => text "mul" <> pp_wrap_bits nuw nsw
| (arith_op.udiv exact)   => text "udiv" <> pp_exact_bit exact
| (arith_op.sdiv exact)   => text "sdiv" <> pp_exact_bit exact
| (arith_op.urem)         => text "urem"
| (arith_op.srem)         => text "srem"
| (arith_op.fadd)         => text "fadd"
| (arith_op.fsub)         => text "fsub"
| (arith_op.fmul)         => text "fmul"
| (arith_op.fdiv)         => text "fdiv"
| (arith_op.frem)         => text "frem"
.

def pp_icmp_op : icmp_op → doc
| (icmp_op.ieq)           => text "eq"
| (icmp_op.ine)           => text "ne"
| (icmp_op.iugt)          => text "ugt"
| (icmp_op.iult)          => text "ult"
| (icmp_op.iuge)          => text "uge"
| (icmp_op.iule)          => text "ule"
| (icmp_op.isgt)          => text "sgt"
| (icmp_op.islt)          => text "slt"
| (icmp_op.isge)          => text "sge"
| (icmp_op.isle)          => text "sle"
.

def pp_fcmp_op : fcmp_op → doc
| (fcmp_op.ffalse)        => text "false"
| (fcmp_op.ftrue)         => text "true"
| (fcmp_op.foeq)          => text "oeq"
| (fcmp_op.fogt)          => text "ogt"
| (fcmp_op.foge)          => text "oge"
| (fcmp_op.folt)          => text "olt"
| (fcmp_op.fole)          => text "ole"
| (fcmp_op.fone)          => text "one"
| (fcmp_op.ford)          => text "ord"
| (fcmp_op.fueq)          => text "ueq"
| (fcmp_op.fugt)          => text "ugt"
| (fcmp_op.fuge)          => text "uge"
| (fcmp_op.fult)          => text "ult"
| (fcmp_op.fule)          => text "ule"
| (fcmp_op.fune)          => text "une"
| (fcmp_op.funo)          => text "uno"
.

def pp_bit_op : bit_op → doc
| (bit_op.shl nuw nsw)    => text "shl" <> pp_wrap_bits nuw nsw
| (bit_op.lshr exact)     => text "lshr" <> pp_exact_bit exact
| (bit_op.ashr exact)     => text "ashr" <> pp_exact_bit exact
| (bit_op.and)            => text "and"
| (bit_op.or)             => text "or"
| (bit_op.xor)            => text "xor"
.


/-
meta def pp_val_tac :=
  `[unfold has_well_founded.r measure inv_image sized.psum_size sizeof has_sizeof.sizeof
      typed.sizeof const_expr.sizeof value.sizeof val_md.sizeof debug_loc.sizeof option.sizeof
      at *,
    repeat { rw llvm.typed.sizeof_spec' at *, unfold sizeof has_sizeof.sizeof at * },
    try { linarith }
   ].
-/

def pp_const_expr (pp_value : value → doc) : const_expr → doc
| (const_expr.select cond x y) =>
     text "select" <+>
     pp_type (typed.type cond) <+> pp_value (typed.value cond) <+>
     text "," <+>
     pp_type (typed.type x) <+> pp_value (typed.value x) <+> text "," <+>
     pp_value (typed.value y)

| (const_expr.gep inbounds inrange tp vs) =>
    text "getelementpointer" <+>
    (if inbounds then text "inbounds " else empty) <>
    parens ( pp_type tp <> comma <+> commas (List.map (λ (v:typed value) => pp_type v.type <+> pp_value v.value) vs.toList))

| (const_expr.conv op x tp) =>
    pp_conv_op op <+> parens (pp_type (typed.type x) <+> pp_value (typed.value x) <+> text "to" <+> pp_type tp)

| (const_expr.arith op x y) =>
    pp_arith_op op <+> parens (pp_type (typed.type x) <+> pp_value (typed.value x) <> comma <+> pp_value y)

| (const_expr.fcmp op x y) =>
    text "fcmp" <+> pp_fcmp_op op <+>
        parens (pp_type (typed.type x) <+> pp_value (typed.value x) <> comma <+>
                pp_type (typed.type y) <+> pp_value (typed.value y))

| (const_expr.icmp op x y) =>
    text "icmp" <+> pp_icmp_op op <+>
        parens (pp_type (typed.type x) <+> pp_value (typed.value x) <> comma <+>
                pp_type (typed.type y) <+> pp_value (typed.value y))

| (const_expr.bit op x y) =>
    pp_bit_op op <+> parens (pp_type (typed.type x) <+> pp_value (typed.value x) <> comma <+> pp_value y)

| (const_expr.block_addr sym lab) =>
    text "blockaddress" <+> parens (pp_symbol sym <> comma <+> pp_label lab)
.

def pp_debug_loc (pp_md : val_md → doc) : debug_loc → doc
| (debug_loc.debug_loc line col scope none) => text "!DILocation" <> parens (commas
    [ text "line:"   <+> int line
    , text "column:" <+> int col
    , text "scope:"  <+> pp_md scope
    ])
| (debug_loc.debug_loc line col scope (some ia)) => text "!DILocation" <> parens (commas
    [ text "line:"      <+> int line
    , text "column:"    <+> int col
    , text "scope:"     <+> pp_md scope
    , text "inlinedAt:" <+> pp_md ia
    ])
.

partial def pp_md (pp_value : value → doc) : val_md → doc
| (val_md.string s)  => text "!" <> pp_string_literal s
| (val_md.value x)   => pp_type (typed.type x) <+> pp_value (typed.value x)
| (val_md.ref i)     => text "!" <> int i
| (val_md.node xs)   => text "!" <> braces (commas (List.map (λ mx => Option.casesOn mx (text "null") pp_md) xs))
| (val_md.loc loc) => pp_debug_loc pp_md loc
| (val_md.debug_info) => empty
.


partial def pp_value : value → doc
| value.null               => text "null"
| value.undef              => text "undef"
| value.zero_init          => text "0"
| (value.integer i)        => to_doc i
| (value.bool b)           => to_doc b
| (value.string s)         => text "c" <> pp_string_literal s
| (value.ident n)          => pp_ident n
| (value.symbol n)         => pp_symbol n
| (value.const_expr e)     => pp_const_expr pp_value e
| (value.label l)          => pp_label l
| (value.array tp vs)      => brackets (commas (List.map (λv => pp_type tp <+> pp_value v) vs.toList))
| (value.vector tp vs)     => angles (commas (List.map (λv => pp_type tp <+> pp_value v) vs.toList))
| (value.struct fs)        => braces (commas (List.map (λ(f : typed value) => pp_type f.type <+> pp_value f.value) fs.toList))
| (value.packed_struct fs) => packed_braces (commas (List.map (λ(f:typed value) => pp_type f.type <+> pp_value f.value) fs.toList))
| (value.md md)            => pp_md pp_value md
.

def pp_atomic_ordering : atomic_ordering → doc
| atomic_ordering.unordered => text "unordered"
| atomic_ordering.monotonic => text "monotonic"
| atomic_ordering.acquire   => text "acquire"
| atomic_ordering.release   => text "release"
| atomic_ordering.acq_rel   => text "acq_rel"
| atomic_ordering.seq_cst   => text "seq_cst"
.

def pp_align : Option Nat → doc
| (some a) => comma <+> text "align" <+> nat a
| none     => empty
.

def pp_scope : Option String → doc :=
  pp_opt (λnm => text "syncscope" <> parens (pp_string_literal nm))
.

def pp_call (tailcall:Bool) (mty:Option llvm_type) (f:value) (args:List (typed value)) : doc :=
  (if tailcall then text "tail call" else text "call") <+>
  (match mty with
  | none => pp.text "void"
  | some ty => pp_type ty) <+>
  pp_value f <+>
  parens (commas (List.map (λ(x:typed value) => pp_type x.type <+> pp_value x.value) args))
.

def pp_alloca (tp:llvm_type) (len:Option (typed value)) (align:Option Nat) : doc :=
  text "alloca" <+> pp_type tp <>
  pp_opt (λv => comma <+> pp_type (typed.type v) <+> pp_value (typed.value v)) len <>
  pp_align align
.

def pp_load (ptr:typed value) (ord:Option atomic_ordering) (align : Option Nat) : doc :=
  text "load" <>
  (if Option.isSome ord then text " atomic" else empty) <+>
  pp_type (typed.type ptr) <+> pp_value (typed.value ptr) <>
  pp_opt pp_atomic_ordering ord <>
  pp_opt pp_align align
.

def pp_store (val:typed value) (ptr:typed value) (align:Option Nat) : doc :=
  text "store" <+>
  pp_type (typed.type val) <+> pp_value (typed.value val) <> comma <+>
  pp_type (typed.type ptr) <+> pp_value (typed.value ptr) <>
  pp_align align
.

def pp_phi_arg (vl:value × block_label) : doc :=
  brackets (pp_value vl.1 <> comma <+> pp_label vl.2)
.

def pp_gep (bounds:Bool) (base:typed value) (xs:List (typed value)) : doc :=
  text "getelementpointer" <>
  (if bounds then text " inbounds" else empty) <+>
  commas (List.map (λ(x:typed value) => pp_type x.type <+> pp_value x.value) (base::xs))
.

def pp_vector_index (v:value) : doc :=
  pp_type (llvm_type.prim_type (prim_type.integer 32)) <+> pp_value v
.

def pp_typed_label (l:block_label) : doc :=
  pp_type (llvm_type.prim_type (prim_type.label)) <+> pp_label l
.

def pp_invoke (ty:llvm_type) (f:value) (args:List (typed value)) (to:block_label) (uw:block_label) : doc :=
  text "invoke" <+> pp_type ty <+> pp_value f <>
  parens (commas (List.map (λ(v:typed value) => pp_type v.type <+> pp_value v.value) args)) <+>
  text "to" <+> pp_typed_label to <+>
  text "unwind" <+> pp_typed_label uw
.

def pp_clause : (clause × typed value)→ doc
| (clause.catch, v)  => text "catch" <+> pp_type (typed.type v) <+> pp_value (typed.value v)
| (clause.filter, v) => text "filter" <+> pp_type (typed.type v) <+> pp_value (typed.value v)
.

def pp_clauses (is_cleanup:Bool) (cs:List (clause × typed value) ): doc :=
  hsep
    ((if is_cleanup then [text "cleanup"] else []) ++
     (List.map pp_clause cs)
    )
.

def pp_switch_entry (ty:llvm_type) : (Nat × block_label) → doc
| (i, l) => pp_type ty <+> nat i <> comma <+> pp_label l
.

def pp_instr : instruction → doc
| (instruction.ret v) => text "ret" <+> pp_type (typed.type v) <+> pp_value (typed.value v)
| (instruction.ret_void) => text "ret void"
| (instruction.arith op x y) =>
    pp_arith_op op <+> pp_type (typed.type x) <+> pp_value (typed.value x) <> comma <+> pp_value y
| (instruction.bit op x y) =>
    pp_bit_op op <+> pp_type (typed.type x) <+> pp_value (typed.value x) <> comma <+> pp_value y
| (instruction.conv op x ty) =>
    pp_conv_op op <+> pp_type (typed.type x) <+> pp_value (typed.value x) <+> text "to" <+> pp_type ty
| (instruction.call tailcall ty f args) => pp_call tailcall ty f args.toList
| (instruction.alloca tp len align) => pp_alloca tp len align
| (instruction.load ptr ord align) => pp_load ptr ord align
| (instruction.store val ptr align) => pp_store val ptr align
| (instruction.icmp op x y) =>
    text "icmp" <+> pp_icmp_op op <+>
    pp_type (typed.type x) <+> pp_value (typed.value x) <> comma <+>
    pp_value y
| (instruction.fcmp op x y) =>
    text "fcmp" <+> pp_fcmp_op op <+>
    pp_type (typed.type x) <+> pp_value (typed.value x) <> comma <+>
    pp_value y
| (instruction.phi ty vls) =>
    text "phi" <+> pp_type ty <+> commas (List.map pp_phi_arg vls.toList)
| (instruction.gep bounds base args) => pp_gep bounds base args.toList
| (instruction.select cond x y) =>
    text "select" <+>
    pp_type (typed.type cond) <+> pp_value (typed.value cond) <> comma <+>
    pp_type (typed.type x) <+> pp_value (typed.value x) <> comma <+>
    pp_type (typed.type x) <+> pp_value y
| (instruction.extract_value v i) =>
    text "extractvalue" <+>
    pp_type (typed.type v) <+> pp_value (typed.value v) <> comma <+>
    commas (List.map nat i)
| (instruction.insert_value v e i) =>
    text "insertvalue" <+>
    pp_type (typed.type v) <+> pp_value (typed.value v) <> comma <+>
    pp_type (typed.type e) <+> pp_value (typed.value e) <> comma <+>
    commas (List.map nat i)
| (instruction.extract_elt v i) =>
    text "extractelement" <+>
    pp_type (typed.type v) <+> pp_value (typed.value v) <> comma <+>
    pp_vector_index i
| (instruction.insert_elt v e i) =>
    text "insertelement" <+>
    pp_type (typed.type v) <+> pp_value (typed.value v) <> comma <+>
    pp_type (typed.type e) <+> pp_value (typed.value e) <> comma <+>
    pp_vector_index i
| (instruction.shuffle_vector a b m) =>
    text "shufflevector" <+>
    pp_type (typed.type a) <+> pp_value (typed.value a) <> comma <+>
    pp_type (typed.type a) <+> pp_value b <> comma <+>
    pp_type (typed.type m) <+> pp_value (typed.value m)
| (instruction.jump l) =>
    text "jump" <+> pp_typed_label l
| (instruction.br cond thn els) =>
    text "br" <+>
    pp_type (typed.type cond) <+> pp_value (typed.value cond) <> comma <+>
    pp_typed_label thn <> comma <+>
    pp_typed_label els
| (instruction.invoke tp f args to uw) =>
    pp_invoke tp f args to uw
| (instruction.comment str) =>
    text ";" <> text str
| (instruction.unreachable) =>
    text "unreachable"
| (instruction.unwind) =>
    text "unwind"
| (instruction.va_arg v tp) =>
    text "va_arg" <+>
    pp_type (typed.type v) <+> pp_value (typed.value v) <> comma <+>
    pp_type tp
| (instruction.indirect_br d ls) =>
    text "indirectbr" <+>
    pp_type (typed.type d) <+> pp_value (typed.value d) <> comma <+>
    commas (List.map pp_typed_label ls)
| (instruction.switch c d ls) =>
    text "switch" <+>
    pp_type (typed.type c) <+> pp_value (typed.value c) <> comma <+>
    pp_typed_label d <+>
    brackets (hcat (List.map (pp_switch_entry (typed.type c)) ls))
| (instruction.landing_pad ty mfn c cs) =>
    text "landingpad" <+> pp_type ty <>
    pp_opt (λv => text " personality" <+> pp_type (typed.type v) <+> pp_value (typed.value v)) mfn <+>
    pp_clauses c cs
| (instruction.resume v) =>
    text "resume" <+>
    pp_type (typed.type v) <+> pp_value (typed.value v)
.


def pp_stmt (s:stmt) : doc :=
  text "    " <>
  match s.assign with
  | none => (pp_instr s.instr)
  | (some i) => pp_ident i <+> text "=" <+> pp_instr s.instr
   --  <>   pp_attached_metadata s.metadata
.

def pp_basic_block (bb:basic_block) : doc :=
  vcat ([ pp_opt (λl => pp_label l <> text ":") bb.label ] ++ List.map pp_stmt bb.stmts.toList)
.

def pp_comdat_name (nm:String) : doc :=
  text "comdat" <> parens (text "$" <> text nm)
.

def pp_fun_attr : fun_attr → doc
| (fun_attr.align_stack w)  => text "alignstack" <> parens (nat w)
| fun_attr.alwaysinline     => text "alwaysinline"
| fun_attr.builtin          => text "builtin"
| fun_attr.cold             => text "cold"
| fun_attr.inlinehint       => text "inlinehint"
| fun_attr.jumptable        => text "jumptable"
| fun_attr.minsize          => text "minsize"
| fun_attr.naked            => text "naked"
| fun_attr.nobuiltin        => text "nobuiltin"
| fun_attr.noduplicate      => text "noduplicate"
| fun_attr.noimplicitfloat  => text "noimplicitfloat"
| fun_attr.noinline         => text "noinline"
| fun_attr.nonlazybind      => text "nonlazybind"
| fun_attr.noredzone        => text "noredzone"
| fun_attr.noreturn         => text "noreturn"
| fun_attr.nounwind         => text "nounwind"
| fun_attr.optnone          => text "optnone"
| fun_attr.optsize          => text "optsize"
| fun_attr.readnone         => text "readnone"
| fun_attr.readonly         => text "readonly"
| fun_attr.returns_twice    => text "returns_twice"
| fun_attr.sanitize_address => text "sanitize_address"
| fun_attr.sanitize_memory  => text "sanitize_memory"
| fun_attr.sanitize_thread  => text "sanitize_thread"
| fun_attr.ssp              => text "ssp"
| fun_attr.ssp_req          => text "sspreq"
| fun_attr.ssp_strong       => text "sspstrong"
| fun_attr.uwtable          => text "uwtable"
.

def pp_declare (d:declare) : doc :=
  text "declare" <+>
  pp_type d.ret_type <+>
  pp_symbol d.name <>
  pp_arg_list d.var_args (List.map pp_type d.args.toList) <+>
  hsep (List.map pp_fun_attr d.attrs.toList) <>
  pp_opt (λnm => text " " <> pp_comdat_name nm) d.comdat
.

def pp_linkage : linkage → doc
| linkage.private_linkage              => text "private"
| linkage.linker_private               => text "linker_private"
| linkage.linker_private_weak          => text "linker_private_weak"
| linkage.linker_private_weak_def_auto => text "linker_private_weak_def_auto"
| linkage.internal		       => text "internal"
| linkage.available_externally	       => text "available_externally"
| linkage.linkonce		       => text "linkonce"
| linkage.weak			       => text "weak"
| linkage.common		       => text "common"
| linkage.appending		       => text "appending"
| linkage.extern_weak		       => text "extern_weak"
| linkage.linkonce_odr		       => text "linkonce_odr"
| linkage.weak_odr		       => text "weak_odr"
| linkage.external		       => text "external"
| linkage.dll_import		       => text "dllimport"
| linkage.dll_export		       => text "dllexport"
.

def pp_visibility : visibility → doc
| visibility.default               => text "default"
| visibility.hidden                => text "hidden"
| visibility.protected_visibility  => text "protected"
.

def pp_global_attrs (ga:global_attrs) : doc :=
  pp_opt pp_linkage ga.linkage <+>
  pp_opt pp_visibility ga.visibility <+>
  (if ga.const then text "const" else text "global")
.

def pp_global (g:global) : doc :=
  pp_symbol g.sym <+> text "=" <+>
  pp_global_attrs g.attrs <+>
  pp_type g.type <+>
  pp_opt pp_value g.value <>
  pp_align g.align
  -- <> pp_attached_metadata g.metadata
.

def pp_global_alias (ga:global_alias) : doc :=
  pp_symbol ga.name <+> text "=" <+>
  (match ga.target with
   | (value.symbol _) => pp_type ga.type <> text " "
   | _ => empty
  ) <>
  pp_value ga.target
.

def pp_type_decl_body : type_decl_body -> doc
| type_decl_body.opaque  => text "opaque"
| type_decl_body.defn tp => pp_type tp
.

def pp_type_decl (t:type_decl) : doc :=
  text "%" <> text t.name <+> text "= type" <+> pp_type_decl_body t.decl
.

def pp_gc (x:GC) : doc := pp_string_literal x.gc
.

def pp_define (d:define) : doc :=
  text "define" <+>
  pp_opt pp_linkage d.linkage <+>
  pp_type d.ret_type <+>
  pp_symbol d.name <>
  pp_arg_list d.var_args (List.map (λa => pp_type (typed.type a) <+> pp_ident (typed.value a)) d.args.toList) <+>
  hsep (List.map pp_fun_attr d.attrs.toList) <>
  pp_opt (λs => text " section" <+> pp_string_literal s) d.sec <>
  pp_opt (λg => text " gc" <+> pp_gc g) d.gc <+>
  -- pp_mds d.metadata <+>
  vcat ([ text "{" ] ++ List.map pp_basic_block d.body.toList ++ [ text "}" ])
.

def pp_module (m:module) : doc :=
  pp_opt (λnm => text "source_filename = " <> pp_string_literal nm) m.source_name $+$
  text "target datalayout = " <> dquotes (pp_layout m.data_layout) $+$
  vcat (List.join
  [ List.map pp_type_decl m.types.toList
  , List.map pp_global m.globals.toList
  , List.map pp_global_alias m.aliases.toList
  , List.map pp_declare m.declares.toList
  , List.map pp_define m.defines.toList
  -- , list.map pp_named_md m.named_md
  -- , list.map pp_unnamed_md m.unnamed_md
  -- , list.map pp_comdat m.comdat
  ])
.

end llvm.
