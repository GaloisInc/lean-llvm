import Init.Data.List
import Init.Data.RBMap
import Init.Data.String

import LeanLLVM.AST

namespace LLVM

structure Doc : Type := (compose : String → String).

class HasPP (α:Type _) := (pp : α → Doc)

export HasPP (pp)

namespace Doc

reserve infixl ` <+> `: 50
reserve infixl ` $+$ `: 60

def text (x:String) := Doc.mk (fun z => x ++ z).
def render (x:Doc) : String := x.compose "".
def toDoc {a:Type} [HasToString a] : a → Doc := text ∘ toString.

def empty : Doc := Doc.mk id.
def next_to (x y : Doc) : Doc := Doc.mk (x.compose ∘ y.compose).

reserve infixl ` <> `: 50
infix <>  := next_to.

instance : Inhabited Doc := ⟨empty⟩

def spacesep (x y:Doc) : Doc  := x <> text " " <> y
def linesep (x y:Doc)  : Doc  := x <> text "\n" <> y

infix <+> := spacesep
infix $+$ := linesep

def hcat (xs:List Doc) : Doc := List.foldr next_to empty xs.
def hsep (xs:List Doc) : Doc := List.foldr spacesep empty xs.
def vcat (xs:List Doc) : Doc := List.foldr linesep empty xs.

def punctuate (p:Doc) : List Doc → List Doc
| [ ]     => []
| (x::xs) => x :: (List.foldr (fun a b => p :: a :: b) [] xs)

def nat : Nat → Doc := text ∘ toString
def int : Int → Doc := text ∘ toString

def pp_nonzero : Nat → Doc
| Nat.zero => empty
| n => nat n

def surrounding (first last : String) (x:Doc) : Doc :=
  text first <> x <> text last

def parens   : Doc → Doc := surrounding "(" ")"
def brackets : Doc → Doc := surrounding "[" "]"
def angles   : Doc → Doc := surrounding "<" ">"
def braces   : Doc → Doc := surrounding "{" "}"

def comma : Doc := text ","
def commas : List Doc → Doc := hcat ∘ punctuate comma

def quotes : Doc → Doc := surrounding "\'" "\'"
def dquotes : Doc → Doc := surrounding "\"" "\""

def pp_opt {A:Type} (f:A → Doc) : Option A → Doc
| some a => f a
| none   => empty

end Doc
end LLVM

namespace LLVM
open Doc

namespace AlignType

def ppDoc : AlignType → Doc
| integer => text "i"
| vector  => text "v"
| float   => text "f"

instance : HasPP AlignType := ⟨ppDoc⟩

end AlignType

namespace Mangling

def ppDoc : Mangling → Doc
| elf => text "e"
| mips => text "m"
| mach_o => text "o"
| windows_coff     => text "w"
| windows_coff_x86 => text "x"

instance : HasPP Mangling := ⟨ppDoc⟩

end Mangling

namespace LayoutSpec

def ppDoc : LayoutSpec → Doc
| endianness Endian.big    => text "E"
| endianness Endian.little => text "e"
| pointerSize addrSpace sz abi pref idx =>
     text "p" <> pp_nonzero addrSpace <> text ":"
              <> nat sz <> text ":"
              <> nat abi <> text ":"
     <> nat pref <> text ":"
     <> pp_opt (λi => text ":" <> nat i) idx
| alignSize tp sz abi pref =>
   pp tp <> nat sz <> text ":" <> nat abi <> pp_opt (λx => text ":" <> nat x) pref
| nativeIntSize szs        => text "n" <> hcat (punctuate (text ":") (List.map nat szs))
| stackAlign n              => text "S" <> nat n
| aggregateAlign abi pref   => text "a:" <> nat abi <> text ":" <> nat pref
| mangling m                 => text "m:" <> pp m
| functionAddressSpace n   => text "P" <> nat n
| stackAlloca n             => text "A" <> nat n

instance : HasPP LayoutSpec := ⟨ppDoc⟩

end LayoutSpec

section LayoutSpec
open LayoutSpec

def pp_layout (xs:List LayoutSpec) : Doc := hcat (punctuate (text "-") (pp <$> xs))

def l1 : List LayoutSpec :=
  [ endianness Endian.big,
    mangling Mangling.mach_o,
    pointerSize 0 64 64 64 none,
    alignSize AlignType.integer 64 64 none,
    alignSize AlignType.float   80 128 none,
    alignSize AlignType.float   64 64 none,
    nativeIntSize [8,16,32,64],
    stackAlign 128
  ]

end LayoutSpec


-- FIXME! We need to handle escaping...
def pp_string_literal : String → Doc := dquotes ∘ text

namespace Ident

def ppDoc : Ident → Doc
| named nm => text "%" <> text nm  -- FIXME! deal with the 'validIdentifier' question
| anon i   => text "%" <> toDoc i

instance : HasPP Ident := ⟨ppDoc⟩

end Ident

namespace Symbol

def ppDoc (n:Symbol) : Doc := text "@" <> text (n.symbol)

instance : HasPP Symbol := ⟨ppDoc⟩

end Symbol

namespace BlockLabel

instance : HasPP BlockLabel := ⟨λl => pp l.label⟩

end BlockLabel

def packed_braces : Doc → Doc := surrounding "<{" "}>"

namespace FloatType

def ppDoc : FloatType → Doc
| half      => text "half"
| float     => text "float"
| double    => text "double"
| fp128     => text "fp128"
| x86FP80  => text "x86_fp80"
| ppcFP128 => text "ppcfp128"

instance : HasPP FloatType := ⟨ppDoc⟩

end FloatType

namespace PrimType

def ppDoc : PrimType → Doc
| label        => text "label"
| token        => text "token"
| void         => text "void"
| x86mmx       => text "x86mmx"
| metadata     => text "metadata"
| floatType f  => pp f
| integer n    => text "i" <> int n

instance : HasPP PrimType := ⟨ppDoc⟩

end PrimType

def pp_arg_list (va:Bool) (xs:List Doc) : Doc :=
  parens (commas (xs ++ if va then [text "..."] else []))

/-
meta def pp_type_tac :=
  `[unfold has_well_founded.r measure inv_image sizeof has_sizeof.sizeof
      llvm_type.sizeof
      at *,
    try { linarith }
   ].
-/

namespace LLVMType

partial def ppDoc : LLVMType → Doc
| prim pt       => pp pt
| alias nm            => text "%" <> text nm
| array len ty        => brackets (int len <+> text "x" <+> ppDoc ty)
| funType ret args va => ppDoc ret <> pp_arg_list va (ppDoc <$> args.toList)
| ptr ty              => ppDoc ty <> text "*"
| struct false ts     => braces (commas (ppDoc <$> ts.toList))
| struct true  ts     => packed_braces (commas (ppDoc <$> ts.toList))
| vector len ty       => angles (int len <+> text "x" <+> ppDoc ty)

instance : HasPP LLVMType := ⟨ppDoc⟩

end LLVMType

namespace Typed

def pp_with {α} (f:α → Doc) (x:Typed α) := pp x.type <+> f x.value

instance {α} [HasPP α] : HasPP (Typed α) := ⟨pp_with pp⟩

end Typed

namespace ConvOp

def ppDoc : ConvOp → Doc
| trunc      => text "trunc"
| zext       => text "zext"
| sext       => text "sext"
| fp_trunc   => text "fptrunc"
| fp_ext     => text "fpext"
| fp_to_ui   => text "fptoui"
| fp_to_si   => text "fptosi"
| ui_to_fp   => text "uitofp"
| si_to_fp   => text "sitofp"
| ptr_to_int => text "ptrtoint"
| int_to_ptr => text "inttoptr"
| bit_cast   => text "bitcast"

instance : HasPP ConvOp := ⟨ppDoc⟩

end ConvOp

def pp_wrap_bits (nuw nsw:Bool) : Doc :=
  (if nuw then text " nuw" else empty) <>
  (if nsw then text " nsw" else empty)

def pp_exact_bit (exact:Bool) : Doc :=
  if exact then text " exact" else empty

namespace ArithOp

def ppDoc : ArithOp → Doc
| add nuw nsw  => text "add" <> pp_wrap_bits nuw nsw
| sub nuw nsw  => text "sub" <> pp_wrap_bits nuw nsw
| mul nuw nsw  => text "mul" <> pp_wrap_bits nuw nsw
| udiv exact   => text "udiv" <> pp_exact_bit exact
| sdiv exact   => text "sdiv" <> pp_exact_bit exact
| urem         => text "urem"
| srem         => text "srem"
| fadd         => text "fadd"
| fsub         => text "fsub"
| fmul         => text "fmul"
| fdiv         => text "fdiv"
| frem         => text "frem"

instance : HasPP ArithOp := ⟨ppDoc⟩

end ArithOp

namespace ICmpOp

def ppDoc : ICmpOp → Doc
| ieq           => text "eq"
| ine           => text "ne"
| iugt          => text "ugt"
| iult          => text "ult"
| iuge          => text "uge"
| iule          => text "ule"
| isgt          => text "sgt"
| islt          => text "slt"
| isge          => text "sge"
| isle          => text "sle"

instance : HasPP ICmpOp := ⟨ppDoc⟩

end ICmpOp

namespace FCmpOp

def ppDoc : FCmpOp → Doc
| ffalse        => text "false"
| ftrue         => text "true"
| foeq          => text "oeq"
| fogt          => text "ogt"
| foge          => text "oge"
| folt          => text "olt"
| fole          => text "ole"
| fone          => text "one"
| ford          => text "ord"
| fueq          => text "ueq"
| fugt          => text "ugt"
| fuge          => text "uge"
| fult          => text "ult"
| fule          => text "ule"
| fune          => text "une"
| funo          => text "uno"

instance : HasPP FCmpOp := ⟨ppDoc⟩

end FCmpOp

namespace BitOp

def ppDoc : BitOp → Doc
| shl nuw nsw    => text "shl" <> pp_wrap_bits nuw nsw
| lshr exact     => text "lshr" <> pp_exact_bit exact
| ashr exact     => text "ashr" <> pp_exact_bit exact
| and            => text "and"
| or             => text "or"
| xor            => text "xor"

instance : HasPP BitOp := ⟨ppDoc⟩

end BitOp


/-
meta def pp_val_tac :=
  `[unfold has_well_founded.r measure inv_image sized.psum_size sizeof has_sizeof.sizeof
      typed.sizeof const_expr.sizeof value.sizeof val_md.sizeof debug_loc.sizeof option.sizeof
      at *,
    repeat { rw llvm.typed.sizeof_spec' at *, unfold sizeof has_sizeof.sizeof at * },
    try { linarith }
   ].
-/

section pp
open ConstExpr

def pp_const_expr (pp_value : Value → Doc) : ConstExpr → Doc
| select cond x y =>
     text "select" <+> cond.pp_with pp_value <+> text ","
                   <+> x.pp_with pp_value <+> text ","
                   <+> pp_value y.value
| gep inbounds inrange tp vs =>
    text "getelementpointer"
    <+> (if inbounds then text "inbounds " else empty)
    <> parens (pp tp <> comma <+> commas (vs.toList.map (λv => v.pp_with pp_value)))
| conv op x tp => pp op <+> parens (x.pp_with pp_value <+> text "to" <+> pp tp)
| arith op x y => pp op <+> parens (x.pp_with pp_value <> comma <+> pp_value y)
| fcmp op x y =>
    text "fcmp"
      <+> pp op
      <+> parens (x.pp_with pp_value <> comma <+> y.pp_with pp_value)
| icmp op x y =>
    text "icmp" <+> pp op
                <+> parens (x.pp_with pp_value <> comma <+> y.pp_with pp_value)
| bit op x y =>
    pp op <+> parens (x.pp_with pp_value <> comma <+> pp_value y)
| blockAddr sym lab =>
  text "blockaddress" <+> parens (pp sym <> comma <+> pp lab)

open DebugLoc

def pp_debug_loc (pp_md : ValMD → Doc) : DebugLoc → Doc
| debugLoc line col scope none =>
    text "!DILocation" <> parens (commas
    [ text "line:"   <+> int line
    , text "column:" <+> int col
    , text "scope:"  <+> pp_md scope
    ])
| debugLoc line col scope (some ia) =>
    text "!DILocation" <> parens (commas
    [ text "line:"      <+> int line
    , text "column:"    <+> int col
    , text "scope:"     <+> pp_md scope
    , text "inlinedAt:" <+> pp_md ia
    ])

open ValMD

partial def pp_md (pp_value : Value → Doc) : ValMD → Doc
| string s  => text "!" <> pp_string_literal s
| value x   => x.pp_with pp_value
| ref i     => text "!" <> int i
| node xs   =>
  text "!" <> braces (commas (xs.map (λ mx => Option.casesOn mx (text "null") pp_md)))
| loc l    => pp_debug_loc pp_md l
| debugInfo => empty

open Value

partial def pp_value : Value → Doc
| null             => text "null"
| undef            => text "undef"
| zeroInit         => text "0"
| integer i        => toDoc i
| Value.bool b     => toDoc b
| string s         => text "c" <> pp_string_literal s
| ident n          => pp n
| symbol n         => pp n
| constExpr e      => pp_const_expr pp_value e
| label l          => pp l
| array tp vs      => brackets (commas (vs.toList.map (λv => pp tp <+> pp_value v)))
| vector tp vs     => angles (commas (vs.toList.map (λv => pp tp <+> pp_value v)))
| struct fs        => braces (commas (fs.toList.map (λf => f.pp_with pp_value)))
| packedStruct fs  => packed_braces (commas (fs.toList.map (λf => f.pp_with pp_value)))
| md d             => pp_md pp_value d

instance : HasPP Value := ⟨pp_value⟩

end pp

namespace AtomicOrdering

protected def pp : AtomicOrdering → Doc
| unordered => text "unordered"
| monotonic => text "monotonic"
| acquire   => text "acquire"
| release   => text "release"
| acqRel   => text "acq_rel"
| seqCst   => text "seq_cst"

instance : HasPP AtomicOrdering := ⟨AtomicOrdering.pp⟩

end AtomicOrdering

def pp_align : Option Nat → Doc
| some a => comma <+> text "align" <+> nat a
| none   => empty

def pp_scope : Option String → Doc :=
  pp_opt (λnm => text "syncscope" <> parens (pp_string_literal nm))

def pp_call (tailcall:Bool) (mty:Option LLVMType) (f:Value) (args:List (Typed Value)) : Doc :=
  (if tailcall then text "tail call" else text "call") <+>
  match mty with
  | none => text "void"
  | some ty => pp ty <+> pp f <+> parens (commas (args.map pp))

def pp_alloca (tp:LLVMType) (len:Option (Typed Value)) (align:Option Nat) : Doc :=
  text "alloca" <+> pp tp <>
  pp_opt (λv => comma <+> pp v) len <>
  pp_align align

def pp_load (ptr:Typed Value) (ord:Option AtomicOrdering) (align : Option Nat) : Doc :=
  text "load" <>
  (if Option.isSome ord then text " atomic" else empty) <+>
  pp ptr <>
  pp_opt pp ord <>
  pp_opt pp_align align

def pp_store (val:Typed Value) (ptr:Typed Value) (align:Option Nat) : Doc :=
  text "store" <+> pp val <> comma <+> pp ptr <> pp_align align

def pp_phi_arg (vl:Value × BlockLabel) : Doc :=
  brackets (pp vl.1 <> comma <+> pp vl.2)

def pp_gep (bounds:Bool) (base:Typed Value) (xs:List (Typed Value)) : Doc :=
  text "getelementpointer" <>
  (if bounds then text " inbounds" else empty) <+>
  commas (pp base :: xs.map pp)

def pp_vector_index (v:Value) : Doc := text "i" <> int 32 <+> pp v

def pp_typed_label (l:BlockLabel) : Doc := text "label" <+> pp l

def pp_invoke (ty:LLVMType) (f:Value) (args:List (Typed Value)) (to:BlockLabel) (uw:BlockLabel) : Doc :=
  text "invoke" <+> pp ty <+> pp f <>
  parens (commas (pp <$> args)) <+>
  text "to label" <+> pp to <+>
  text "unwind label" <+> pp uw

def pp_clause : (clause × Typed Value)→ Doc
| (clause.catch, v)  => text "catch"  <+> pp v
| (clause.filter, v) => text "filter" <+> pp v

def pp_clauses (is_cleanup:Bool) (cs:List (clause × Typed Value) ): Doc :=
  hsep ((if is_cleanup then [text "cleanup"] else []) ++ cs.map pp_clause)

def pp_switch_entry (ty:LLVMType) : (Nat × BlockLabel) → Doc
| (i, l) => pp ty <+> nat i <> comma <+> pp l

namespace Instruction

protected
def ppDoc : Instruction → Doc
| ret v => text "ret" <+> pp v
| retVoid => text "ret void"
| arith op x y => pp op <+> pp x <> comma <+> pp y
| bit op x y   => pp op <+> pp x <> comma <+> pp y
| conv op x ty => pp op <+> pp x <+> text "to" <+> pp ty
| call tailcall ty f args => pp_call tailcall ty f args.toList
| alloca tp len align => pp_alloca tp len align
| load ptr ord align => pp_load ptr ord align
| store val ptr align => pp_store val ptr align
| icmp op x y => text "icmp" <+> pp op <+> pp x <> comma <+> pp y
| fcmp op x y => text "fcmp" <+> pp op <+> pp x <> comma <+> pp y
| phi ty vls  => text "phi" <+> pp ty <+> commas (vls.toList.map pp_phi_arg)
| gep bounds base args => pp_gep bounds base args.toList
| select cond x y =>
    text "select" <+> pp cond <> comma <+> pp x <> comma <+> pp x.type <+> pp y
| extractvalue v i =>
    text "extractvalue" <+> pp v <> comma <+> commas (i.map nat)
| insertvalue v e i =>
    text "insertvalue" <+> pp v <> comma <+> pp e <> comma <+> commas (nat <$> i)
| extractelement v i =>
    text "extractelement" <+> pp v <> comma <+> pp_vector_index i
| insertelement v e i =>
    text "insertelement" <+> pp v <> comma <+> pp e <> comma <+> pp_vector_index i
| shufflevector a b m =>
    text "shufflevector" <+> pp a <> comma <+> pp a.type <+> pp b <> comma <+> pp m
| jump l =>
    text "jump label" <+> pp l
| br cond thn els =>
    text "br" <+> pp cond <> comma <+>
    text "label" <+> pp thn <> comma <+> text "label" <+> pp els
| invoke tp f args to uw => pp_invoke tp f args to uw
| comment str =>
    text ";" <> text str
| unreachable =>
    text "unreachable"
| unwind => text "unwind"
| va_arg v tp => text "va_arg" <+> pp v <> comma <+> pp tp
| indirectbr d ls =>
    text "indirectbr" <+> pp d <> comma <+> commas (pp_typed_label <$> ls)
| switch c d ls =>
    text "switch" <+> pp c <> comma <+>
    pp_typed_label d <+>
    brackets (hcat (pp_switch_entry c.type <$> ls))
| landingpad ty mfn c cs =>
    text "landingpad" <+> pp ty <>
    pp_opt (λv => text " personality" <+> pp v) mfn <+>
    pp_clauses c cs
| resume v => text "resume" <+> pp v

instance : HasPP Instruction := ⟨Instruction.ppDoc⟩

end Instruction

namespace Stmt

def ppDoc (s:Stmt) : Doc :=
  text "    " <>
  match s.assign with
  | none => pp s.instr
  | some i => pp i <+> text "=" <+> pp s.instr
   --  <>   pp_attached_metadata s.metadata

instance : HasPP Stmt := ⟨ppDoc⟩

end Stmt

namespace BasicBlock

def ppDoc (bb:BasicBlock) := vcat ([ pp bb.label <> text ":" ] ++ pp <$> bb.stmts.toList)

instance : HasPP BasicBlock := ⟨ppDoc⟩

end BasicBlock

def pp_comdat_name (nm:String) : Doc :=
  text "comdat" <> parens (text "$" <> text nm)

namespace FunAttr

protected def pp : FunAttr → Doc
| align_stack w    => text "alignstack" <> parens (nat w)
| alwaysinline     => text "alwaysinline"
| builtin          => text "builtin"
| cold             => text "cold"
| inlinehint       => text "inlinehint"
| jumptable        => text "jumptable"
| minsize          => text "minsize"
| naked            => text "naked"
| nobuiltin        => text "nobuiltin"
| noduplicate      => text "noduplicate"
| noimplicitfloat  => text "noimplicitfloat"
| noinline         => text "noinline"
| nonlazybind      => text "nonlazybind"
| noredzone        => text "noredzone"
| noreturn         => text "noreturn"
| nounwind         => text "nounwind"
| optnone          => text "optnone"
| optsize          => text "optsize"
| readnone         => text "readnone"
| readonly         => text "readonly"
| returns_twice    => text "returns_twice"
| sanitize_address => text "sanitize_address"
| sanitize_memory  => text "sanitize_memory"
| sanitize_thread  => text "sanitize_thread"
| ssp              => text "ssp"
| ssp_req          => text "sspreq"
| ssp_strong       => text "sspstrong"
| uwtable          => text "uwtable"

instance : HasPP FunAttr := ⟨FunAttr.pp⟩

end FunAttr

namespace Declare

def ppDoc (d:Declare) : Doc :=
  text "declare" <+>
  pp d.retType <+>
  pp d.name <>
  pp_arg_list d.varArgs (pp <$> d.args.toList) <+>
  hsep (pp <$> d.attrs.toList) <>
  pp_opt (λnm => text " " <> pp_comdat_name nm) d.comdat

instance : HasPP Declare := ⟨ppDoc⟩

end Declare

namespace Linkage

protected def pp : Linkage → Doc
| private_linkage              => text "private"
| linker_private               => text "linker_private"
| linker_private_weak          => text "linker_private_weak"
| linker_private_weak_def_auto => text "linker_private_weak_def_auto"
| internal		       => text "internal"
| available_externally	       => text "available_externally"
| linkonce		       => text "linkonce"
| weak			       => text "weak"
| common		       => text "common"
| appending		       => text "appending"
| extern_weak		       => text "extern_weak"
| linkonce_odr		       => text "linkonce_odr"
| weak_odr		       => text "weak_odr"
| external		       => text "external"
| dll_import		       => text "dllimport"
| dll_export		       => text "dllexport"

instance : HasPP Linkage := ⟨Linkage.pp⟩

end Linkage

namespace Visibility

def pp : Visibility → Doc
| default               => text "default"
| hidden                => text "hidden"
| protected_visibility  => text "protected"

instance : HasPP Visibility := ⟨Visibility.pp⟩

end Visibility

namespace GlobalAttrs


protected def pp (ga:GlobalAttrs) : Doc :=
  pp_opt pp ga.linkage <+>
  pp_opt pp ga.visibility <+>
  (if ga.const then text "const" else text "global")

instance : HasPP GlobalAttrs := ⟨GlobalAttrs.pp⟩

end GlobalAttrs

namespace Global

def ppDoc (g:Global) : Doc :=
  pp g.sym <+> text "=" <+>
  pp g.attrs <+>
  pp g.type <+>
  pp_opt pp_value g.value <>
  pp_align g.align
  -- <> pp_attached_metadata g.metadata

instance : HasPP Global := ⟨ppDoc⟩

end Global

namespace GlobalAlias

def ppDoc (ga:GlobalAlias) : Doc :=
  let tgtd := match ga.target with
              | Value.symbol _ => pp ga.type <> text " "
              | _ => empty;
  pp ga.name <+> text "=" <+> tgtd <> pp ga.target

instance : HasPP GlobalAlias := ⟨ppDoc⟩

end GlobalAlias

namespace TypeDeclBody

def ppDoc : TypeDeclBody -> Doc
| opaque  => text "opaque"
| defn tp => pp tp

instance : HasPP TypeDeclBody := ⟨TypeDeclBody.ppDoc⟩

end TypeDeclBody

namespace TypeDecl

def ppDoc (t:TypeDecl) := text "%" <> text t.name <+> text "= type" <+> pp t.decl

instance : HasPP TypeDecl := ⟨TypeDecl.ppDoc⟩

end TypeDecl

namespace GC

def ppDoc (x:GC) : Doc := pp_string_literal x.gc

instance : HasPP GC := ⟨ppDoc⟩

end GC

namespace Define

def ppDoc (d:Define) : Doc :=
  text "define" <+>
  pp_opt pp d.linkage <+>
  pp d.retType <+>
  pp d.name <>
  pp_arg_list d.varArgs (pp <$> d.args.toList) <+>
  hsep (pp <$> d.attrs.toList) <>
  pp_opt (λs => text " section" <+> pp_string_literal s) d.sec <>
  pp_opt (λg => text " gc" <+> pp g) d.gc <+>
  -- pp_mds d.metadata <+>
  vcat ([ text "{" ] ++ List.map pp d.body.toList ++ [ text "}" ])

instance : HasPP Define := ⟨ppDoc⟩

end Define

namespace Module

def ppDoc (m:Module) : Doc :=
  pp_opt (λnm => text "source_filename = " <> pp_string_literal nm) m.sourceName $+$
  text "target datalayout = " <> dquotes (pp_layout m.dataLayout) $+$
  vcat (List.join
  [ pp <$> m.types.toList
  , pp <$> m.globals.toList
  , pp <$> m.aliases.toList
  , pp <$> m.declares.toList
  , pp <$> m.defines.toList
  -- , list.map pp_named_md m.named_md
  -- , list.map pp_unnamed_md m.unnamed_md
  -- , list.map pp_comdat m.comdat
  ])

instance : HasPP Module := ⟨ppDoc⟩

end Module

end LLVM

def ppLLVM {α} [LLVM.HasPP α] (a : α) : String := LLVM.Doc.render $ LLVM.HasPP.pp a
