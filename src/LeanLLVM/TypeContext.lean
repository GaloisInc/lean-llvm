import Init.Control.Functor
import Init.Control.Applicative
import Init.Control.Monad
import Init.Data.Array
import Init.Data.List
import Std.Data.RBMap

import LeanLLVM.AST
import LeanLLVM.Alignment
import LeanLLVM.DataLayout

open Std (RBMap)

namespace LLVM

structure fieldInfo (α:Type) :=
(value   : α)
(offset  : Nat) -- offset from the beginning of the struct
(padding : Nat) -- number of padding bytes following this field

structure structInfo (α:Type) :=
(fields : Array (fieldInfo α))
(size : Nat)
(alignment : Alignment)

mutual 

inductive sym_type : Type
  | mem_type : mem_type → sym_type
  | ty_alias : String → sym_type
  | fun_type : fun_decl → sym_type
  | void     : sym_type
  | opaque   : sym_type
  | unsupported : LLVMType → sym_type

inductive mem_type : Type
  | ptr      : sym_type → mem_type
  | int      : Nat → mem_type
  | array    : Nat → mem_type → mem_type
  | vector   : Nat → mem_type → mem_type
  | struct   : structInfo mem_type → mem_type
  | metadata : mem_type

--  | float    :
--  | double   :
--  | x86_fp80 :

inductive fun_decl : Type
  | fun_decl : ∀(ret : Option mem_type) (args : List mem_type) (varargs : Bool), fun_decl

end

namespace mem_type

partial def szAndAlign (dl:DataLayout) : mem_type → Nat × Alignment
| ptr _            => (dl.ptrSize, dl.ptrAlign)
| int n            => ((n+7)/8, computeIntegerAlignment dl.integerInfo n)
| array n tp       =>
  let (sz,a) := szAndAlign dl tp
  (n * padToAlignment sz a, a)
| vector n tp      =>
  let (sz,a) := szAndAlign dl tp
  let vsz := n * sz;
  (vsz, computeVectorAlignment dl.vectorInfo (8*vsz))
| struct si        => (si.size, si.alignment)
| metadata         => (0, unaligned)

def sz (dl:DataLayout) (mt:mem_type) : Nat := (szAndAlign dl mt).1

def alignment (dl:DataLayout) (mt:mem_type) : Alignment := (szAndAlign dl mt).2

end mem_type

def compute_struct_info_aux (dl:DataLayout)
: Nat → Alignment → Array (fieldInfo mem_type) → mem_type → List mem_type → structInfo mem_type
| sz, a, fs, t, [] =>
  let sz' := sz.add (t.sz dl);
  let a'  := maxAlignment a (t.alignment dl);
  let fs' := fs.push { value := t, offset := sz, padding := 0 };
  { fields := fs', size := sz', alignment := a' }

| sz, a, fs, t, t'::ts =>
  let ⟨tsz,talign⟩ := mem_type.szAndAlign dl t;
  let tend := sz + tsz;
  let sz'  := padToAlignment tend (t'.alignment dl);
  let a'   := maxAlignment a talign;
  let fs'  := fs.push { value := t, offset := sz, padding := sz' - tend };
  compute_struct_info_aux dl sz' a' fs' t' ts

def compute_struct_info (dl:DataLayout) : List mem_type -> structInfo mem_type
| []    => { fields := Array.empty, size := 0, alignment := unaligned }
| t::ts => compute_struct_info_aux dl 0 dl.aggregateAlignment Array.empty t ts

def compute_packed_struct_info_aux (dl:DataLayout)
: Nat → Array (fieldInfo mem_type) → List mem_type -> structInfo mem_type
| sz, fs, [] => { fields := fs, size := sz, alignment := unaligned }
| sz, fs, t::ts =>
  let sz' := sz.add (t.sz dl);
  let fs' := fs.push { value := t, offset := sz, padding := 0 };
  compute_packed_struct_info_aux dl sz' fs' ts

def compute_packed_struct_info (dl:DataLayout) : List mem_type → structInfo mem_type :=
  compute_packed_struct_info_aux dl 0 Array.empty

instance sym_type.inh : Inhabited sym_type := ⟨sym_type.void⟩
instance mem_type.inh : Inhabited mem_type := ⟨mem_type.ptr sym_type.void⟩

def lookup_td (tds:Array TypeDecl) (i:String) : Option TypeDeclBody :=
  Option.map TypeDecl.decl
  (tds.find? (λtd =>
   match decEq td.name i with
   | Decidable.isTrue _  => true
   | Decidable.isFalse _ => false
   ))


partial def lift_sym_type (dl:DataLayout) (lift_mem_type : LLVMType → Option mem_type) (tds:Array TypeDecl)
: LLVMType → sym_type
| t@(LLVMType.prim pt) =>
  match pt with
  | PrimType.label        => sym_type.unsupported t
  | PrimType.token        => sym_type.unsupported t
  | PrimType.void         => sym_type.void
  | PrimType.integer n    => sym_type.mem_type (mem_type.int n)
  | PrimType.metadata     => sym_type.mem_type mem_type.metadata
  | PrimType.floatType _  => sym_type.unsupported t
  | PrimType.x86mmx       => sym_type.unsupported t

| LLVMType.alias i => sym_type.ty_alias i

| t@(LLVMType.funType ret args va) =>
  let mt : Option fun_decl := (do
       lift_mem_type ret >>= λret' =>
         List.mapM lift_mem_type args.toList >>= λargs' =>
         pure (fun_decl.fun_decl ret' args' va));
  match mt with
  | none => sym_type.unsupported t
  | some t' => sym_type.fun_type t'

| LLVMType.ptr t' => sym_type.mem_type (mem_type.ptr (lift_sym_type dl lift_mem_type tds t'))

| t@(LLVMType.array n tp) =>
  match lift_mem_type tp with
  | none   => sym_type.unsupported t
  | some m => sym_type.mem_type (mem_type.array n m)

| t@(LLVMType.vector n tp) =>
  match lift_mem_type tp with
  | none   => sym_type.unsupported t
  | some m => sym_type.mem_type (mem_type.vector n m)

| t@(LLVMType.struct false fs) =>
  let mt : Option (List mem_type) := List.mapM lift_mem_type fs.toList;
  match mt with
  | none => sym_type.unsupported t
  | some t' => 
    sym_type.mem_type $ mem_type.struct $ compute_struct_info dl t'

| t@(LLVMType.struct true fs) =>
  let mt : Option (List mem_type) := List.mapM lift_mem_type fs.toList;
  match mt with
  | none => sym_type.unsupported t
  | some t' => 
    sym_type.mem_type $ mem_type.struct $ compute_packed_struct_info dl t'


partial def lift_mem_type (dl:DataLayout) (tds:Array TypeDecl) : LLVMType → Option mem_type
| LLVMType.prim pt =>
  match pt with
  | PrimType.integer n   => some (mem_type.int n)
  | PrimType.metadata    => some mem_type.metadata
  | PrimType.label       => none
  | PrimType.token       => none
  | PrimType.void        => none
  | PrimType.floatType _ => none
  | PrimType.x86mmx      => none
| LLVMType.ptr tp        => some (mem_type.ptr (lift_sym_type dl (lift_mem_type dl tds) tds tp))
| LLVMType.alias i       => do 
  let b ← lookup_td tds i
  match b with
  | TypeDeclBody.opaque   => none
  | TypeDeclBody.defn tp' => lift_mem_type dl tds tp'
| LLVMType.struct false fs  => do
  let fs' ← fs.toList.mapM (lift_mem_type dl tds)
  mem_type.struct $ compute_struct_info dl fs'
| LLVMType.struct true fs   => do
  let fs' ← fs.toList.mapM (lift_mem_type dl tds)
  mem_type.struct $ compute_packed_struct_info dl fs'
| LLVMType.array n tp       => mem_type.array n <$> lift_mem_type dl tds tp
| LLVMType.vector n tp      => mem_type.vector n <$> lift_mem_type dl tds tp
| LLVMType.funType _ _ _     => none

def sym_type_to_mem_type (dl:DataLayout) (tds:Array TypeDecl) : sym_type -> Option mem_type
| sym_type.mem_type mt => some mt
| sym_type.ty_alias i  => do
  let b ← lookup_td tds i
  match b with
  | TypeDeclBody.opaque => none
  | TypeDeclBody.defn tp => lift_mem_type dl tds tp
| _ => none

end LLVM
