import init.control.functor
import init.control.applicative
import init.control.monad
import init.control.combinators
import init.data.array
import init.data.list
import init.data.rbmap
import .ast
import .alignment
import .data_layout

namespace llvm.

structure fieldInfo (α:Type) :=
  ( value   : α )
  ( offset  : bytes ) -- offset from the beginning of the struct
  ( padding : bytes ). -- number of padding bytes following this field

structure structInfo (α:Type) :=
  ( fields : Array (fieldInfo α) )
  ( size : bytes )
  ( alignment : alignment ).

mutual inductive sym_type, mem_type, fun_decl
with sym_type : Type
  | mem_type : mem_type → sym_type
  | ty_alias : String → sym_type
  | fun_type : fun_decl → sym_type
  | void     : sym_type
  | opaque   : sym_type
  | unsupported : llvm_type → sym_type

with mem_type : Type
  | ptr      : sym_type → mem_type
  | int      : Nat → mem_type
  | array    : Nat → mem_type → mem_type
  | vector   : Nat → mem_type → mem_type
  | struct   : structInfo mem_type → mem_type
  | metadata : mem_type

--  | float    :
--  | double   :
--  | x86_fp80 :

with fun_decl : Type
  | fun_decl : ∀(ret : Option mem_type) (args : List mem_type) (varargs : Bool), fun_decl
.

namespace mem_type.

partial def szAndAlign (dl:data_layout) : mem_type → (bytes × alignment)
| (ptr _)            => (dl.ptr_size, dl.ptr_align)
| (int n)            => (toBytes n, computeIntegerAlignment dl.integer_info n)
| (array n tp)       =>
     let (sz,a) := szAndAlign tp;
     ((padToAlignment sz a).mul n, a)
| (vector n tp)      =>
     let (sz,a) := szAndAlign tp;
     let vsz := sz.mul n;
     (vsz, computeVectorAlignment dl.vector_info vsz.toBits)
| (struct si)        => (si.size, si.alignment)
| metadata           => (bytes.mk 0, noAlignment)
.

@[reducible]
def sz (dl:data_layout) (mt:mem_type) : bytes := (szAndAlign dl mt).1

@[reducible]
def alignment (dl:data_layout) (mt:mem_type) : alignment := (szAndAlign dl mt).2

end mem_type.

def compute_struct_info_aux (dl:data_layout) : bytes → alignment → Array (fieldInfo mem_type) → mem_type → List mem_type → structInfo mem_type
| sz, a, fs, t, [] =>
    let sz' := sz.add (t.sz dl);
    let a'  := maxAlignment a (t.alignment dl);
    let fs' := fs.push { value := t, offset := sz, padding := bytes.mk 0 };
    { fields := fs', size := sz', alignment := a' }

| sz, a, fs, t, t'::ts =>
    let tsz  := t.sz dl;
    let tend := sz.add tsz;
    let sz'  := padToAlignment tend (t'.alignment dl);
    let a'   := maxAlignment a (t.alignment dl);
    let fs'  := fs.push { value := t, offset := sz, padding := bytes.mk (sz'.val - tend.val) };
    compute_struct_info_aux sz' a' fs' t' ts

def compute_struct_info (dl:data_layout) : List mem_type -> structInfo mem_type
| []    => { fields := Array.empty, size := bytes.mk 0, alignment := noAlignment }
| t::ts => compute_struct_info_aux dl (bytes.mk 0) dl.aggregate_alignment Array.empty t ts

def compute_packed_struct_info_aux (dl:data_layout) : bytes → Array (fieldInfo mem_type) → List mem_type -> structInfo mem_type
| sz, fs, [] => { fields := fs, size := sz, alignment := noAlignment }
| sz, fs, t::ts =>
    let sz' := sz.add (t.sz dl);
    let fs' := fs.push { value := t, offset := sz, padding := bytes.mk 0 };
    compute_packed_struct_info_aux sz' fs' ts

def compute_packed_struct_info (dl:data_layout) : List mem_type → structInfo mem_type :=
  compute_packed_struct_info_aux dl (bytes.mk 0) Array.empty

instance sym_type.inh : Inhabited sym_type := ⟨sym_type.void⟩
instance mem_type.inh : Inhabited mem_type := ⟨mem_type.ptr sym_type.void⟩

def lookup_td (tds:Array type_decl) (i:String) : Option type_decl_body :=
  Array.find tds (λtd =>
   match decEq td.name i with
   | Decidable.isTrue _  => some td.decl
   | Decidable.isFalse _ => none
   ).

partial def lift_sym_type (dl:data_layout) (lift_mem_type : llvm_type → Option mem_type) (tds:Array type_decl) : llvm_type → sym_type
| t@(llvm_type.prim_type pt) =>
     (match pt with
     | prim_type.label     => sym_type.unsupported t
     | prim_type.token     => sym_type.unsupported t
     | prim_type.void      => sym_type.void
     | prim_type.integer n => sym_type.mem_type (mem_type.int n)
     | prim_type.metadata  => sym_type.mem_type mem_type.metadata
     | prim_type.float_type _ => sym_type.unsupported t
     | prim_type.x86mmx       => sym_type.unsupported t)

| (llvm_type.alias i) => sym_type.ty_alias i

| t@(llvm_type.fun_ty ret args va) =>
     let mt : Option fun_decl := (do
          lift_mem_type ret >>= λret' =>
            List.mmap lift_mem_type args.toList >>= λargs' =>
            pure (fun_decl.fun_decl ret' args' va));
     Option.casesOn mt (sym_type.unsupported t) sym_type.fun_type

| (llvm_type.ptr_to t') => sym_type.mem_type (mem_type.ptr (lift_sym_type t'))

| t@(llvm_type.array n tp) =>
    (match lift_mem_type tp with
     | none   => sym_type.unsupported t
     | some m => sym_type.mem_type (mem_type.array n m))

| t@(llvm_type.vector n tp) =>
    (match lift_mem_type tp with
     | none   => sym_type.unsupported t
     | some m => sym_type.mem_type (mem_type.vector n m))

| t@(llvm_type.struct false fs) =>
     let mt : Option (List mem_type) := List.mmap lift_mem_type fs.toList;
     Option.casesOn mt (sym_type.unsupported t) (sym_type.mem_type ∘ mem_type.struct ∘ compute_struct_info dl)

| t@(llvm_type.struct true fs) =>
     let mt : Option (List mem_type) := List.mmap lift_mem_type fs.toList;
     Option.casesOn mt (sym_type.unsupported t) (sym_type.mem_type ∘ mem_type.struct ∘ compute_packed_struct_info dl)
.

partial def lift_mem_type (dl:data_layout) (tds:Array type_decl) : llvm_type → Option mem_type
| llvm_type.prim_type pt =>
  match pt with
  | prim_type.integer n      => some (mem_type.int n)
  | prim_type.metadata       => some mem_type.metadata
  | prim_type.label          => none
  | prim_type.token          => none
  | prim_type.void           => none
  | prim_type.float_type _   => none
  | prim_type.x86mmx         => none
| llvm_type.ptr_to tp        => some (mem_type.ptr (lift_sym_type dl lift_mem_type tds tp))
| llvm_type.alias i          =>
     do b <- lookup_td tds i;
        match b with
        | type_decl_body.opaque   => none
        | type_decl_body.defn tp' => lift_mem_type tp'
| llvm_type.struct false fs  => (mem_type.struct ∘ compute_struct_info dl) <$> (List.mmap lift_mem_type fs.toList)
| llvm_type.struct true fs   => (mem_type.struct ∘ compute_packed_struct_info dl) <$> (List.mmap lift_mem_type fs.toList)
| llvm_type.array n tp       => mem_type.array n <$> lift_mem_type tp
| llvm_type.vector n tp      => mem_type.vector n <$> lift_mem_type tp
| llvm_type.fun_ty _ _ _     => none
.

def sym_type_to_mem_type (dl:data_layout) (tds:Array type_decl) : sym_type -> Option mem_type
| sym_type.mem_type mt => some mt
| sym_type.ty_alias i  =>
   do b <- lookup_td tds i;
      match b with
      | type_decl_body.opaque => none
      | type_decl_body.defn tp => lift_mem_type dl tds tp
| _ => none


end llvm.
