import init.control.functor
import init.control.applicative
import init.control.monad
import init.control.combinators
import init.data.list
import init.data.rbmap
import .ast

namespace llvm.

mutual inductive sym_type, mem_type, fun_decl
with sym_type : Type
  | mem_type : mem_type → sym_type
  | ty_alias : ident → sym_type
  | fun_type : fun_decl → sym_type
  | void     : sym_type
  | opaque   : sym_type
  | unsupported : llvm_type → sym_type

with mem_type : Type 
  | ptr      : sym_type → mem_type
  | int      : ℕ → mem_type
  | array    : ℕ → mem_type → mem_type
  | vector   : ℕ → mem_type → mem_type
  | struct   : List mem_type → mem_type
  | packed_struct : List mem_type → mem_type
  | metadata : mem_type

--  | float    : 
--  | double   : 
--  | x86_fp80 : 

with fun_decl : Type
  | fun_decl : Π(ret : Option mem_type) (args : List mem_type) (varargs : Bool), fun_decl
.

instance : Inhabited sym_type := ⟨sym_type.void⟩

def lookup_td : List type_decl → ident → Option llvm_type
| [] _ := none
| (td :: tds) i :=
   match decEq td.name.ident i.ident with
   | Decidable.isTrue _  := some td.value
   | Decidable.isFalse _ := lookup_td tds i
.

partial def lift_sym_type (lift_mem_type : llvm_type → Option mem_type) (tds:List type_decl) : llvm_type → sym_type
| t@(llvm_type.prim_type pt) :=
     (match pt with
     | prim_type.label     := sym_type.unsupported t
     | prim_type.void      := sym_type.void
     | prim_type.integer n := sym_type.mem_type (mem_type.int n)
     | prim_type.metadata  := sym_type.mem_type mem_type.metadata
     | prim_type.float_type _ := sym_type.unsupported t
     | prim_type.x86mmx       := sym_type.unsupported t)

| (llvm_type.alias i) := sym_type.ty_alias i

| t@(llvm_type.fun_ty ret args va) :=
     let mt : Option fun_decl
         := lift_mem_type ret >>= λret',
            List.mmap lift_mem_type args >>= λargs',
            pure (fun_decl.fun_decl ret' args' va)
     in Option.casesOn mt (sym_type.unsupported t) sym_type.fun_type

| (llvm_type.ptr_to t') := sym_type.mem_type (mem_type.ptr (lift_sym_type t'))
            
| t@(llvm_type.array n tp) :=
    (match lift_mem_type tp with
     | none   := sym_type.unsupported t
     | some m := sym_type.mem_type (mem_type.array n m))

| t@(llvm_type.vector n tp) :=
    (match lift_mem_type tp with
     | none   := sym_type.unsupported t
     | some m := sym_type.mem_type (mem_type.vector n m))

| llvm_type.opaque := sym_type.opaque 

| t@(llvm_type.struct fs) :=
     let mt : Option (List mem_type)
            := List.mmap lift_mem_type fs
      in Option.casesOn mt (sym_type.unsupported t) (sym_type.mem_type ∘ mem_type.struct)

| t@(llvm_type.packed_struct fs) :=
     let mt : Option (List mem_type)
            := List.mmap lift_mem_type fs
      in Option.casesOn mt (sym_type.unsupported t) (sym_type.mem_type ∘ mem_type.packed_struct)
.

partial def lift_mem_type (tds:List type_decl) : llvm_type → Option mem_type
| (llvm_type.prim_type pt) :=
   (match pt with
    | prim_type.label      := none
    | prim_type.void       := none
    | prim_type.integer n  := some (mem_type.int n)
    | prim_type.metadata   := some mem_type.metadata
    | prim_type.float_type _ := none
    | prim_type.x86mmx     := none)

| (llvm_type.alias i) := lookup_td tds i >>= lift_mem_type
| llvm_type.opaque := none
| (llvm_type.struct fs) := mem_type.struct <$> (List.mmap lift_mem_type fs)
| (llvm_type.packed_struct fs) := mem_type.packed_struct <$> (List.mmap lift_mem_type fs)
| (llvm_type.ptr_to tp)    := some (mem_type.ptr (lift_sym_type lift_mem_type tds tp))
| (llvm_type.array n tp)   := mem_type.array n <$> lift_mem_type tp
| (llvm_type.vector n tp)  := mem_type.vector n <$> lift_mem_type tp 
| (llvm_type.fun_ty _ _ _) := none
.

end llvm.
