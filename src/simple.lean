import init.data.rbmap
import init.io

import .ast
import .pp

open llvm


def simple_module :=

module.mk
(some "simple.c")
[layout_spec.little_endian, (layout_spec.mangling mangling.mach_o), (layout_spec.align_size align_type.integer 64 64 none), (layout_spec.align_size align_type.float 80 128 none), (layout_spec.native_int_size [8, 16, 32, 64]), (layout_spec.stack_align 128)]
[]
[(named_md.mk "llvm.dbg.cu" [0]), (named_md.mk "llvm.ident" [7]), (named_md.mk "llvm.module.flags" [3, 4, 5, 6])]
[(unnamed_md.mk 0 val_md.debug_info true), (unnamed_md.mk 1 val_md.debug_info false), (unnamed_md.mk 2 (val_md.node []) false), (unnamed_md.mk 3 (val_md.node [(some (val_md.value (typed.mk (llvm_type.prim_type (prim_type.integer 32)) (value.integer 2)))), (some (val_md.string "Dwarf Version")), (some (val_md.value (typed.mk (llvm_type.prim_type (prim_type.integer 32)) (value.integer 4))))]) false), (unnamed_md.mk 4 (val_md.node [(some (val_md.value (typed.mk (llvm_type.prim_type (prim_type.integer 32)) (value.integer 2)))), (some (val_md.string "Debug Info Version")), (some (val_md.value (typed.mk (llvm_type.prim_type (prim_type.integer 32)) (value.integer 3))))]) false), (unnamed_md.mk 5 (val_md.node [(some (val_md.value (typed.mk (llvm_type.prim_type (prim_type.integer 32)) (value.integer 1)))), (some (val_md.string "wchar_size")), (some (val_md.value (typed.mk (llvm_type.prim_type (prim_type.integer 32)) (value.integer 4))))]) false), (unnamed_md.mk 6 (val_md.node [(some (val_md.value (typed.mk (llvm_type.prim_type (prim_type.integer 32)) (value.integer 7)))), (some (val_md.string "PIC Level")), (some (val_md.value (typed.mk (llvm_type.prim_type (prim_type.integer 32)) (value.integer 2))))]) false), (unnamed_md.mk 7 (val_md.node [(some (val_md.string "Apple LLVM version 10.0.0 (clang-1000.10.44.4)"))]) false), (unnamed_md.mk 8 val_md.debug_info true), (unnamed_md.mk 9 val_md.debug_info false), (unnamed_md.mk 10 val_md.debug_info false), (unnamed_md.mk 11 val_md.debug_info false), (unnamed_md.mk 12 (val_md.node [(some (val_md.ref 11)), (some (val_md.ref 11)), (some (val_md.ref 11))]) false), (unnamed_md.mk 13 val_md.debug_info true), (unnamed_md.mk 14 val_md.debug_info false), (unnamed_md.mk 15 val_md.debug_info false), (unnamed_md.mk 16 (val_md.node [(some (val_md.ref 14)), (some (val_md.ref 15))]) false), (unnamed_md.mk 17 val_md.debug_info true)]
(strmap_empty selection_kind)
[]
[(declare.mk
    (llvm_type.prim_type prim_type.void)
    (symbol.mk "llvm.dbg.value")
    [(llvm_type.prim_type prim_type.metadata), (llvm_type.prim_type prim_type.metadata), (llvm_type.prim_type prim_type.metadata)]
    false
    []
    none)]
[(define.mk
    none
    (llvm_type.prim_type (prim_type.integer 32))
    (symbol.mk "add")
    [(typed.mk (llvm_type.prim_type (prim_type.integer 32)) (ident.mk "0")), (typed.mk (llvm_type.prim_type (prim_type.integer 32)) (ident.mk "1"))]
    false
    []
    none
    none
    [ (basic_block.mk (some (block_label.anon 2))
         [ (stmt.mk none (instruction.call false (llvm_type.ptr_to (llvm_type.fun_ty (llvm_type.prim_type prim_type.void) [(llvm_type.prim_type prim_type.metadata), (llvm_type.prim_type prim_type.metadata), (llvm_type.prim_type prim_type.metadata)] false)) (value.symbol (symbol.mk "llvm.dbg.value")) [(typed.mk (llvm_type.prim_type prim_type.metadata) (value.md (val_md.value (typed.mk (llvm_type.prim_type (prim_type.integer 32)) (value.ident (ident.mk "0")))))), (typed.mk (llvm_type.prim_type prim_type.metadata) (value.md val_md.debug_info)), (typed.mk (llvm_type.prim_type prim_type.metadata) (value.md val_md.debug_info))]) [("dbg", (val_md.loc (debug_loc.debug_loc 3 24 (val_md.ref 8) none)))])
         , (stmt.mk none (instruction.call false (llvm_type.ptr_to (llvm_type.fun_ty (llvm_type.prim_type prim_type.void) [(llvm_type.prim_type prim_type.metadata), (llvm_type.prim_type prim_type.metadata), (llvm_type.prim_type prim_type.metadata)] false)) (value.symbol (symbol.mk "llvm.dbg.value")) [(typed.mk (llvm_type.prim_type prim_type.metadata) (value.md (val_md.value (typed.mk (llvm_type.prim_type (prim_type.integer 32)) (value.ident (ident.mk "1")))))), (typed.mk (llvm_type.prim_type prim_type.metadata) (value.md val_md.debug_info)), (typed.mk (llvm_type.prim_type prim_type.metadata) (value.md val_md.debug_info))]) [("dbg", (val_md.loc (debug_loc.debug_loc 3 36 (val_md.ref 8) none)))])
         , (stmt.mk (some (ident.mk "3")) (instruction.bit (bit_op.shl false false) (typed.mk (llvm_type.prim_type (prim_type.integer 32)) (value.ident (ident.mk "1"))) (value.integer 1)) [("dbg", (val_md.loc (debug_loc.debug_loc 4 17 (val_md.ref 8) none)))])
         , (stmt.mk (some (ident.mk "4")) (instruction.arith (arith_op.add false false) (typed.mk (llvm_type.prim_type (prim_type.integer 32)) (value.ident (ident.mk "3"))) (value.ident (ident.mk "0"))) [("dbg", (val_md.loc (debug_loc.debug_loc 4 13 (val_md.ref 8) none)))])
         , (stmt.mk none (instruction.ret (typed.mk (llvm_type.prim_type (prim_type.integer 32)) (value.ident (ident.mk "4")))) [("dbg", (val_md.loc (debug_loc.debug_loc 4 3 (val_md.ref 8) none)))])
         ])
    ]
    (strmap_empty val_md)
    none)]
[]
[]

def main : IO Unit :=
  IO.println (pp.render (pp_module simple_module))

