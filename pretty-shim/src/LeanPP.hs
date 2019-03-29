{-# LANGUAGE ViewPatterns #-}

module LeanPP where

import Prelude hiding ((<>))

import Text.PrettyPrint.HughesPJ

import Text.LLVM.AST


app :: String -> [Doc] -> Doc
app constr args = parens (text constr <+> hsep args)

vapp :: String -> [Doc] -> Doc
vapp constr args =
  parens (text constr $$ nest 2 (sep args))

list :: (a -> Doc) -> [a] -> Doc
list f xs = brackets (hsep (punctuate comma (map f xs)))

vert_list :: (a -> Doc) -> [a] -> Doc
vert_list f [] = text "[]"
vert_list f (x:xs) =
  vcat $
    (char '[' <+> f x) :
    (map (\z -> comma <+> f z) xs) ++
    [ char ']' ]

pair :: (a -> Doc) -> (b -> Doc) -> (a,b) -> Doc
pair f g (x, y) = parens (f x <> comma <+> g y)

option :: (a -> Doc) -> Maybe a -> Doc
option _ Nothing  = text "none"
option f (Just x) = app "some" [f x]

bool :: Bool -> Doc
bool True = text "true"
bool False = text "false"

nat :: Integral a => a -> Doc
nat (toInteger -> x)
  | x >= 0    = text (show x)
  | otherwise = error $ "Expected nonnegative literal: " ++ show x


mangling :: Mangling -> Doc
mangling ElfMangling   = text "mangling.elf"
mangling MipsMangling  = text "mangling.mips"
mangling MachOMangling = text "mangling.mach_o"
mangling WindowsCoffMangling = text "mangling.windows_coff"

layout_spec :: LayoutSpec -> Doc
layout_spec x = case x of
  BigEndian -> text "layout_spec.big_endian"
  LittleEndian -> text "layout_spec.little_endian"
  PointerSize addrSpace sz abi pref ->
    app "layout_spec.pointer_size" [nat addrSpace, nat sz, option nat pref, nat sz]
  IntegerSize sz abi pref ->
    app "layout_spec.align_size" [text "align_type.integer", nat sz, nat abi, option nat pref]
  VectorSize sz abi pref ->
    app "layout_spec.align_size" [text "align_type.vector", nat sz, nat abi, option nat pref]
  FloatSize sz abi pref ->
    app "layout_spec.align_size" [text "align_type.float", nat sz, nat abi, option nat pref]
  AggregateSize sz abi pref ->
    app "layout_spec.align_size" [text "align_type.aggregate", nat sz, nat abi, option nat pref]
  NativeIntSize szs ->
    app "layout_spec.native_int_size" [ list nat szs ]
  StackAlign align ->
    app "layout_spec.stack_align" [ nat align ]
  Mangling m ->
    app "layout_spec.mangling" [ mangling m ]
  _ -> error $ "Unsupported layout_spec" ++ show x

data_layout :: DataLayout -> Doc
data_layout = list layout_spec

string_lit :: String -> Doc
string_lit = text . show

ident :: Ident -> Doc
ident (Ident nm) = app "ident.mk" [string_lit nm]

symbol :: Symbol -> Doc
symbol (Symbol nm) = app "symbol.mk" [string_lit nm]

block_label :: BlockLabel -> Doc
block_label (Named nm) = app "block_label.named" [ ident nm ]
block_label (Anon n)   = app "block_label.anon"  [ nat n ]

gc :: GC -> Doc
gc (GC nm) = app "gc.mk" [text nm]

strmap_empty :: String -> Doc
strmap_empty nm = app "strmap_empty" [ text nm ]

float_type :: FloatType -> Doc
float_type ft = case ft of
  Half -> text "float_type.half"
  Float -> text "float_type.float"
  Double -> text "float_type.double"
  Fp128 -> text "float_type.fp128"
  X86_fp80 -> text "float_type.x86_fp80"
  PPC_fp128 -> text "float_type.ppc_fp128"

prim_type :: PrimType -> Doc
prim_type pt = case pt of
  Label -> text "prim_type.label"
  Void -> text "prim_type.void"
  Integer n -> app "prim_type.integer" [ nat n ]
  FloatType ft -> app "prim_type.float_type" [ float_type ft ]
  X86mmx -> text "prim_type.x86mmx"
  Metadata -> text "prim_type.metadata"

llvm_type :: Type -> Doc
llvm_type tp = case tp of
  PrimType pt -> app "llvm_type.prim_type" [ prim_type pt ]
  Alias nm    -> app "llvm_type.alias" [ ident nm ]
  Array n t   -> app "llvm_type.array" [ nat n, llvm_type t ]
  FunTy ret args varargs -> app "llvm_type.fun_ty" [ llvm_type ret, list llvm_type args, bool varargs ]
  PtrTo t -> app "llvm_type.ptr_to" [ llvm_type t ]
  Struct ts -> app "llvm_type.struct" [ list llvm_type ts ]
  PackedStruct ts -> app "llvm_type.packed_struct" [ list llvm_type ts ]
  Vector n t -> app "llvm_type.vector" [ nat n, llvm_type t ]
  Opaque -> text "llvm_type.opaque"

type_decl :: TypeDecl -> Doc
type_decl (TypeDecl nm val) = app "type_decl.mk" [ ident nm, llvm_type val ]

fun_attr :: FunAttr -> Doc
fun_attr attr= case attr of
  AlignStack n    -> app "fun_attr.align_stack" [ nat n ] 
  Alwaysinline    -> text "fun_attr.alwaysinline"
  Builtin         -> text "fun_attr.builtin"
  Cold            -> text "fun_attr.cold"
  Inlinehint      -> text "fun_attr.inlinehint"
  Jumptable       -> text "fun_attr.jumptable"
  Minsize         -> text "fun_attr.minsize"
  Naked           -> text "fun_attr.naked"
  Nobuiltin       -> text "fun_attr.nobuiltin"
  Noduplicate     -> text "fun_attr.noduplicate"
  Noimplicitfloat -> text "fun_attr.noimplicitfloat"
  Noinline        -> text "fun_attr.noinline"
  Nonlazybind     -> text "fun_attr.nonlazybind"
  Noredzone       -> text "fun_attr.noredzone"
  Noreturn        -> text "fun_attr.noreturn"
  Nounwind        -> text "fun_attr.nounwind"
  Optnone         -> text "fun_attr.optnone"
  Optsize         -> text "fun_attr.optsize"
  Readnone        -> text "fun_attr.readnone"
  Readonly        -> text "fun_attr.readonly"
  ReturnsTwice    -> text "fun_attr.returns_twice"
  SanitizeAddress -> text "fun_attr.sanitize_address"
  SanitizeMemory  -> text "fun_attr.sanitize_memory"
  SanitizeThread  -> text "fun_attr.sanitize_thread"
  SSP             -> text "fun_attr.ssp"
  SSPreq          -> text "fun_attr.ssp_req"
  SSPstrong       -> text "fun_attr.ssp_string"
  UWTable         -> text "fun_attr.uwtable"

declare :: Declare -> Doc
declare d =
  vapp "declare.mk"
    [ llvm_type (decRetType d)
    , symbol (decName d)
    , list llvm_type (decArgs d)
    , bool (decVarArgs d)
    , list fun_attr (decAttrs d)
    , option string_lit (decComdat d)
    ]


typed :: (a -> Doc) -> Typed a -> Doc
typed f (Typed tp v) = app "typed.mk" [ llvm_type tp, f v ]

value :: Value -> Doc
value v = case v of
  ValInteger n       -> app "value.integer" [ integer (toInteger n) ]
  ValBool b          -> app "value.bool" [ bool b ]
  ValIdent nm        -> app "value.ident" [ ident nm ]
  ValSymbol nm       -> app "value.symbol" [ symbol nm ]
  ValNull            -> text "value.null"
  ValArray tp xs     -> app "value.array" [ llvm_type tp, list value xs ]
  ValVector tp xs    -> app "value.vector" [ llvm_type tp, list value xs ]
  ValStruct xs       -> app "value.struct" [ list (typed value) xs ]
  ValPackedStruct xs -> app "value.packed_struct" [ list (typed value) xs ]
  ValConstExpr cnst  -> app "value.const_expr" [ const_expr cnst ]
  ValString chrs     -> app "value.string" [ string_lit str ]
    where
    -- FIXME, pretty gross
    str :: String
    str = map (toEnum . fromIntegral) chrs
  ValUndef           -> text "value.undef"
  ValLabel l         -> app "value.label" [ block_label l ]
  ValZeroInit        -> text "value.zero_init"
  ValMd md           -> app "value.md" [ val_md md ]

  ValAsm{} -> unsupported
  ValFloat{} -> unsupported
  ValDouble{} -> unsupported

 where
 unsupported = error $ "shim printer does not support the value: " ++ show v

val_md :: ValMd -> Doc
val_md md = case md of
  ValMdString str -> app "val_md.string" [ string_lit str ]
  ValMdValue v    -> app "val_md.value" [ typed value v ]
  ValMdRef n      -> app "val_md.ref" [ nat n ]
  ValMdNode mds   -> app "val_md.node" [ list (option val_md) mds ]
  ValMdLoc loc    -> app "val_md.loc" [ debug_loc loc ]
  ValMdDebugInfo _di -> text "val_md.debug_info" -- FIXME, ignore the actual info for now

debug_loc :: DebugLoc -> Doc
debug_loc loc =
  app "debug_loc.debug_loc"
    [ nat (dlLine loc)
    , nat (dlCol loc)
    , val_md (dlScope loc)
    , option val_md (dlIA loc)
    ]

icmp_op :: ICmpOp -> Doc
icmp_op op = case op of
  Ieq  -> text "icmp_op.ieq"
  Ine  -> text "icmp_op.ine"
  Iugt -> text "icmp_op.iuge"
  Iuge -> text "icmp_op.iuge"
  Iult -> text "icmp_op.iult"
  Iule -> text "icmp_op.iule"
  Isgt -> text "icmp_op.isgt"
  Isge -> text "icmp_op.isge"
  Islt -> text "icmp_op.islt"
  Isle -> text "icmp_op.isle"

fcmp_op :: FCmpOp -> Doc
fcmp_op op = case op of
  Ffalse -> text "fcmp_op.ffalse"
  Foeq   -> text "fcmp_op.foeq"
  Fogt   -> text "fcmp_op.fogt"
  Foge   -> text "fcmp_op.foge"
  Folt   -> text "fcmp_op.folt"
  Fole   -> text "fcmp_op.fole"
  Fone   -> text "fcmp_op.fone"
  Ford   -> text "fcmp_op.ford"
  Fueq   -> text "fcmp_op.fueq"
  Fugt   -> text "fcmp_op.fugt"
  Fuge   -> text "fcmp_op.fuge"
  Fult   -> text "fcmp_op.fult"
  Fule   -> text "fcmp_op.fule"
  Fune   -> text "fcmp_op.fune"
  Funo   -> text "fcmp_op.funo"
  Ftrue  -> text "fcmp_op.ftrue"


arith_op :: ArithOp -> Doc
arith_op op = case op of
  Add nuw nsw -> app "arith_op.add" [ bool nuw, bool nsw ]
  Sub nuw nsw -> app "arith_op.sub" [ bool nuw, bool nsw ]
  Mul nuw nsw -> app "arith_op.mul" [ bool nuw, bool nsw ]
  UDiv exact  -> app "arith_op.udiv" [ bool exact ]
  SDiv exact  -> app "arith_op.sdiv" [ bool exact ]
  URem        -> text "arith_op.urem"
  SRem        -> text "arith_op.srem"
  FAdd        -> text "arith_op.fadd"
  FSub        -> text "arith_op.fsub"
  FMul        -> text "arith_op.fmul"
  FDiv        -> text "arith_op.fdiv"
  FRem        -> text "arith_op.frem"

bit_op :: BitOp -> Doc
bit_op op = case op of
  Shl nuw nsw -> app "bit_op.shl" [ bool nuw, bool nsw ]
  Lshr exact  -> app "bit_op.lshr" [ bool exact ]
  Ashr exact  -> app "bit_op.ashr" [ bool exact ]
  And         -> text "bit_op.and"
  Or          -> text "bit_op.or"
  Xor         -> text "bit_op.xor"
  

conv_op :: ConvOp -> Doc
conv_op op = case op of
  Trunc    -> text "conv_op.trunc"
  ZExt     -> text "conv_op.zext"
  SExt     -> text "conv_op.sext"
  FpTrunc  -> text "conv_op.fp_trunc"
  FpExt    -> text "conv_op.fp_ext"
  FpToUi   -> text "conv_op.fp_to_ui"
  FpToSi   -> text "conv_op.fp_to_si"
  UiToFp   -> text "conv_op.ui_to_fp"
  SiToFp   -> text "conv_op.si_to_fp"
  PtrToInt -> text "conv_op.ptr_to_int"
  IntToPtr -> text "conv_op.int_to_ptr"
  BitCast  -> text "conv_op.bit_cast"

const_expr :: ConstExpr -> Doc
const_expr cnst = case cnst of
  ConstGEP _ _ Nothing _ ->
    error $ "Unsupported constant GEP, result type expected:" ++ show cnst
  ConstGEP inbounds inrange (Just tp) vals ->
    app "const_expr.gep" [ bool inbounds, option nat inrange, llvm_type tp, list (typed value) vals ]
  ConstSelect c x y  -> app "const_expr.select" [ typed value c, typed value x, typed value y ]
  ConstConv op x tp  -> app "const_expr.conv" [ conv_op op, typed value x, llvm_type tp ]
  ConstBlockAddr s l -> app "const_expr.block_addr" [ symbol s, block_label l ]
  ConstFCmp op x y   -> app "const_expr.fcmp" [ fcmp_op op, typed value x, typed value y ]
  ConstICmp op x y   -> app "const_expr.icmp" [ icmp_op op, typed value x, typed value y ]
  ConstArith op x y  -> app "const_expr.arith" [ arith_op op, typed value x, value y ]
  ConstBit op x y    -> app "const_expr.bit" [ bit_op op, typed value x, value y ]

atomic_ordering :: AtomicOrdering -> Doc
atomic_ordering ord = case ord of
  Unordered  -> text "atomic_ordering.unordered"
  Monotonic  -> text "atomic_ordering.monotonic"
  Acquire    -> text "atomic_ordering.acquire"
  Release    -> text "atomic_ordering.release"
  AcqRel     -> text "atomic_ordering.acq_rel"
  SeqCst     -> text "atomic_ordering.seq_cst"

instruction :: Instr -> Doc
instruction instr = case instr of
  Ret v        -> app "instruction.ret" [ typed value v ]
  RetVoid      -> text "instruction.ret_void"
  Arith op x y -> app "instruction.arith" [ arith_op op, typed value x, value y ]
  Bit op x y   -> app "instruction.bit" [ bit_op op, typed value x, value y ]
  Conv op x tp -> app "instruction.conv" [ conv_op op, typed value x, llvm_type tp ]
  Call tailcall ret_ty fn args ->
    app "instruction.call" [ bool tailcall, llvm_type ret_ty, value fn, list (typed value) args ]
  Invoke ret_ty fn args normal except ->
    app "instruction.invoke" [ llvm_type ret_ty, value fn, list (typed value) args,
                               block_label normal, block_label except ]
  Alloca tp num align ->
    app "instruction.alloca" [ llvm_type tp, option (typed value) num, option nat align ]
  Load ptr ord align ->
    app "instruction.load" [ typed value ptr, option atomic_ordering ord, option nat align ]
  Store val ptr ord align ->
    app "instruction.store" [ typed value val, typed value ptr, option atomic_ordering ord, option nat align ]
  
  Fence{} -> unsupported
  CmpXchg{} -> unsupported
  AtomicRW{} -> unsupported

  ICmp op x y -> app "instruction.icmp" [ icmp_op op, typed value x, value y ]
  FCmp op x y -> app "instruction.fcmp" [ fcmp_op op, typed value x, value y ]
  Phi tp preds -> app "instruction.phi" [ llvm_type tp, list (pair value block_label) preds ]
  GEP inbounds base vals ->
    app "instruction.gep" [ bool inbounds, typed value base, list (typed value) vals ]
  Select c x y -> app "instruction.select" [ typed value c, typed value x, value y ]
  ExtractValue agg idxes ->
    app "instruction.extract_value" [ typed value agg, list nat idxes ]
  InsertValue agg val idxes ->
    app "instruction.insert_value" [ typed value agg, typed value val, list nat idxes ]
  ExtractElt vec idx ->
    app "instruction.extract_elt" [ typed value vec, value idx ]
  InsertElt vec val idx ->
    app "instruction.insert_elt" [ typed value vec, typed value val, value idx ]
  ShuffleVector xs ys idxes ->
    app "instruction.shuffle_vector" [ typed value xs, value ys, typed value idxes ]
  Jump l -> app "instruction.jump" [ block_label l ]
  Br c l1 l2 -> app "instruction.br" [ typed value c, block_label l1, block_label l2 ]
  Comment s -> app "instruction.comment" [ string_lit s ]
  Unreachable -> text "unreachable"
  Unwind -> text "unwind"
  VaArg val tp -> app "instruction.va_arg" [ typed value val, llvm_type tp ]
  IndirectBr val ls -> app "instruction.indirect_br" [ typed value val, list block_label ls ]
  Switch val def ls ->
    app "instruction.switch" [ typed value val, block_label def, list (pair nat block_label) ls]
  LandingPad{} -> unsupported
  Resume{} -> unsupported

 where
 unsupported = error $ "printing shim does not support instruction: " ++ show instr

stmt :: Stmt -> Doc
stmt (Result nm i md) =
  app "stmt.mk" [ option ident (Just nm), instruction i, list (pair string_lit val_md) md ]
stmt (Effect i md) =
  app "stmt.mk" [ option ident Nothing, instruction i, list (pair string_lit val_md) md ]

basic_block :: BasicBlock -> Doc
basic_block (BasicBlock l ss) =
  parens (text "basic_block.mk" <+> option block_label l $+$ (nest 2 $ vert_list stmt ss))

visibility :: Visibility -> Doc
visibility v = case v of
  DefaultVisibility   -> text "visibility.default"
  HiddenVisibility    -> text "visibility.hidden"
  ProtectedVisibility -> text "visibility.protected_visibility"

linkage :: Linkage -> Doc
linkage lk = case lk of
  Private                  -> text "linkage.private_linkage"
  LinkerPrivate            -> text "linkage.linker_private"
  LinkerPrivateWeak        -> text "linkage.linker_private_weak"
  LinkerPrivateWeakDefAuto -> text "linkage.linker_private_weak_def_auto"
  Internal                 -> text "linkage.internal"
  AvailableExternally      -> text "linkage.available_externally"
  Linkonce                 -> text "linkage.linkonce"
  Weak                     -> text "linkage.weak"
  Common                   -> text "linkage.common"
  Appending                -> text "linkage.appending"
  ExternWeak               -> text "linkage.extern_weak"
  LinkonceODR              -> text "linkage.linkonce_odr"
  WeakODR                  -> text "linkage.weak_odr"
  External                 -> text "linkage.external"
  DLLImport                -> text "linkage.dll_import"
  DLLExport                -> text "linkage.dll_export" 

define :: Define -> Doc
define d = vapp "define.mk"
  [ option linkage (defLinkage d)
  , llvm_type (defRetType d)
  , symbol (defName d)
  , list (typed ident) (defArgs d)
  , bool (defVarArgs d)
  , list fun_attr (defAttrs d)
  , option string_lit (defSection d)
  , option gc (defGC d)
  , vert_list basic_block (defBody d)
  , strmap_empty "val_md" -- FIXME! (defMetadata d) 
  , option string_lit (defComdat d)
  ] 

global_attrs :: GlobalAttrs -> Doc
global_attrs ga =
  app "global_attrs.mk"
    [ option linkage (gaLinkage ga)
    , option visibility (gaVisibility ga)
    , bool (gaConstant ga)
    ]

global :: Global -> Doc
global g =
  vapp "global.mk"
    [ symbol (globalSym g)
    , global_attrs (globalAttrs g)
    , llvm_type (globalType g)
    , option value (globalValue g)
    , option nat (globalAlign g)
    , strmap_empty "val_md" -- FIXME! (globalMetadata)
    ]

global_alias :: GlobalAlias -> Doc
global_alias ga = app "global_alias.mk"
  [ symbol (aliasName ga)
  , llvm_type (aliasType ga)
  , value (aliasTarget ga)
  ]

named_md :: NamedMd -> Doc
named_md md = app "named_md.mk"
  [ string_lit (nmName md)
  , list nat (nmValues md)
  ]

unnamed_md :: UnnamedMd -> Doc
unnamed_md md = app "unnamed_md.mk"
  [ nat (umIndex md)
  , val_md (umValues md)
  , bool (umDistinct md)
  ]

llvm_module :: Module -> Doc
llvm_module m = text "module.mk" $$ vcat
  [ option string_lit (modSourceName m)
  , data_layout (modDataLayout m)
  , list type_decl (modTypes m)
  , list named_md (modNamedMd m)
  , list unnamed_md (modUnnamedMd m)
  , strmap_empty "selection_kind"  -- FIXME! (modComdat)
  , list global (modGlobals m)
  , list declare (modDeclares m)
  , list define (modDefines m)
  , text "[]"  -- FIXME (modInlineAsm)
  , list global_alias (modAliases m)
  ]
