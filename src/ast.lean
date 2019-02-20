/- A transliteration of llvm-pretty https://github.com/elliottt/llvm-pretty/blob/master/src/Text/LLVM/AST.hs -/
import data.bitvec
import data.rbmap

namespace llvm

-- FIXME
def float : Type 0 := sorry
def double : Type 0 := sorry

-- Identifiers -----------------------------------------------------------------

structure ident := (ident : string)

-- Data Layout -----------------------------------------------------------------

inductive align_type
  | integer : align_type 
  | vector : align_type
  | float  : align_type
  | aggregate : align_type

inductive mangling 
  | elf
  | mips
  | mach_o
  | windows_coff
  | windows_coff_x86

-- The labels are mainly for documentation, taken from parseSpecifier
inductive layout_spec
  | big_endian                                : layout_spec  
  | little_endian                             : layout_spec  
  | pointer_size  (address_space : nat)
                  (size : nat)
                  (abi_align : nat)
                  (pref_align : option nat)
                  (index_size : nat)         : layout_spec 
  | align_size    (align_type : align_type) (size : nat)
                  (abi_align : nat) (pref_align : option nat) : layout_spec
  | native_int_size (legal_widths : list nat)     : layout_spec  
  | stack_align    : nat -> layout_spec
  | function_address_space : nat -> layout_spec
  | stack_alloca  : nat -> layout_spec
  | mangling : mangling -> layout_spec  
.

def data_layout := list layout_spec

-- Types -----------------------------------------------------------------------

inductive float_type
  | half
  | float
  | double
  | fp128
  | x86_fp80
  | ppc_fp128

inductive prim_type
  | label
  | void
  | integer : nat -> prim_type
  | float_type : float_type -> prim_type
  | x86mmx
  | metadata

inductive llvm_type
  | prim_type : prim_type -> llvm_type 
  | alias : ident -> llvm_type 
  | array : nat -> llvm_type -> llvm_type 
  | fun_ty : llvm_type -> list llvm_type -> bool -> llvm_type 
  | ptr_to : llvm_type -> llvm_type 
  | struct : list llvm_type -> llvm_type 
  | packed_struct : list llvm_type -> llvm_type 
  | vector : nat -> llvm_type -> llvm_type 
  | opaque : llvm_type

-- Top-level Type Aliases ------------------------------------------------------

structure type_decl := 
  (name : ident)
  (value : llvm_type)

-- Symbols ---------------------------------------------------------------------

structure symbol := (symbol : string)

inductive block_label
  | named : ident -> block_label
  | anon : nat -> block_label

structure typed (a : Type):= 
  ( type  : llvm_type )
  ( value : a )

namespace llvm.typed
lemma sizeof_spec' (a:Type) [has_sizeof a] (x:typed a) :
  typed.sizeof a x = 1 + sizeof (x.type) + sizeof (x.value) :=
begin
  cases x, unfold typed.sizeof
end
end llvm.typed

-- Instructions ----------------------------------------------------------------

inductive arith_op
  | add (uoverflow : bool) (soverflow : bool) : arith_op
  | fadd : arith_op
  | sub (uoverflow : bool) (soverflow : bool) : arith_op
  | fsub : arith_op
  | mul (uoverflow : bool) (soverflow : bool) : arith_op
  | fmul : arith_op
  | udiv (exact : bool) : arith_op
  | sdiv (exact : bool) : arith_op
  | fdiv : arith_op
  | urem : arith_op
  | srem : arith_op
  | frem : arith_op

-- | binary bitwise operators.
inductive bit_op
  | shl (uoverflow : bool) (soverflow : bool) : bit_op
  | lshr (exact : bool) : bit_op
  | ashr (exact : bool) : bit_op
  | and
  | or
  | xor

-- | Conversions from one type to another.
inductive conv_op
  | trunc
  | zext
  | sext
  | fp_trunc
  | fp_ext
  | fp_to_ui
  | fp_to_si
  | ui_to_fp
  | si_to_fp
  | ptr_to_int
  | int_to_ptr
  | bit_cast

inductive atomic_rw_op
  | xchg
  | add
  | sub
  | and
  | nand
  | or
  | xor
  | max
  | min
  | u_max
  | u_min

inductive atomic_ordering
  | unordered
  | monotonic
  | acquire
  | release
  | acq_rel
  | seq_cst

-- | Integer comparison operators.
inductive icmp_op 
  | ieq | ine | iugt | iuge | iult | iule | isgt | isge | islt | isle

-- | Floating-point comparison operators.
inductive fcmp_op 
  | ffalse  | foeq | fogt | foge | folt | fole | fone
  | ford    | fueq | fugt | fuge | fult | fule | fune
  | funo    | ftrue

-- Values ----------------------------------------------------------------------


inductive val_md' (v : Type) : Type
  | string : string -> val_md'
  | value : typed v -> val_md'
  | ref : nat -> val_md'
  | node : option val_md' -> val_md'
--  | md_loc : debug_loc v -> val_md
--  | val_md_debug_info (debug_info' lab)

-- structure debug_loc v := 
--   ( line  : nat )
--   ( col   : nat )
--   ( scope : val_md v )
--   ( IA    : option (val_md v) )

inductive clause
  | catch 
  | filter


-- value here does not correspond exactly with LLVM::Value
mutual inductive value, const_expr
with value : Type
  | integer : ℤ -> value
  | bool : bool -> value
--  | float : float -> value
--  | double : double -> value
  | ident : ident -> value
  | const_expr : const_expr -> value
  | symbol : symbol -> value
  | null  : value
  | array : llvm_type -> list value -> value
  | vector : llvm_type -> list value -> value
  | struct : list (typed value) -> value
  | packed_struct : list (typed value) -> value
  -- | string : string -> value -- list word8?

  | undef : value
  | label : block_label -> value
  | zero_init : value
  -- | asm : bool -> bool -> string -> string -> value
  -- | md : val_md' value -> value

with const_expr : Type
  | select : typed value -> typed value -> typed value -> const_expr
  | gep : bool -> option nat -> llvm_type -> list (typed value) -> const_expr
  | conv : conv_op -> typed value -> llvm_type -> const_expr
  -- | block_addr : symbol -> block_label -> expr const
  -- | fcmp : fcmp_op -> typed (expr val) -> typed (expr val) -> expr const
  -- | icmp : icmp_op -> typed (expr val) -> typed (expr val) -> expr const
  -- | arith : arith_op -> typed (expr val) -> (expr val) -> expr const
  -- | bit : bit_op -> typed (expr val) -> expr val -> expr const
.

@[simp]
def val_md := val_md' value.


inductive instruction : Type
  | ret : typed value -> instruction
  | ret_void
  | arith : arith_op -> typed value -> value -> instruction
  | bit : bit_op -> typed value -> value -> instruction
  | conv : conv_op -> typed value -> llvm_type -> instruction
  | call : llvm_type -> value -> list (typed value) -> instruction
  | alloca : llvm_type -> option (typed value) -> option nat -> instruction
  | load : typed value -> option atomic_ordering -> option nat /- align -/ -> instruction
  | store : typed value -> typed value -> option nat /- align -/ -> instruction
  | fence : option string -> atomic_ordering -> instruction
  | cmp_xchg (weak : bool) (volatile : bool) : typed value -> typed value -> typed value 
            -> option string -> atomic_ordering -> atomic_ordering -> instruction
  | atomic_rw (volatile : bool) : atomic_rw_op -> typed value -> typed value
            -> option string -> atomic_ordering -> instruction
  | icmp : icmp_op -> typed value -> value -> instruction
  | fcmp : fcmp_op -> typed value -> value -> instruction
  | phi : llvm_type -> list (value × block_label) -> instruction
  | gep (bounds : bool) : typed value -> list (typed value) -> instruction
  | select : typed value -> typed value -> value -> instruction
  | extract_value : typed value -> list nat -> instruction
  | insert_value : typed value -> typed value -> list nat -> instruction
  | extract_elt : typed value -> value -> instruction
  | insert_elt : typed value -> typed value -> value -> instruction
  | shuffle_vector : typed value -> value -> typed value -> instruction
  | jump : block_label -> instruction
  | br : typed value -> block_label -> block_label -> instruction
  | invoke : llvm_type -> value -> list (typed value) -> block_label -> block_label -> instruction
  | comment : string -> instruction
  | unreachable
  | unwind
  | va_arg : typed value -> llvm_type -> instruction
  | indirect_br : typed value -> list block_label -> instruction
  | switch : typed value -> block_label -> list (nat × block_label) -> instruction
  | landing_pad : llvm_type -> option (typed value) -> bool -> list (clause × typed value) -> instruction
  | resume : typed value -> instruction

-- Named Metadata --------------------------------------------------------------

structure named_md := 
  ( name   : string)
  ( values : list nat)

-- Unnamed Metadata ------------------------------------------------------------

structure unnamed_md :=
  ( index  : nat)
  ( values : val_md)
  ( distinct : bool)

-- Comdat ----------------------------------------------------------------------

inductive selection_kind
  | any
  | exact_match
  | largest
  | no_duplicates
  | same_size

inductive linkage
  | private_linkage
  | linker_private
  | linker_private_weak
  | linker_private_weak_def_auto
  | internal
  | available_externally
  | linkonce
  | weak
  | common
  | appending
  | extern_weak
  | linkonce_odr
  | weak_odr
  | external
  | dll_import
  | dll_export

inductive visibility 
  | default
  | hidden
  | protected_visibility

structure global_attrs :=
  ( linkage    : option linkage    ) 
  ( visibility : option visibility ) 
  ( const      : bool              ) 

structure global :=
  ( sym   : symbol                  )
  ( attrs : global_attrs             )
  ( type  : llvm_type                )
  ( value : option value            )
  ( align : option nat              )
  ( metadata : rbmap string val_md )

inductive fun_attr
   | align_stack : nat -> fun_attr
   | alwaysinline
   | builtin
   | cold
   | inlinehint
   | jumptable
   | minsize
   | naked
   | nobuiltin
   | noduplicate
   | noimplicitfloat
   | noinline
   | nonlazybind
   | noredzone
   | noreturn
   | nounwind
   | optnone
   | optsize
   | readnone
   | readonly
   | returns_twice
   | sanitize_address
   | sanitize_memory
   | sanitize_thread
   | ssp
   | ss_preq
   | ss_pstrong
   | uw_table

structure declare :=
  ( ret_type : llvm_type      )
  ( name    : symbol        )
  ( args    : list llvm_type )
  ( var_args : bool          )
  ( attrs   : list fun_attr  )
  ( comdat  : option string )

structure GC := string

structure stmt :=
  (assign : option ident) 
  (instr : instruction)
  (metadata : (list (string × val_md)))

structure basic_block :=
  ( label : option block_label )
  ( stmts : list stmt )

structure define :=
  ( linkage  : option linkage  ) 
  ( ret_type  : llvm_type       ) 
  ( name     : symbol         ) 
  ( args     : list (typed ident)  ) 
  ( var_args  : bool           ) 
  ( attrs    : list fun_attr   ) 
  ( sec      : option string  ) 
  ( gc       : option GC      ) 
  ( body     : list basic_block) 
  ( metadata : rbmap string val_md) 
  ( comdat   : option string   ) 

structure global_alias :=
  ( name   : symbol   ) 
  ( type   : llvm_type ) 
  ( target : value    ) 

-- Modules ---------------------------------------------------------------------
structure module := 
  ( source_name : option string  )
  ( data_layout : data_layout    ) -- ^ type size and alignment information
  ( types      : list type_decl    ) -- ^ top-level type aliases
  ( named_md    : list named_md     )
  ( unnamed_md  : list unnamed_md   )
  ( comdat     : rbmap string selection_kind)
  ( globals    : list global   ) -- ^ global value declarations
  ( declares   : list declare  ) -- ^ external function declarations (without definitions)
  ( defines    : list define   ) -- ^ internal function declarations (with definitions)
  ( inline_asm  : list string   )
  ( aliases    : list global_alias )

-- DWARF Debug Info ------------------------------------------------------------
/-
data DebugInfo' lab
  = DebugInfoBasicType DIBasicType
  | DebugInfoCompileUnit (DICompileUnit' lab)
  | DebugInfoCompositeType (DICompositeType' lab)
  | DebugInfoDerivedType (DIDerivedType' lab)
  | DebugInfoEnumerator String !Int64
  | DebugInfoExpression DIExpression
  | DebugInfoFile DIFile
  | DebugInfoGlobalVariable (DIGlobalVariable' lab)
  | DebugInfoGlobalVariableExpression (DIGlobalVariableExpression' lab)
  | DebugInfoLexicalBlock (DILexicalBlock' lab)
  | DebugInfoLexicalBlockFile (DILexicalBlockFile' lab)
  | DebugInfoLocalVariable (DILocalVariable' lab)
  | DebugInfoSubprogram (DISubprogram' lab)
  | DebugInfoSubrange DISubrange
  | DebugInfoSubroutineType (DISubroutineType' lab)
  | DebugInfoNameSpace (DINameSpace' lab)
  | DebugInfoTemplateTypeParameter (DITemplateTypeParameter' lab)
  | DebugInfoTemplateValueParameter (DITemplateValueParameter' lab)
  | DebugInfoImportedEntity (DIImportedEntity' lab)
  deriving (Show,Functor,Generic,Generic1)

type DebugInfo = DebugInfo' BlockLabel

type DIImportedEntity = DIImportedEntity' BlockLabel
data DIImportedEntity' lab = DIImportedEntity
    { diieTag      :: DwarfTag
    , diieName     :: String
    , diieScope    :: Maybe (ValMd' lab)
    , diieEntity   :: Maybe (ValMd' lab)
    , diieLine     :: Word32
    } deriving (Show,Functor,Generic,Generic1)

type DITemplateTypeParameter = DITemplateTypeParameter' BlockLabel
data DITemplateTypeParameter' lab = DITemplateTypeParameter
    { dittpName :: String
    , dittpType :: ValMd' lab
    } deriving (Show,Functor,Generic,Generic1)

type DITemplateValueParameter = DITemplateValueParameter' BlockLabel
data DITemplateValueParameter' lab = DITemplateValueParameter
    { ditvpName  :: String
    , ditvpType  :: ValMd' lab
    , ditvpValue :: ValMd' lab
    } deriving (Show,Functor,Generic,Generic1)

type DINameSpace = DINameSpace' BlockLabel
data DINameSpace' lab = DINameSpace
    { dinsName  :: String
    , dinsScope :: ValMd' lab
    , dinsFile  :: ValMd' lab
    , dinsLine  :: Word32
    } deriving (Show,Functor,Generic,Generic1)

-- TODO: Turn these into sum types
-- See https://github.com/llvm-mirror/llvm/blob/release_38/include/llvm/Support/Dwarf.def
type DwarfAttrEncoding = Word8
type DwarfLang = Word16
type DwarfTag = Word16
type DwarfVirtuality = Word8
-- See https://github.com/llvm-mirror/llvm/blob/release_38/include/llvm/IR/DebugInfoMetadata.h#L175
type DIFlags = Word32
-- This seems to be defined internally as a small enum, and defined
-- differently across versions. Maybe turn this into a sum type once
-- it stabilizes.
type DIEmissionKind = Word8

data DIBasicType = DIBasicType
  { dibtTag :: DwarfTag
  , dibtName :: String
  , dibtSize :: Word64
  , dibtAlign :: Word64
  , dibtEncoding :: DwarfAttrEncoding
  } deriving (Show,Generic)

data DICompileUnit' lab = DICompileUnit
  { dicuLanguage           :: DwarfLang
  , dicuFile               :: Maybe (ValMd' lab)
  , dicuProducer           :: Maybe String
  , dicuIsOptimized        :: Bool
  , dicuFlags              :: Maybe String
  , dicuRuntimeVersion     :: Word16
  , dicuSplitDebugFilename :: Maybe FilePath
  , dicuEmissionKind       :: DIEmissionKind
  , dicuEnums              :: Maybe (ValMd' lab)
  , dicuRetainedTypes      :: Maybe (ValMd' lab)
  , dicuSubprograms        :: Maybe (ValMd' lab)
  , dicuGlobals            :: Maybe (ValMd' lab)
  , dicuImports            :: Maybe (ValMd' lab)
  , dicuMacros             :: Maybe (ValMd' lab)
  , dicuDWOId              :: Word64
  , dicuSplitDebugInlining :: Bool
  }
  deriving (Show,Functor,Generic,Generic1)

type DICompileUnit = DICompileUnit' BlockLabel

data DICompositeType' lab = DICompositeType
  { dictTag            :: DwarfTag
  , dictName           :: Maybe String
  , dictFile           :: Maybe (ValMd' lab)
  , dictLine           :: Word32
  , dictScope          :: Maybe (ValMd' lab)
  , dictBaseType       :: Maybe (ValMd' lab)
  , dictSize           :: Word64
  , dictAlign          :: Word64
  , dictOffset         :: Word64
  , dictFlags          :: DIFlags
  , dictElements       :: Maybe (ValMd' lab)
  , dictRuntimeLang    :: DwarfLang
  , dictVTableHolder   :: Maybe (ValMd' lab)
  , dictTemplateParams :: Maybe (ValMd' lab)
  , dictIdentifier     :: Maybe String
  }
  deriving (Show,Functor,Generic,Generic1)

type DICompositeType = DICompositeType' BlockLabel

data DIDerivedType' lab = DIDerivedType
  { didtTag :: DwarfTag
  , didtName :: Maybe String
  , didtFile :: Maybe (ValMd' lab)
  , didtLine :: Word32
  , didtScope :: Maybe (ValMd' lab)
  , didtBaseType :: Maybe (ValMd' lab)
  , didtSize :: Word64
  , didtAlign :: Word64
  , didtOffset :: Word64
  , didtFlags :: DIFlags
  , didtExtraData :: Maybe (ValMd' lab)
  }
  deriving (Show,Functor,Generic,Generic1)

type DIDerivedType = DIDerivedType' BlockLabel

data DIExpression = DIExpression
  { dieElements :: [Word64]
  }
  deriving (Show,Generic)

data DIFile = DIFile
  { difFilename  :: FilePath
  , difDirectory :: FilePath
  } deriving (Show,Generic)

data DIGlobalVariable' lab = DIGlobalVariable
  { digvScope                :: Maybe (ValMd' lab)
  , digvName                 :: Maybe String
  , digvLinkageName          :: Maybe String
  , digvFile                 :: Maybe (ValMd' lab)
  , digvLine                 :: Word32
  , digvType                 :: Maybe (ValMd' lab)
  , digvIsLocal              :: Bool
  , digvIsDefinition         :: Bool
  , digvVariable             :: Maybe (ValMd' lab)
  , digvDeclaration          :: Maybe (ValMd' lab)
  , digvAlignment            :: Maybe Word32
  }
  deriving (Show,Functor,Generic,Generic1)

type DIGlobalVariable = DIGlobalVariable' BlockLabel

data DIGlobalVariableExpression' lab = DIGlobalVariableExpression
  { digveVariable   :: Maybe (ValMd' lab)
  , digveExpression :: Maybe (ValMd' lab)
  }
  deriving (Show,Functor,Generic,Generic1)

type DIGlobalVariableExpression = DIGlobalVariableExpression' BlockLabel

data DILexicalBlock' lab = DILexicalBlock
  { dilbScope  :: Maybe (ValMd' lab)
  , dilbFile   :: Maybe (ValMd' lab)
  , dilbLine   :: Word32
  , dilbColumn :: Word16
  }
  deriving (Show,Functor,Generic,Generic1)

type DILexicalBlock = DILexicalBlock' BlockLabel

data DILexicalBlockFile' lab = DILexicalBlockFile
  { dilbfScope         :: ValMd' lab
  , dilbfFile          :: Maybe (ValMd' lab)
  , dilbfDiscriminator :: Word32
  }
  deriving (Show,Functor,Generic,Generic1)

type DILexicalBlockFile = DILexicalBlockFile' BlockLabel

data DILocalVariable' lab = DILocalVariable
  { dilvScope :: Maybe (ValMd' lab)
  , dilvName :: Maybe String
  , dilvFile :: Maybe (ValMd' lab)
  , dilvLine :: Word32
  , dilvType :: Maybe (ValMd' lab)
  , dilvArg :: Word16
  , dilvFlags :: DIFlags
  }
  deriving (Show,Functor,Generic,Generic1)

type DILocalVariable = DILocalVariable' BlockLabel

data DISubprogram' lab = DISubprogram
  { dispScope          :: Maybe (ValMd' lab)
  , dispName           :: Maybe String
  , dispLinkageName    :: Maybe String
  , dispFile           :: Maybe (ValMd' lab)
  , dispLine           :: Word32
  , dispType           :: Maybe (ValMd' lab)
  , dispIsLocal        :: Bool
  , dispIsDefinition   :: Bool
  , dispScopeLine      :: Word32
  , dispContainingType :: Maybe (ValMd' lab)
  , dispVirtuality     :: DwarfVirtuality
  , dispVirtualIndex   :: Word32
  , dispThisAdjustment :: Int64
  , dispThrownTypes    :: Maybe (ValMd' lab)
  , dispFlags          :: DIFlags
  , dispIsOptimized    :: Bool
  , dispTemplateParams :: Maybe (ValMd' lab)
  , dispDeclaration    :: Maybe (ValMd' lab)
  , dispVariables      :: Maybe (ValMd' lab)
  }
  deriving (Show,Functor,Generic,Generic1)

type DISubprogram = DISubprogram' BlockLabel

data DISubrange = DISubrange
  { disrCount :: Int64
  , disrLowerBound :: Int64
  }
  deriving (Show,Generic)

data DISubroutineType' lab = DISubroutineType
  { distFlags :: DIFlags
  , distTypeArray :: Maybe (ValMd' lab)
  }
  deriving (Show,Functor,Generic,Generic1)

type DISubroutineType = DISubroutineType' BlockLabel

-- Aggregate Utilities ---------------------------------------------------------

data IndexResult
  = Invalid                             -- ^ An invalid use of GEP
  | HasType Type                        -- ^ A resolved type
  | Resolve Ident (Type -> IndexResult) -- ^ Continue, after resolving an alias

isInvalid :: IndexResult -> Bool
isInvalid ir = case ir of
  Invalid -> True
  _       -> False

-- | Resolves the type of a GEP instruction. Type aliases are resolved
-- using the given function. An invalid use of GEP or one relying
-- on unknown type aliases will return 'Nothing'
resolveGepFull ::
  (Ident -> Maybe Type) {- ^ Type alias resolution -} ->
  Type                  {- ^ Pointer type          -} ->
  [Typed Value]  {- ^ Path                  -} ->
  Maybe Type            {- ^ Type of result        -}
resolveGepFull env t ixs = go (resolveGep t ixs)
  where
  go Invalid                = Nothing
  go (HasType result)       = Just result
  go (Resolve ident resume) = go . resume =<< env ident


-- | Resolve the type of a GEP instruction.  Note that the type produced is the
-- type of the result, not necessarily a pointer.
resolveGep :: Type -> [Typed Value] -> IndexResult
resolveGep (PtrTo ty0) (v:ixs0)
  | isGepIndex v =
    resolveGepBody ty0 ixs0
resolveGep ty0@PtrTo{} (v:ixs0)
  | Just i <- elimAlias (typedType v) =
    Resolve i (\ty' -> resolveGep ty0 (Typed ty' (typedValue v):ixs0))
resolveGep (Alias i) ixs =
    Resolve i (\ty' -> resolveGep ty' ixs)
resolveGep _ _ = Invalid

-- | Resolve the type of a GEP instruction.  This assumes that the input has
-- already been processed as a pointer.
resolveGepBody :: Type -> [Typed Value] -> IndexResult
resolveGepBody (Struct fs) (v:ixs)
  | Just i <- isGepStructIndex v, genericLength fs > i =
    resolveGepBody (genericIndex fs i) ixs
resolveGepBody (PackedStruct fs) (v:ixs)
  | Just i <- isGepStructIndex v, genericLength fs > i =
    resolveGepBody (genericIndex fs i) ixs
resolveGepBody (Alias name) is
  | not (null is) =
    Resolve name (\ty' -> resolveGepBody ty' is)
resolveGepBody (Array _ ty') (v:ixs)
  | isGepIndex v =
    resolveGepBody ty' ixs
resolveGepBody (Vector _ tp) [val]
  | isGepIndex val =
    HasType tp
resolveGepBody ty (v:ixs)
  | Just i <- elimAlias (typedType v) =
    Resolve i (\ty' -> resolveGepBody ty (Typed ty' (typedValue v):ixs))
resolveGepBody ty [] =
    HasType ty
resolveGepBody _ _ =
    Invalid

isGepIndex :: Typed Value -> Bool
isGepIndex tv =
  isPrimTypeOf isInteger (typedType tv) ||
  isVectorOf (isPrimTypeOf isInteger) (typedType tv)

isGepStructIndex :: Typed Value -> Maybe Integer
isGepStructIndex tv = do
  guard (isGepIndex tv)
  elimValInteger (typedValue tv)

resolveValueIndex :: Type -> [Int32] -> IndexResult
resolveValueIndex ty is@(ix:ixs) = case ty of
  Struct fs | genericLength fs > ix
    -> resolveValueIndex (genericIndex fs ix) ixs

  PackedStruct fs | genericLength fs > ix
    -> resolveValueIndex (genericIndex fs ix) ixs

  Array n ty' | fromIntegral ix < n
    -> resolveValueIndex ty' ixs

  Alias name
    -> Resolve name (\ty' -> resolveValueIndex ty' is)

  _ -> Invalid
resolveValueIndex ty [] = HasType ty
-/

end llvm

