/- A transliteration of llvm-pretty https://github.com/elliottt/llvm-pretty/blob/master/src/Text/LLVM/AST.hs -/
import data.bitvec
import data.rbmap

namespace llvm

-- Identifiers -----------------------------------------------------------------

structure Ident := string

-- Data Layout -----------------------------------------------------------------

inductive AlignType : Type 0
  | IntegerAlign : AlignType 
  | VectorAlign : AlignType
  | FloatAlign  : AlignType
  | AggregateAlign : AlignType

inductive Mangling 
  | ElfMangling
  | MipsMangling
  | MachOMangling
  | WindowsCoffMangling
  | WindowsCoffX86Mangling

-- The labels are mainly for documentation, taken from parseSpecifier
inductive LayoutSpec
  | BigEndian                                : LayoutSpec  
  | LittleEndian                             : LayoutSpec  
  | PointerSize   (address_space : nat)
                  (abi_align : nat)
                  (pref_align : option nat )
                  (mem_size : nat)
                  (index_size : nat)         : LayoutSpec 
  | AlignSize     (align_type : AlignType) (size : nat) (abi_align : nat) (pref_align : option nat) : LayoutSpec
  | NativeIntSize (legal_widths : list nat)     : LayoutSpec  
  | StackAlign    : nat -> LayoutSpec  -- ^ size, abi, pref
  | FunctionAddresSpace : nat -> LayoutSpec
  | StackAlloca  : nat -> LayoutSpec
  | Mangling : Mangling -> LayoutSpec  

def DataLayout := list LayoutSpec

-- Types -----------------------------------------------------------------------

inductive FloatType
  | Half
  | Float
  | Double
  | Fp128
  | X86_fp80
  | PPC_fp128

inductive PrimType
  | Label
  | Void
  | Integer : nat -> PrimType
  | FloatType : FloatType -> PrimType
  | X86mmx
  | Metadata

inductive LLVMType
  | PrimType : PrimType -> LLVMType 
  | Alias : Ident -> LLVMType 
  | Array : nat -> LLVMType -> LLVMType 
  | FunTy : LLVMType -> list LLVMType -> bool -> LLVMType 
  | PtrTo : LLVMType -> LLVMType 
  | Struct : list LLVMType -> LLVMType 
  | PackedStruct : list LLVMType -> LLVMType 
  | Vector : nat -> LLVMType -> LLVMType 
  | Opaque : LLVMType

-- Top-level Type Aliases ------------------------------------------------------

structure TypeDecl := 
  (typeName : Ident)
  (typeValue : LLVMType)

-- Symbols ---------------------------------------------------------------------

structure Symbol := string

inductive BlockLabel
  | Named : Ident -> BlockLabel
  | Anon : nat -> BlockLabel

structure Typed (a : Type _):= 
  ( type  : LLVMType)
  ( value : a)

-- Instructions ----------------------------------------------------------------

inductive ArithOp
  | Add (uoverflow : bool) (soverflow : bool) : ArithOp
  | FAdd : ArithOp
  | Sub (uoverflow : bool) (soverflow : bool) : ArithOp
  | FSub : ArithOp
  | Mul (uoverflow : bool) (soverflow : bool) : ArithOp
  | FMul : ArithOp
  | UDiv (exact : bool) :ArithOp
  | SDiv (exact : bool) : ArithOp
  | FDiv : ArithOp
  | URem : ArithOp
  | SRem : ArithOp
  | FRem : ArithOp

-- | Binary bitwise operators.
inductive BitOp
  | Shl (uoverflow : bool) (soverflow : bool) : BitOp
  | Lshr (exact : bool) : BitOp
  | Ashr (exact : bool) : BitOp
  | And
  | Or
  | Xor

-- | Conversions from one type to another.
inductive ConvOp
  | Trunc
  | ZExt
  | SExt
  | FpTrunc
  | FpExt
  | FpToUi
  | FpToSi
  | UiToFp
  | SiToFp
  | PtrToInt
  | IntToPtr
  | BitCast

inductive AtomicRWOp
  | AtomicXchg
  | AtomicAdd
  | AtomicSub
  | AtomicAnd
  | AtomicNand
  | AtomicOr
  | AtomicXor
  | AtomicMax
  | AtomicMin
  | AtomicUMax
  | AcomicUMin

inductive AtomicOrdering
  | Unordered
  | Monotonic
  | Acquire
  | Release
  | AcqRel
  | SeqCst

-- | Integer comparison operators.
inductive ICmpOp 
  | Ieq | Ine | Iugt | Iuge | Iult | Iule | Isgt | Isge | Islt | Isle

-- | Floating-point comparison operators.
inductive FCmpOp 
  | Ffalse  | Foeq | Fogt | Foge | Folt | Fole | Fone
  | Ford    | Fueq | Fugt | Fuge | Fult | Fule | Fune
  | Funo    | Ftrue

-- Values ----------------------------------------------------------------------

-- sjw: ConstExpr has been removed, and replaced by the corresponding
-- Instr -- we can use ConstantExpr::getAsInstruction().  This means
-- we lose some info (not all Instrs are ConstantExprs), but it
-- simplifies the AST.
mutual inductive Value, ValMd, Instruction, Clause
with Value : Type
  | ValInteger : int -> Value
  | ValBool : bool -> Value
--  | ValFloat Float
--  | ValDouble Double
  | ValIdent : Ident -> Value
  | ValSymbol : Symbol -> Value
  | ValNull
  | ValArray : LLVMType -> list Value -> Value
  | ValVector : LLVMType -> list Value -> Value
  | ValStruct : list (Typed Value) -> Value
  | ValPackedStruct : list (Typed Value) -> Value
  | ValString : string -> Value -- list Word8?
  | ValConstExpr : Instruction /- ConstExpr -/ -> Value
  | ValUndef
  | ValLabel : BlockLabel -> Value
  | ValZeroInit
  | ValAsm : bool -> bool -> string -> string -> Value
  | ValMd : ValMd -> Value
with ValMd : Type
  | ValMdString : string -> ValMd
  | ValMdValue : Typed Value -> ValMd
  | ValMdRef : nat -> ValMd
  | ValMdNode : option ValMd -> ValMd
--  | ValMdLoc (DebugLoc' lab)
--  | ValMdDebugInfo (DebugInfo' lab)
with Instruction : Type
  | Ret : Typed Value -> Instruction
  | RetVoid
  | Arith : ArithOp -> Typed Value -> Value -> Instruction
  | Bit : BitOp -> Typed Value -> Value -> Instruction
  | Conv : ConvOp -> Typed Value -> LLVMType -> Instruction
  | Call : LLVMType -> Value -> list (Typed Value) -> Instruction
  | Alloca : LLVMType -> option (Typed Value) -> option nat -> Instruction
  | Load : Typed Value -> option AtomicOrdering -> option nat /- align -/ -> Instruction
  | Store : Typed Value -> Typed Value -> option nat /- align -/ -> Instruction
  | Fence : option string -> AtomicOrdering -> Instruction
  | CmpXchg (weak : bool) (volatile : bool) : Typed Value -> Typed Value -> Typed Value 
            -> option string -> AtomicOrdering -> AtomicOrdering -> Instruction
  | AtomicRW (volatile : bool) : AtomicRWOp -> Typed Value -> Typed Value
            -> option string -> AtomicOrdering -> Instruction
  | ICmp : ICmpOp -> Typed Value -> Value -> Instruction
  | FCmp : FCmpOp -> Typed Value -> Value -> Instruction
  | Phi : LLVMType -> list (Value × BlockLabel) -> Instruction
  | GEP (bounds : bool) : Typed Value -> list (Typed Value) -> Instruction
  | Select : Typed Value -> Typed Value -> Value -> Instruction
  | ExtractValue : Typed Value -> list nat -> Instruction
  | InsertValue : Typed Value -> Typed Value -> list nat -> Instruction
  | ExtractElt : Typed Value -> Value -> Instruction
  | InsertElt : Typed Value -> Typed Value -> Value -> Instruction
  | ShuffleVector : Typed Value -> Value -> Typed Value -> Instruction
  | Jump : BlockLabel -> Instruction
  | Br : Typed Value -> BlockLabel -> BlockLabel -> Instruction
  | Invoke : LLVMType -> Value -> list (Typed Value) -> BlockLabel -> BlockLabel -> Instruction
  | Comment : string -> Instruction
  | Unreachable
  | Unwind
  | VaArg : Typed Value -> LLVMType -> Instruction
  | IndirectBr : Typed Value -> list BlockLabel -> Instruction
  | Switch : Typed Value -> BlockLabel -> list (nat × BlockLabel) -> Instruction
  | LandingPad : LLVMType -> option (Typed Value) -> bool -> list Clause -> Instruction
  | Resume : Typed Value -> Instruction
with Clause : Type
  | Catch : Typed Value -> Clause
  | Filter : Typed Value -> Clause

/-
type ValMd = ValMd' BlockLabel
-/

/-
type KindMd = String
type FnMdAttachments = Map.Map KindMd ValMd
type GlobalMdAttachments = Map.Map KindMd ValMd

data DebugLoc' lab = DebugLoc
  { dlLine  :: Word32
  , dlCol   :: Word32
  , dlScope :: ValMd' lab
  , dlIA    :: Maybe (ValMd' lab)
  } deriving (Show,Functor,Generic,Generic1)

type DebugLoc = DebugLoc' BlockLabel

-/
-- Named Metadata --------------------------------------------------------------

structure NamedMd := 
  ( nmName   : string)
  ( nmValues : list nat)

-- Unnamed Metadata ------------------------------------------------------------

structure UnnamedMd :=
  ( umIndex  : nat)
  ( umValues : ValMd)
  ( umDistinct : bool)

-- Comdat ----------------------------------------------------------------------

inductive SelectionKind
  | ComdatAny
  | ComdatExactMatch
  | ComdatLargest
  | ComdatNoDuplicates
  | ComdatSameSize

inductive Linkage
  | Private
  | LinkerPrivate
  | LinkerPrivateWeak
  | LinkerPrivateWeakDefAuto
  | Internal
  | AvailableExternally
  | Linkonce
  | Weak
  | Common
  | Appending
  | ExternWeak
  | LinkonceODR
  | WeakODR
  | External
  | DLLImport
  | DLLExport

inductive Visibility 
  | DefaultVisibility
  | HiddenVisibility
  | ProtectedVisibility

structure GlobalAttrs :=
  ( gaLinkage    : option Linkage    ) 
  ( gaVisibility : option Visibility ) 
  ( gaConstant   : bool              ) 

structure Global :=
  ( globalSym   : Symbol                  )
  ( globalAttrs : GlobalAttrs             )
  ( globalType  : LLVMType                )
  ( globalValue : option Value            )
  ( globalAlign : option nat              )
  ( globalMetadata : rbmap string ValMd   )

inductive FunAttr
   | AlignStack : nat -> FunAttr
   | Alwaysinline
   | Builtin
   | Cold
   | Inlinehint
   | Jumptable
   | Minsize
   | Naked
   | Nobuiltin
   | Noduplicate
   | Noimplicitfloat
   | Noinline
   | Nonlazybind
   | Noredzone
   | Noreturn
   | Nounwind
   | Optnone
   | Optsize
   | Readnone
   | Readonly
   | ReturnsTwice
   | SanitizeAddress
   | SanitizeMemory
   | SanitizeThread
   | SSP
   | SSPreq
   | SSPstrong
   | UWTable

structure Declare :=
  ( decRetType : LLVMType      )
  ( decName    : Symbol        )
  ( decArgs    : list LLVMType )
  ( decVarArgs : bool          )
  ( decAttrs   : list FunAttr  )
  ( decComdat  : option string )

structure GC := string

structure Stmt :=
  (assign : option Ident) 
  (instr : Instruction)
  (metadata : (list (string × ValMd)))

structure BasicBlock :=
  ( bbLabel : option BlockLabel )
  ( bbStmts : list Stmt )

structure Define :=
  ( defLinkage  : option Linkage  ) 
  ( defRetType  : LLVMType       ) 
  ( defName     : Symbol         ) 
  ( defArgs     : list (Typed Ident)  ) 
  ( defVarArgs  : bool           ) 
  ( defAttrs    : list FunAttr   ) 
  ( defSection  : option string  ) 
  ( defGC       : option GC      ) 
  ( defBody     : list BasicBlock) 
  ( defMetadata : rbmap string ValMd) 
  ( defComdat   : option string   ) 

structure GlobalAlias :=
  ( aliasName   : Symbol   ) 
  ( aliasType   : LLVMType ) 
  ( aliasTarget : Value    ) 

/-
-- Modules ---------------------------------------------------------------------

data Module = Module
  { modSourceName :: Maybe String
  , modDataLayout :: DataLayout    -- ^ type size and alignment information
  , modTypes      :: [TypeDecl]    -- ^ top-level type aliases
  , modNamedMd    :: [NamedMd]
  , modUnnamedMd  :: [UnnamedMd]
  , modComdat     :: Map.Map String SelectionKind
  , modGlobals    :: [Global]      -- ^ global value declarations
  , modDeclares   :: [Declare]     -- ^ external function declarations (without definitions)
  , modDefines    :: [Define]      -- ^ internal function declarations (with definitions)
  , modInlineAsm  :: InlineAsm
  , modAliases    :: [GlobalAlias]
  } deriving (Show,Generic)
-/
structure Module := 
  ( sourceName : option string  )
  ( dataLayout : DataLayout    ) -- ^ type size and alignment information
  ( types      : list TypeDecl    ) -- ^ top-level type aliases
  ( namedMd    : list NamedMd     )
  ( unnamedMd  : list UnnamedMd   )
  ( comdat     : rbmap string SelectionKind)
  ( globals    : list Global   ) -- ^ global value declarations
  ( declares   : list Declare  ) -- ^ external function declarations (without definitions)
  ( defines    : list Define   ) -- ^ internal function declarations (with definitions)
  ( inlineAsm  : list string   )
  ( aliases    : list GlobalAlias )

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

