/- A transliteration of llvm-pretty https://github.com/elliottt/llvm-pretty/blob/master/src/Text/LLVM/AST.hs -/
-- import data.bitvec
import Std.Data.RBMap
import Init.Data.String
import Init.Data.Int

open Std (RBMap)

namespace LLVM

-- FIXME
-- def float : Type 0 := sorry
-- def double : Type 0 := sorry

def Strmap (a:Type) := RBMap String a (fun x y => decide (x < y))
def Strmap.empty {a:Type} : Strmap a := Std.RBMap.empty

-- Identifiers -----------------------------------------------------------------

inductive Ident
| named (nm:String)
| anon (idx:Nat)

namespace Ident

def asString : Ident → String
| named nm => "%" ++ nm
| anon i   => "%" ++ (Nat.toDigits 10 i).asString

protected
def lt : Ident → Ident → Prop
| named x, named y => x < y
| named _, anon _  => True
| anon x,  anon y  => x < y
| anon _,  named _ => False

instance : HasLess Ident := ⟨Ident.lt⟩.

instance decideEq : ∀(x y:Ident), Decidable (x = y)
| named a, named b =>
  match decEq a b with
  | Decidable.isTrue p  => Decidable.isTrue (congrArg _ p)
  | Decidable.isFalse p => Decidable.isFalse (fun H => Ident.noConfusion H p)
| anon a,  anon b =>
  match decEq a b with
  | Decidable.isTrue p  => Decidable.isTrue (congrArg _ p)
  | Decidable.isFalse p => Decidable.isFalse (fun H => Ident.noConfusion H p)
| anon _,  named _ => Decidable.isFalse (fun H => Ident.noConfusion H)
| named _, anon _  => Decidable.isFalse (fun H => Ident.noConfusion H)

instance decideLt : ∀(x y:Ident), Decidable (x < y)
| named x, named y =>
  match String.decLt x y with
  | Decidable.isTrue  p => Decidable.isTrue p
  | Decidable.isFalse p => Decidable.isFalse p
| anon x, anon y =>
  match Nat.decLt x y with
  | Decidable.isTrue  p => Decidable.isTrue p
  | Decidable.isFalse p => Decidable.isFalse p
| named _, anon _  => Decidable.isTrue True.intro
| anon _,  named _ => Decidable.isFalse False.elim

end Ident

-- Data Layout -----------------------------------------------------------------

inductive AlignType
| integer
| vector
| float

inductive Mangling
| elf
| mips
| mach_o
| windows_coff
| windows_coff_x86

inductive Endian
| big
| little

-- The labels are mainly for documentation, taken from parseSpecifier
inductive LayoutSpec
| endianness (e:Endian)
| pointerSize (address_space : Nat)
               (size : Nat)
               (abi_align : Nat)
               (pref_align : Nat)
               (index_size : Option Nat)
| alignSize (type : AlignType) (size : Nat) (abi_align : Nat) (pref_align : Option Nat)
| nativeIntSize (legal_widths : List Nat)
| stackAlign    (a:Nat)
| aggregateAlign (abi_align : Nat) (pref_align:Nat)
| functionAddressSpace (x:Nat)
| stackAlloca  (sz:Nat)
| mangling (m:Mangling)

-- Types -----------------------------------------------------------------------

inductive FloatType
| half
| float
| double
| fp128
| x86FP80
| ppcFP128

inductive PrimType
| label
| token
| void
| integer (w:Nat)
| floatType (tp:FloatType)
| x86mmx
| metadata

namespace PrimType
instance : HasCoe FloatType PrimType := ⟨PrimType.floatType⟩
end PrimType

inductive LLVMType
| prim (tp:PrimType)
| alias (nm:String)
| array (n:Nat) (elt:LLVMType)
| funType (ret:LLVMType) (args:Array LLVMType) (varargs:Bool)
| ptr (tp:LLVMType)
| struct (packed:Bool) (fields:Array LLVMType)
| vector (n:Nat) (elt:LLVMType)

namespace LLVMType
instance : HasCoe PrimType LLVMType := ⟨LLVMType.prim⟩
end LLVMType

-- Top-level Type Aliases ------------------------------------------------------

inductive TypeDeclBody
| opaque
| defn (tp:LLVMType)

structure TypeDecl :=
(name : String)
(decl : TypeDeclBody)

-- Symbols ---------------------------------------------------------------------

structure Symbol := (symbol : String)

@[reducible]
instance symbolHasLess : HasLess Symbol := ⟨ λ(x y:Symbol) => x.symbol < y.symbol ⟩.

@[reducible]
instance symbolLtDec (x y:Symbol) : Decidable (x < y) := String.decLt x.symbol y.symbol.

structure BlockLabel := (label : Ident)

namespace BlockLabel

instance decideEq : ∀(x y : BlockLabel), Decidable (x = y)
| ⟨a⟩, ⟨b⟩ =>
  match Ident.decideEq a b with
  | Decidable.isTrue p  => Decidable.isTrue (congrArg _ p)
  | Decidable.isFalse p => Decidable.isFalse (λH => BlockLabel.noConfusion H p)

end BlockLabel


structure Typed (a : Type) :=
(type  : LLVMType)
(value : a)

/-
namespace llvm.typed
lemma sizeof_spec' (a:Type) [has_sizeof a] (x:typed a) :
  typed.sizeof a x = 1 + sizeof (x.type) + sizeof (x.value) :=
begin
  cases x, unfold typed.sizeof
end
end llvm.typed
-/

-- Instructions ----------------------------------------------------------------

inductive ArithOp
| add (uoverflow : Bool) (soverflow : Bool)
| fadd
| sub (uoverflow : Bool) (soverflow : Bool)
| fsub
| mul (uoverflow : Bool) (soverflow : Bool)
| fmul
| udiv (exact : Bool)
| sdiv (exact : Bool)
| fdiv
| urem
| srem
| frem

-- | binary bitwise operators.
inductive BitOp
| shl (uoverflow : Bool) (soverflow : Bool)
| lshr (exact : Bool)
| ashr (exact : Bool)
| and
| or
| xor

-- | Conversions from one type to another.
inductive ConvOp
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

inductive AtomicRWOp
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

/-- Ordering constraint (https://llvm.org/docs/LangRef.html#ordering) -/
inductive AtomicOrdering
| unordered
| monotonic
| acquire
| release
| acqRel
| seqCst

-- | Integer comparison operators.
inductive ICmpOp
| ieq | ine | iugt | iuge | iult | iule | isgt | isge | islt | isle

-- | Floating-point comparison operators.
inductive FCmpOp
| ffalse| foeq | fogt | foge | folt | fole | fone
| ford  | fueq | fugt | fuge | fult | fule | fune
| funo  | ftrue

-- Values ----------------------------------------------------------------------


inductive clause
| catch
| filter

def Float := UInt32

def Double := UInt64

mutual inductive Value, ConstExpr, ValMD, DebugLoc
with Value : Type
     | integer : Int -> Value
     | bool : Bool -> Value
--     | float : Float -> Value
--     | double : Double -> Value
     | ident : Ident -> Value
     | constExpr : ConstExpr -> Value
     | symbol : Symbol -> Value
     | null  : Value
     | array : LLVMType -> Array Value -> Value
     | vector : LLVMType -> Array Value -> Value
     | struct : Array (Typed Value) -> Value
     | packedStruct : Array (Typed Value) -> Value
     | string : String -> Value -- FIXME, should probably actually be list of word8
     | undef : Value
     | label : BlockLabel -> Value
     | zeroInit : Value
     | md : ValMD -> Value
     | asm : Bool -> Bool -> String -> String -> Value -- hasSideEffects isAlignStack asmString constraintString

with ConstExpr : Type
     | select : Typed Value -> Typed Value -> Typed Value -> ConstExpr
     | gep : Bool -> Option Nat -> LLVMType -> Array (Typed Value) -> ConstExpr
     | conv : ConvOp -> Typed Value -> LLVMType -> ConstExpr
     | arith : ArithOp -> Typed Value -> Value -> ConstExpr
     | fcmp : FCmpOp -> Typed Value -> Typed Value -> ConstExpr
     | icmp : ICmpOp -> Typed Value -> Typed Value -> ConstExpr
     | bit : BitOp -> Typed Value -> Value -> ConstExpr
     | blockAddr : Symbol -> BlockLabel -> ConstExpr

with ValMD : Type
     | string (s:String) : ValMD
     | value (val:Typed Value) : ValMD
     | ref (r:Nat) : ValMD
     | node (l:List (Option ValMD)) : ValMD
     | loc (l:DebugLoc) : ValMD
     | debugInfo  : ValMD -- FIXME , just a placeholder for now
with DebugLoc : Type
     | debugLoc (line : Nat) (col : Nat) (scope : ValMD) (IA : Option ValMD) : DebugLoc

instance symbolIsValue    : HasCoe Symbol Value := ⟨Value.symbol⟩
instance constExprIsValue : HasCoe ConstExpr Value := ⟨Value.constExpr⟩

inductive Instruction : Type
| ret (val:Typed Value)
| retVoid
| arith (op:ArithOp) (x:Typed Value) (y:Value)
| bit   (op:BitOp) (x:Typed Value) (y:Value)
| conv  (op:ConvOp) (x:Typed Value) (res:LLVMType)
| call (tailcall : Bool) (rtp:Option LLVMType) (fn:Value) (args:Array (Typed Value))
| alloca (tp:LLVMType) (cnt:Option (Typed Value)) (align:Option Nat)
| load (addr:Typed Value) (ord:Option AtomicOrdering) (align:Option Nat)
| store (val:Typed Value) (addr:Typed Value) (align:Option Nat)
/-
| fence : option string -> atomic_ordering -> instruction
| cmp_xchg (weak : bool) (volatile : bool) : Typed Value -> Typed Value -> Typed Value
            -> option string -> atomic_ordering -> atomic_ordering -> instruction
| atomic_rw (volatile : bool) : AtomicRWOp -> Typed Value -> Typed Value
            -> option string -> atomic_ordering -> instruction
-/
| icmp (op:ICmpOp) (x:Typed Value) (y:Value)
| fcmp (op:FCmpOp) (x:Typed Value) (y:Value)
| phi (tp:LLVMType) (vals:Array (Value × BlockLabel))
| gep (bounds : Bool) (val:Typed Value) (idx:Array (Typed Value))
| select (c:Typed Value) (t:Typed Value) (f:Value)
| extractvalue (ag:Typed Value) (idxl:Array Nat)
| insertvalue (ag:Typed Value) (elt:Typed Value) (idxl:Array Nat)
| extractelement (vec:Typed Value) (idx:Value)
| insertelement (vec:Typed Value) (elt:Typed Value) (idx:Value)
| shufflevector (x:Typed Value) (y:Value) (mask:Typed Value)
| jump (label:BlockLabel)
| br (cond:Typed Value) (iftrue iffalse:BlockLabel)
| invoke (rtype:LLVMType) (fn:Value) (args:List (Typed Value)) (normal unwind:BlockLabel)
| comment (msg:String)
| unreachable
| unwind
| va_arg (argl:Typed Value) (tp:LLVMType)
| indirectbr (addr:Typed Value) (allowed:List BlockLabel)
| switch (idx:Typed Value) (default:BlockLabel) (cases:List (Nat × BlockLabel))
| landingpad (res:LLVMType) (y:Option (Typed Value)) (x:Bool) (clauses:List (clause × Typed Value))
| resume (exn:Typed Value)

-- Named Metadata --------------------------------------------------------------

structure NamedMD :=
(name   : String)
(values : List Nat)

-- Unnamed Metadata ------------------------------------------------------------

structure UnnamedMD :=
(index  : Nat)
(values : ValMD)
(distinct : Bool)

-- Comdat ----------------------------------------------------------------------

inductive SelectionKind
| any
| exact_match
| largest
| no_duplicates
| same_size

inductive Linkage
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

inductive Visibility
| default
| hidden
| protected_visibility

structure GlobalAttrs :=
(linkage    : Option Linkage)
(visibility : Option Visibility)
(const      : Bool)

structure Global :=
(sym   : Symbol)
(attrs : GlobalAttrs)
(type  : LLVMType)
(value : Option Value)
(align : Option Nat)
(metadata : Strmap ValMD)

inductive FunAttr
 | align_stack (a:Nat)
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
 | ssp_req
 | ssp_strong
 | uwtable

structure Declare :=
(retType : LLVMType)
(name    : Symbol)
(args    : Array LLVMType)
(varArgs : Bool)
(attrs   : Array FunAttr)
(comdat  : Option String)

structure GC := (gc : String)

structure Stmt :=
(assign : Option Ident)
(instr : Instruction)
(metadata : (Array (String × ValMD)))

structure BasicBlock :=
(label : BlockLabel)
(stmts : Array Stmt)

structure Define :=
(linkage  : Option Linkage)
(retType  : LLVMType)
(name     : Symbol)
(args     : Array (Typed Ident))
(varArgs  : Bool)
(attrs    : Array FunAttr)
(sec      : Option String)
(gc       : Option GC)
(body     : Array BasicBlock)
(metadata : Strmap ValMD)
(comdat   : Option String)

structure GlobalAlias :=
(name   : Symbol)
(type   : LLVMType)
(target : Value)

-- Modules ---------------------------------------------------------------------
structure Module :=
(sourceName : Option String)
(dataLayout : List LayoutSpec) -- ^ type size and alignment information
(types      : Array TypeDecl) -- ^ top-level type aliases
(namedMD    : Array NamedMD)
(unnamedMD  : Array UnnamedMD)
(comdat     : Strmap SelectionKind)
(globals    : Array Global) -- ^ global value declarations
(declares   : Array Declare) -- ^ external function declarations (without definitions)
(defines    : Array Define) -- ^ internal function declarations (with definitions)
(inlineAsm  : Array String)
(aliases    : Array GlobalAlias)

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

end LLVM
