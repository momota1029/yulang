import YulangClosure.OriginalPrimitiveValueReturnR338
import YulangClosure.OriginalReceiverReturnRefinementR338

/-!
R339: a hygienic, durable combined application of the original R338 modules.
The Native section embeds the complete R338 generated witness and historical
R335 comparison artifact. Only their leading `import Lean` headers are hoisted;
all remaining payload bytes and their internal namespaces are unchanged.
Current payload SHA-256: 70c080855a0f57700b0521e7c0c92ff0794d0ef3db5bbd0a7ecc609e780586ed.
Historical wrapper SHA-256: 7e856fc36176eeadc9a6e5658238bd9aa07845afbc673c8d6a565655470968e6.
The Selected proof is R338Selected with imports hoisted and its enclosing
namespace changed. The two run identifiers remain distinct and unmodified.
This is finite native control evidence plus conditional original Return
elimination. Original Inputs, primitive licenses, independent arms and R159
admission remain open. No Rust semantics or generator changes are made.
-/
namespace YulangClosure.OriginalWitnessIntegrationR339.Native
-- BEGIN EXACT R338 GENERATED PAYLOAD (leading import hoisted)
namespace R314Artifact

structure Position where
  startByte : Nat
  endByte : Nat
  kind : String
  text : String
  deriving Repr
inductive ScopeTag where
  | definition | moduleExpression | sourceMember
  | expression (id : Nat) | parameter (id : Nat) | localInitializer (id : Nat)
  | catchArm (id : Nat) (arm : Position)
  deriving Repr
structure RootBinding where
  name : String
  realm : String
  path : String
  sameNameOrdinal : Nat
  deriving Repr
inductive ExecutionOwner where | moduleRun | invocation (id : Nat) deriving Repr
inductive SourceRootIdentity where
  | definition (bindingName realm path : String) (sameNameOrdinal : Nat)
  | expression (occurrence : Nat)
  | member (realm path kind : String) (declaration member : Position)
  deriving Repr
structure RuntimeSite where
  bindingName : String
  realm : String
  path : String
  sameNameOrdinal : Nat
  occurrence : Nat
  startByte : Nat
  endByte : Nat
  deriving Repr
inductive Interface where | value | computation deriving Repr
structure Received where
  value : Nat
  view : Nat
  interface : Interface
  dispatch : Option Nat
  deriving Repr
structure RuntimeCell where
  value : Option Received
  deriving Repr
structure RuntimeEnvironment where
  parent : Option Nat
  binderKind : Option String
  binderId : Option Nat
  binderCell : Option Nat
  binderOwner : Option SourceRootIdentity
  dispatchBase : Option Nat
  dispatchWord : Option Nat
  substitution : Option Nat
  deriving Repr
inductive ReceivingViewKind where
  | ordinary | rootComp | callbackEntry (id : Nat) | callbackResult (id : Nat)
  deriving Repr
structure ReceivingView where
  index : Nat
  value : Nat
  image : Option Nat
  unknown : Bool
  kind : ReceivingViewKind
  deriving Repr
structure ImageLink where
  image : Nat
  boundary : Nat
  receiver : Nat
  deriving Repr
structure ViewImageChain where
  view : Nat
  links : List ImageLink
  deriving Repr
inductive RuntimeEvent where
  | request (step order id : Nat) (site : RuntimeSite) (owner : ExecutionOwner)
  | pendingCallee (step order request frame argumentLabel environment : Nat)
      (calleeLabel : Option Nat) (requestSite applySite : RuntimeSite) (owner : ExecutionOwner)
  | calleeReturn (step order frame argumentLabel environment value view : Nat)
      (calleeLabel : Option Nat) (site : RuntimeSite) (owner : ExecutionOwner)
      (interface : Interface) (provider : RuntimeSite)
  | delay (value code environment view : Nat)
  | nameLookup (step order environment parameter cell value view : Nat)
      (site : RuntimeSite) (owner : ExecutionOwner) (consumption : String)
  | nameReceipt (step order receipt value view : Nat)
      (site : RuntimeSite) (owner : ExecutionOwner) (consumption : String)
  | valueBind (step order receiver parameter cell environment value view : Nat) (interface : Interface)
  deriving Repr
inductive Resolution where
  | moduleDef (name : String) (realm : String) (path : String) (ordinal : Nat)
  | parameter (id : Nat) | local (id : Nat) | catchBinder (id : Nat) | caseBinder (id : Nat)
  | unresolved | ambiguous
  deriving Repr
structure EffectId where
  realm : String
  path : String
  declaration : Position
  deriving Repr
structure EffectRow where
  position : Position
  concrete : List EffectId
  variables : List String
  deriving Repr
mutual
inductive SourceType where
  | unit | int | bool | str | variable (name : String) | hole (position : Position)
  | tuple (items : List AnnotationType) | function (argument result : AnnotationType)
  deriving Repr
inductive AnnotationType where
  | mk (value : SourceType) (effects : Option EffectRow)
  deriving Repr
end
structure Annotation where
  owner : String
  position : Position
  type : AnnotationType
  deriving Repr
structure OperationIdentity where
  name : String
  familyRealm : String
  familyPath : String
  familyDeclaration : Position
  declaration : Position
  namePosition : Position
  signaturePosition : Position
  startByte : Nat
  endByte : Nat
  visibility : String
  signature : AnnotationType
  deriving Repr
inductive ValueKind where
  | unit | integer (value : String) | boolean (value : Bool) | string (value : String)
  | primitive (name : String) | tuple (items : List Received)
  | variant (tag : String) (items : List Received)
  | record (fields : List (String × Received)) | closure | computation
  | operation (identity : OperationIdentity)
  deriving Repr
structure RuntimeValue where
  source : RuntimeSite
  kind : ValueKind
  deriving Repr
structure ReturnSnapshot where
  runId : Nat
  frame : Nat
  applySite : RuntimeSite
  argumentLabel : Nat
  callerEnvironment : Nat
  cells : List RuntimeCell
  environments : List RuntimeEnvironment
  values : List RuntimeValue
  receivingViews : List ReceivingView
  receivingImageChains : List ViewImageChain
  sourceNameInitialization : Option Received
  sourceNameParameter : Option Nat
  receivingScanTruncated : Bool
  deriving Repr
structure Formal where
  id : Nat
  spelling : String
  startByte : Nat
  endByte : Nat
  sourcePosition : Position
  scope : ScopeTag
  annotation : Option Annotation
  deriving Repr
inductive BlockStatement where
  | expression (code : Nat) | binding (ordinal localId initializer : Nat)
  deriving Repr
inductive SourceStatement where
  | expression (source : Nat) | binding (ordinal localId initializer : Nat)
  deriving Repr
structure SourceStatementBlock where
  statements : List SourceStatement
  finalExpression : Nat
  deriving Repr
structure InstructionStatementBlock where
  statements : List BlockStatement
  finalExpression : Nat
  deriving Repr
inductive SourceForm where
  | unit | integer (value : String) | boolean (value : Bool) | string (value : String)
  | decodedString (value : String) | name (spelling : String) (resolution : Resolution)
  | apply (syntaxKind : String) (callee argument : Nat) | group (inner : Nat)
  | ascription (annotation : Annotation) (inner : Nat) | lambda (formal : Formal) (body : Nat)
  | operation (identity : OperationIdentity) | block (bindings : List (Nat × Nat)) (finalExpression : Nat)
  | statementBlock (block : SourceStatementBlock)
  deriving Repr
inductive Instruction where
  | unit | integer (value : String) | boolean (value : Bool) | string (value : String)
  | decodedString (value : String) | name (resolution : Resolution) (consumption : String)
  | apply (callee argument : Nat) | forward (inner : Nat) | lambda (formalId body : Nat)
  | operation (identity : OperationIdentity) | block (bindings : List (Nat × Nat)) (finalExpression : Nat)
  | statementBlock (block : InstructionStatementBlock)
  deriving Repr
structure SourceNode where
  ordinal : Nat
  occurrence : Nat
  startByte : Nat
  endByte : Nat
  sourcePosition : Position
  scope : ScopeTag
  form : SourceForm
  childOrdinals : List Nat
  codeLabel : Nat
  instruction : Instruction
  deriving Repr
def sourceText : String := (String.ofList [Char.ofNat 97, Char.ofNat 99, Char.ofNat 116, Char.ofNat 32, Char.ofNat 105, Char.ofNat 111, Char.ofNat 58, Char.ofNat 10, Char.ofNat 32, Char.ofNat 32, Char.ofNat 32, Char.ofNat 32, Char.ofNat 111, Char.ofNat 117, Char.ofNat 114, Char.ofNat 32, Char.ofNat 116, Char.ofNat 105, Char.ofNat 99, Char.ofNat 107, Char.ofNat 58, Char.ofNat 32, Char.ofNat 105, Char.ofNat 110, Char.ofNat 116, Char.ofNat 32, Char.ofNat 45, Char.ofNat 62, Char.ofNat 32, Char.ofNat 105, Char.ofNat 110, Char.ofNat 116, Char.ofNat 10, Char.ofNat 109, Char.ofNat 121, Char.ofNat 32, Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101, Char.ofNat 32, Char.ofNat 115, Char.ofNat 101, Char.ofNat 101, Char.ofNat 100, Char.ofNat 32, Char.ofNat 61, Char.ofNat 32, Char.ofNat 123, Char.ofNat 32, Char.ofNat 105, Char.ofNat 111, Char.ofNat 58, Char.ofNat 58, Char.ofNat 116, Char.ofNat 105, Char.ofNat 99, Char.ofNat 107, Char.ofNat 32, Char.ofNat 115, Char.ofNat 101, Char.ofNat 101, Char.ofNat 100, Char.ofNat 59, Char.ofNat 32, Char.ofNat 92, Char.ofNat 97, Char.ofNat 114, Char.ofNat 103, Char.ofNat 117, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116, Char.ofNat 32, Char.ofNat 45, Char.ofNat 62, Char.ofNat 32, Char.ofNat 97, Char.ofNat 114, Char.ofNat 103, Char.ofNat 117, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116, Char.ofNat 32, Char.ofNat 125, Char.ofNat 10, Char.ofNat 109, Char.ofNat 121, Char.ofNat 32, Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121, Char.ofNat 32, Char.ofNat 118, Char.ofNat 97, Char.ofNat 108, Char.ofNat 117, Char.ofNat 101, Char.ofNat 32, Char.ofNat 61, Char.ofNat 32, Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101, Char.ofNat 32, Char.ofNat 49, Char.ofNat 32, Char.ofNat 118, Char.ofNat 97, Char.ofNat 108, Char.ofNat 117, Char.ofNat 101, Char.ofNat 10, Char.ofNat 109, Char.ofNat 121, Char.ofNat 32, Char.ofNat 104, Char.ofNat 97, Char.ofNat 110, Char.ofNat 100, Char.ofNat 108, Char.ofNat 101, Char.ofNat 32, Char.ofNat 40, Char.ofNat 116, Char.ofNat 104, Char.ofNat 117, Char.ofNat 110, Char.ofNat 107, Char.ofNat 58, Char.ofNat 91, Char.ofNat 105, Char.ofNat 111, Char.ofNat 93, Char.ofNat 32, Char.ofNat 105, Char.ofNat 110, Char.ofNat 116, Char.ofNat 41, Char.ofNat 32, Char.ofNat 61, Char.ofNat 32, Char.ofNat 99, Char.ofNat 97, Char.ofNat 116, Char.ofNat 99, Char.ofNat 104, Char.ofNat 32, Char.ofNat 116, Char.ofNat 104, Char.ofNat 117, Char.ofNat 110, Char.ofNat 107, Char.ofNat 32, Char.ofNat 123, Char.ofNat 32, Char.ofNat 105, Char.ofNat 111, Char.ofNat 58, Char.ofNat 58, Char.ofNat 116, Char.ofNat 105, Char.ofNat 99, Char.ofNat 107, Char.ofNat 40, Char.ofNat 112, Char.ofNat 41, Char.ofNat 44, Char.ofNat 32, Char.ofNat 107, Char.ofNat 32, Char.ofNat 45, Char.ofNat 62, Char.ofNat 32, Char.ofNat 104, Char.ofNat 97, Char.ofNat 110, Char.ofNat 100, Char.ofNat 108, Char.ofNat 101, Char.ofNat 32, Char.ofNat 123, Char.ofNat 32, Char.ofNat 107, Char.ofNat 32, Char.ofNat 49, Char.ofNat 48, Char.ofNat 32, Char.ofNat 125, Char.ofNat 32, Char.ofNat 125, Char.ofNat 10, Char.ofNat 109, Char.ofNat 121, Char.ofNat 32, Char.ofNat 109, Char.ofNat 97, Char.ofNat 105, Char.ofNat 110, Char.ofNat 32, Char.ofNat 61, Char.ofNat 32, Char.ofNat 104, Char.ofNat 97, Char.ofNat 110, Char.ofNat 100, Char.ofNat 108, Char.ofNat 101, Char.ofNat 32, Char.ofNat 123, Char.ofNat 32, Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121, Char.ofNat 32, Char.ofNat 55, Char.ofNat 32, Char.ofNat 125])
def rootBinding : RootBinding := { name := (String.ofList [Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0 }
def rootInitializer : Nat := 0
def rootFormals : List Formal := [
  { id := 0, spelling := (String.ofList [Char.ofNat 118, Char.ofNat 97, Char.ofNat 108, Char.ofNat 117, Char.ofNat 101]), startByte := 98, endByte := 103, sourcePosition := { startByte := 98, endByte := 103, kind := (String.ofList [Char.ofNat 73, Char.ofNat 100, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116, Char.ofNat 105, Char.ofNat 102, Char.ofNat 105, Char.ofNat 101, Char.ofNat 114, Char.ofNat 80, Char.ofNat 97, Char.ofNat 116, Char.ofNat 116, Char.ofNat 101, Char.ofNat 114, Char.ofNat 110]), text := (String.ofList [Char.ofNat 118, Char.ofNat 97, Char.ofNat 108, Char.ofNat 117, Char.ofNat 101]) }, scope := ScopeTag.definition, annotation := none },
]
def nodes : List SourceNode := [
  { ordinal := 0, occurrence := 11, startByte := 89, endByte := 118, sourcePosition := { startByte := 89, endByte := 118, kind := (String.ofList [Char.ofNat 66, Char.ofNat 105, Char.ofNat 110, Char.ofNat 100, Char.ofNat 105, Char.ofNat 110, Char.ofNat 103, Char.ofNat 83, Char.ofNat 116, Char.ofNat 97, Char.ofNat 116, Char.ofNat 101, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116]), text := (String.ofList [Char.ofNat 109, Char.ofNat 121, Char.ofNat 32, Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121, Char.ofNat 32, Char.ofNat 118, Char.ofNat 97, Char.ofNat 108, Char.ofNat 117, Char.ofNat 101, Char.ofNat 32, Char.ofNat 61, Char.ofNat 32, Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101, Char.ofNat 32, Char.ofNat 49, Char.ofNat 32, Char.ofNat 118, Char.ofNat 97, Char.ofNat 108, Char.ofNat 117, Char.ofNat 101]) }, scope := ScopeTag.definition, form := SourceForm.lambda ({ id := 0, spelling := (String.ofList [Char.ofNat 118, Char.ofNat 97, Char.ofNat 108, Char.ofNat 117, Char.ofNat 101]), startByte := 98, endByte := 103, sourcePosition := { startByte := 98, endByte := 103, kind := (String.ofList [Char.ofNat 73, Char.ofNat 100, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116, Char.ofNat 105, Char.ofNat 102, Char.ofNat 105, Char.ofNat 101, Char.ofNat 114, Char.ofNat 80, Char.ofNat 97, Char.ofNat 116, Char.ofNat 116, Char.ofNat 101, Char.ofNat 114, Char.ofNat 110]), text := (String.ofList [Char.ofNat 118, Char.ofNat 97, Char.ofNat 108, Char.ofNat 117, Char.ofNat 101]) }, scope := ScopeTag.definition, annotation := none }) 1, childOrdinals := [1], codeLabel := 7, instruction := Instruction.lambda 0 8 },
  { ordinal := 1, occurrence := 12, startByte := 113, endByte := 118, sourcePosition := { startByte := 113, endByte := 118, kind := (String.ofList [Char.ofNat 77, Char.ofNat 108, Char.ofNat 65, Char.ofNat 114, Char.ofNat 103, Char.ofNat 117, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116]), text := (String.ofList [Char.ofNat 118, Char.ofNat 97, Char.ofNat 108, Char.ofNat 117, Char.ofNat 101]) }, scope := ScopeTag.parameter 0, form := SourceForm.apply (String.ofList [Char.ofNat 77, Char.ofNat 108, Char.ofNat 65, Char.ofNat 114, Char.ofNat 103, Char.ofNat 117, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116]) 2 3, childOrdinals := [2, 3], codeLabel := 8, instruction := Instruction.apply 9 10 },
  { ordinal := 2, occurrence := 13, startByte := 111, endByte := 112, sourcePosition := { startByte := 111, endByte := 112, kind := (String.ofList [Char.ofNat 77, Char.ofNat 108, Char.ofNat 65, Char.ofNat 114, Char.ofNat 103, Char.ofNat 117, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116]), text := (String.ofList [Char.ofNat 49]) }, scope := ScopeTag.parameter 0, form := SourceForm.apply (String.ofList [Char.ofNat 77, Char.ofNat 108, Char.ofNat 65, Char.ofNat 114, Char.ofNat 103, Char.ofNat 117, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116]) 4 5, childOrdinals := [4, 5], codeLabel := 9, instruction := Instruction.apply 11 12 },
  { ordinal := 3, occurrence := 16, startByte := 113, endByte := 118, sourcePosition := { startByte := 113, endByte := 118, kind := (String.ofList [Char.ofNat 73, Char.ofNat 100, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116, Char.ofNat 105, Char.ofNat 102, Char.ofNat 105, Char.ofNat 101, Char.ofNat 114, Char.ofNat 69, Char.ofNat 120, Char.ofNat 112, Char.ofNat 114, Char.ofNat 101, Char.ofNat 115, Char.ofNat 115, Char.ofNat 105, Char.ofNat 111, Char.ofNat 110]), text := (String.ofList [Char.ofNat 118, Char.ofNat 97, Char.ofNat 108, Char.ofNat 117, Char.ofNat 101]) }, scope := ScopeTag.parameter 0, form := SourceForm.name (String.ofList [Char.ofNat 118, Char.ofNat 97, Char.ofNat 108, Char.ofNat 117, Char.ofNat 101]) (Resolution.parameter 0), childOrdinals := [], codeLabel := 10, instruction := Instruction.name (Resolution.parameter 0) (String.ofList [Char.ofNat 79, Char.ofNat 98, Char.ofNat 115, Char.ofNat 101, Char.ofNat 114, Char.ofNat 118, Char.ofNat 101]) },
  { ordinal := 4, occurrence := 14, startByte := 106, endByte := 110, sourcePosition := { startByte := 106, endByte := 110, kind := (String.ofList [Char.ofNat 73, Char.ofNat 100, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116, Char.ofNat 105, Char.ofNat 102, Char.ofNat 105, Char.ofNat 101, Char.ofNat 114, Char.ofNat 69, Char.ofNat 120, Char.ofNat 112, Char.ofNat 114, Char.ofNat 101, Char.ofNat 115, Char.ofNat 115, Char.ofNat 105, Char.ofNat 111, Char.ofNat 110]), text := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101]) }, scope := ScopeTag.parameter 0, form := SourceForm.name (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101]) (Resolution.moduleDef (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101]) (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]) (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]) 0), childOrdinals := [], codeLabel := 11, instruction := Instruction.name (Resolution.moduleDef (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101]) (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]) (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]) 0) (String.ofList [Char.ofNat 79, Char.ofNat 98, Char.ofNat 115, Char.ofNat 101, Char.ofNat 114, Char.ofNat 118, Char.ofNat 101]) },
  { ordinal := 5, occurrence := 15, startByte := 111, endByte := 112, sourcePosition := { startByte := 111, endByte := 112, kind := (String.ofList [Char.ofNat 73, Char.ofNat 110, Char.ofNat 116, Char.ofNat 101, Char.ofNat 103, Char.ofNat 101, Char.ofNat 114, Char.ofNat 76, Char.ofNat 105, Char.ofNat 116, Char.ofNat 101, Char.ofNat 114, Char.ofNat 97, Char.ofNat 108]), text := (String.ofList [Char.ofNat 49]) }, scope := ScopeTag.parameter 0, form := SourceForm.integer (String.ofList [Char.ofNat 49]), childOrdinals := [], codeLabel := 12, instruction := Instruction.integer (String.ofList [Char.ofNat 49]) },
]
def runId : Nat := 129221288479048
def events : List RuntimeEvent := [RuntimeEvent.request 32 14 0 ({ bindingName := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 4, startByte := 59, endByte := 63 }) (ExecutionOwner.invocation 2),
RuntimeEvent.pendingCallee 32 15 0 2 10 2 (some 9) ({ bindingName := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 4, startByte := 59, endByte := 63 }) ({ bindingName := (String.ofList [Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 12, startByte := 113, endByte := 118 }) (ExecutionOwner.invocation 2),
RuntimeEvent.calleeReturn 59 22 2 10 2 15 17 (some 9) ({ bindingName := (String.ofList [Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 12, startByte := 113, endByte := 118 }) (ExecutionOwner.invocation 6) Interface.value ({ bindingName := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 7, startByte := 65, endByte := 86 }),
RuntimeEvent.delay 16 10 2 18,
RuntimeEvent.nameLookup 60 24 2 0 5 4 5 (({ bindingName := (String.ofList [Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 16, startByte := 113, endByte := 118 })) (ExecutionOwner.invocation 8) ((String.ofList [Char.ofNat 79, Char.ofNat 98, Char.ofNat 115, Char.ofNat 101, Char.ofNat 114, Char.ofNat 118, Char.ofNat 101])),
RuntimeEvent.nameReceipt 60 25 10 4 5 (({ bindingName := (String.ofList [Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 16, startByte := 113, endByte := 118 })) (ExecutionOwner.invocation 8) ((String.ofList [Char.ofNat 79, Char.ofNat 98, Char.ofNat 115, Char.ofNat 101, Char.ofNat 114, Char.ofNat 118, Char.ofNat 101])),
RuntimeEvent.valueBind 15 7 1 0 5 2 4 5 Interface.value,
RuntimeEvent.valueBind 23 10 2 0 6 3 7 8 Interface.value,
RuntimeEvent.valueBind 61 26 8 1 10 7 4 5 Interface.value]
def returnSnapshot : ReturnSnapshot := { runId := 129221288479048, frame := 2, applySite := { bindingName := (String.ofList [Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 12, startByte := 113, endByte := 118 }, argumentLabel := 10, callerEnvironment := 2, cells := [{ value := some { value := 5, view := 6, interface := Interface.value, dispatch := none } }, { value := some { value := 2, view := 3, interface := Interface.value, dispatch := none } }, { value := some { value := 0, view := 0, interface := Interface.value, dispatch := none } }, { value := none }, { value := some { value := 1, view := 2, interface := Interface.computation, dispatch := none } }, { value := some { value := 4, view := 5, interface := Interface.value, dispatch := none } }, { value := some { value := 7, view := 8, interface := Interface.value, dispatch := none } }, { value := some { value := 7, view := 8, interface := Interface.value, dispatch := none } }, { value := some { value := 11, view := 12, interface := Interface.value, dispatch := none } }, { value := some { value := 12, view := 14, interface := Interface.computation, dispatch := none } }], environments := [{ parent := none, binderKind := none, binderId := none, binderCell := none, binderOwner := none, dispatchBase := none, dispatchWord := none, substitution := none }, { parent := some 0, binderKind := some (String.ofList [Char.ofNat 112, Char.ofNat 97, Char.ofNat 114, Char.ofNat 97, Char.ofNat 109, Char.ofNat 101, Char.ofNat 116, Char.ofNat 101, Char.ofNat 114]), binderId := some 0, binderCell := some 4, binderOwner := some (SourceRootIdentity.definition (String.ofList [Char.ofNat 104, Char.ofNat 97, Char.ofNat 110, Char.ofNat 100, Char.ofNat 108, Char.ofNat 101]) (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]) (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]) 0), dispatchBase := none, dispatchWord := none, substitution := none }, { parent := some 0, binderKind := some (String.ofList [Char.ofNat 112, Char.ofNat 97, Char.ofNat 114, Char.ofNat 97, Char.ofNat 109, Char.ofNat 101, Char.ofNat 116, Char.ofNat 101, Char.ofNat 114]), binderId := some 0, binderCell := some 5, binderOwner := some (SourceRootIdentity.definition (String.ofList [Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121]) (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]) (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]) 0), dispatchBase := none, dispatchWord := none, substitution := none }, { parent := some 0, binderKind := some (String.ofList [Char.ofNat 112, Char.ofNat 97, Char.ofNat 114, Char.ofNat 97, Char.ofNat 109, Char.ofNat 101, Char.ofNat 116, Char.ofNat 101, Char.ofNat 114]), binderId := some 0, binderCell := some 6, binderOwner := some (SourceRootIdentity.definition (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101]) (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]) (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]) 0), dispatchBase := none, dispatchWord := none, substitution := none }, { parent := some 1, binderKind := some (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 116, Char.ofNat 99, Char.ofNat 104]), binderId := some 0, binderCell := some 7, binderOwner := some (SourceRootIdentity.definition (String.ofList [Char.ofNat 104, Char.ofNat 97, Char.ofNat 110, Char.ofNat 100, Char.ofNat 108, Char.ofNat 101]) (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]) (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]) 0), dispatchBase := none, dispatchWord := none, substitution := none }, { parent := some 4, binderKind := some (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 116, Char.ofNat 99, Char.ofNat 104]), binderId := some 1, binderCell := some 8, binderOwner := some (SourceRootIdentity.definition (String.ofList [Char.ofNat 104, Char.ofNat 97, Char.ofNat 110, Char.ofNat 100, Char.ofNat 108, Char.ofNat 101]) (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]) (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]) 0), dispatchBase := none, dispatchWord := none, substitution := none }, { parent := some 0, binderKind := some (String.ofList [Char.ofNat 112, Char.ofNat 97, Char.ofNat 114, Char.ofNat 97, Char.ofNat 109, Char.ofNat 101, Char.ofNat 116, Char.ofNat 101, Char.ofNat 114]), binderId := some 0, binderCell := some 9, binderOwner := some (SourceRootIdentity.definition (String.ofList [Char.ofNat 104, Char.ofNat 97, Char.ofNat 110, Char.ofNat 100, Char.ofNat 108, Char.ofNat 101]) (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]) (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]) 0), dispatchBase := none, dispatchWord := none, substitution := none }], values := [{ source := { bindingName := (String.ofList [Char.ofNat 104, Char.ofNat 97, Char.ofNat 110, Char.ofNat 100, Char.ofNat 108, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 19, startByte := 119, endByte := 197 }, kind := ValueKind.closure }, { source := { bindingName := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 105, Char.ofNat 110]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 30, startByte := 215, endByte := 226 }, kind := ValueKind.computation }, { source := { bindingName := (String.ofList [Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 11, startByte := 89, endByte := 118 }, kind := ValueKind.closure }, { source := { bindingName := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 105, Char.ofNat 110]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 33, startByte := 223, endByte := 224 }, kind := ValueKind.computation }, { source := { bindingName := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 105, Char.ofNat 110]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 35, startByte := 223, endByte := 224 }, kind := ValueKind.integer (String.ofList [Char.ofNat 55]) }, { source := { bindingName := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 2, startByte := 33, endByte := 88 }, kind := ValueKind.closure }, { source := { bindingName := (String.ofList [Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 13, startByte := 111, endByte := 112 }, kind := ValueKind.computation }, { source := { bindingName := (String.ofList [Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 15, startByte := 111, endByte := 112 }, kind := ValueKind.integer (String.ofList [Char.ofNat 49]) }, { source := { bindingName := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 5, startByte := 52, endByte := 58 }, kind := ValueKind.operation ({ name := (String.ofList [Char.ofNat 116, Char.ofNat 105, Char.ofNat 99, Char.ofNat 107]), familyRealm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), familyPath := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), familyDeclaration := { startByte := 0, endByte := 32, kind := (String.ofList [Char.ofNat 65, Char.ofNat 99, Char.ofNat 116, Char.ofNat 68, Char.ofNat 101, Char.ofNat 99, Char.ofNat 108, Char.ofNat 97, Char.ofNat 114, Char.ofNat 97, Char.ofNat 116, Char.ofNat 105, Char.ofNat 111, Char.ofNat 110]), text := (String.ofList [Char.ofNat 97, Char.ofNat 99, Char.ofNat 116, Char.ofNat 32, Char.ofNat 105, Char.ofNat 111, Char.ofNat 58, Char.ofNat 10, Char.ofNat 32, Char.ofNat 32, Char.ofNat 32, Char.ofNat 32, Char.ofNat 111, Char.ofNat 117, Char.ofNat 114, Char.ofNat 32, Char.ofNat 116, Char.ofNat 105, Char.ofNat 99, Char.ofNat 107, Char.ofNat 58, Char.ofNat 32, Char.ofNat 105, Char.ofNat 110, Char.ofNat 116, Char.ofNat 32, Char.ofNat 45, Char.ofNat 62, Char.ofNat 32, Char.ofNat 105, Char.ofNat 110, Char.ofNat 116]) }, declaration := { startByte := 12, endByte := 32, kind := (String.ofList [Char.ofNat 66, Char.ofNat 105, Char.ofNat 110, Char.ofNat 100, Char.ofNat 105, Char.ofNat 110, Char.ofNat 103, Char.ofNat 83, Char.ofNat 116, Char.ofNat 97, Char.ofNat 116, Char.ofNat 101, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116]), text := (String.ofList [Char.ofNat 111, Char.ofNat 117, Char.ofNat 114, Char.ofNat 32, Char.ofNat 116, Char.ofNat 105, Char.ofNat 99, Char.ofNat 107, Char.ofNat 58, Char.ofNat 32, Char.ofNat 105, Char.ofNat 110, Char.ofNat 116, Char.ofNat 32, Char.ofNat 45, Char.ofNat 62, Char.ofNat 32, Char.ofNat 105, Char.ofNat 110, Char.ofNat 116]) }, namePosition := { startByte := 16, endByte := 20, kind := (String.ofList [Char.ofNat 73, Char.ofNat 100, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116, Char.ofNat 105, Char.ofNat 102, Char.ofNat 105, Char.ofNat 101, Char.ofNat 114, Char.ofNat 80, Char.ofNat 97, Char.ofNat 116, Char.ofNat 116, Char.ofNat 101, Char.ofNat 114, Char.ofNat 110]), text := (String.ofList [Char.ofNat 116, Char.ofNat 105, Char.ofNat 99, Char.ofNat 107]) }, signaturePosition := { startByte := 22, endByte := 32, kind := (String.ofList [Char.ofNat 84, Char.ofNat 121, Char.ofNat 112, Char.ofNat 101, Char.ofNat 69, Char.ofNat 120, Char.ofNat 112, Char.ofNat 114, Char.ofNat 101, Char.ofNat 115, Char.ofNat 115, Char.ofNat 105, Char.ofNat 111, Char.ofNat 110]), text := (String.ofList [Char.ofNat 105, Char.ofNat 110, Char.ofNat 116, Char.ofNat 32, Char.ofNat 45, Char.ofNat 62, Char.ofNat 32, Char.ofNat 105, Char.ofNat 110, Char.ofNat 116]) }, startByte := 12, endByte := 32, visibility := (String.ofList [Char.ofNat 79, Char.ofNat 117, Char.ofNat 114]), signature := AnnotationType.mk (SourceType.function (AnnotationType.mk (SourceType.int) (none)) (AnnotationType.mk (SourceType.int) (none))) (none) }) }, { source := { bindingName := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 4, startByte := 59, endByte := 63 }, kind := ValueKind.computation }, { source := { bindingName := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 4, startByte := 59, endByte := 63 }, kind := ValueKind.computation }, { source := { bindingName := (String.ofList [Char.ofNat 104, Char.ofNat 97, Char.ofNat 110, Char.ofNat 100, Char.ofNat 108, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 20, startByte := 148, endByte := 197 }, kind := ValueKind.closure }, { source := { bindingName := (String.ofList [Char.ofNat 104, Char.ofNat 97, Char.ofNat 110, Char.ofNat 100, Char.ofNat 108, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 22, startByte := 187, endByte := 195 }, kind := ValueKind.computation }, { source := { bindingName := (String.ofList [Char.ofNat 104, Char.ofNat 97, Char.ofNat 110, Char.ofNat 100, Char.ofNat 108, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 25, startByte := 191, endByte := 193 }, kind := ValueKind.computation }, { source := { bindingName := (String.ofList [Char.ofNat 104, Char.ofNat 97, Char.ofNat 110, Char.ofNat 100, Char.ofNat 108, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 27, startByte := 191, endByte := 193 }, kind := ValueKind.integer (String.ofList [Char.ofNat 49, Char.ofNat 48]) }, { source := { bindingName := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 7, startByte := 65, endByte := 86 }, kind := ValueKind.closure }], receivingViews := [{ index := 0, value := 0, image := none, unknown := true, kind := ReceivingViewKind.ordinary }, { index := 1, value := 1, image := none, unknown := true, kind := ReceivingViewKind.ordinary }, { index := 2, value := 1, image := some 0, unknown := true, kind := ReceivingViewKind.rootComp }, { index := 3, value := 2, image := none, unknown := true, kind := ReceivingViewKind.ordinary }, { index := 4, value := 3, image := none, unknown := true, kind := ReceivingViewKind.ordinary }, { index := 5, value := 4, image := none, unknown := false, kind := ReceivingViewKind.ordinary }, { index := 6, value := 5, image := none, unknown := true, kind := ReceivingViewKind.ordinary }, { index := 7, value := 6, image := none, unknown := true, kind := ReceivingViewKind.ordinary }, { index := 8, value := 7, image := none, unknown := false, kind := ReceivingViewKind.ordinary }, { index := 9, value := 8, image := none, unknown := true, kind := ReceivingViewKind.ordinary }, { index := 10, value := 9, image := none, unknown := true, kind := ReceivingViewKind.ordinary }, { index := 11, value := 10, image := none, unknown := true, kind := ReceivingViewKind.ordinary }, { index := 12, value := 11, image := none, unknown := true, kind := ReceivingViewKind.ordinary }, { index := 13, value := 12, image := none, unknown := true, kind := ReceivingViewKind.ordinary }, { index := 14, value := 12, image := some 1, unknown := true, kind := ReceivingViewKind.rootComp }, { index := 15, value := 13, image := none, unknown := true, kind := ReceivingViewKind.ordinary }, { index := 16, value := 14, image := none, unknown := false, kind := ReceivingViewKind.ordinary }, { index := 17, value := 15, image := none, unknown := true, kind := ReceivingViewKind.ordinary }], receivingImageChains := [{ view := 0, links := [] }, { view := 1, links := [] }, { view := 2, links := [{ image := 0, boundary := 0, receiver := 0 }] }, { view := 3, links := [] }, { view := 4, links := [] }, { view := 5, links := [] }, { view := 6, links := [] }, { view := 7, links := [] }, { view := 8, links := [] }, { view := 9, links := [] }, { view := 10, links := [] }, { view := 11, links := [] }, { view := 12, links := [] }, { view := 13, links := [] }, { view := 14, links := [{ image := 1, boundary := 1, receiver := 4 }] }, { view := 15, links := [] }, { view := 16, links := [] }, { view := 17, links := [] }], sourceNameInitialization := some { value := 4, view := 5, interface := Interface.value, dispatch := none }, sourceNameParameter := some 0, receivingScanTruncated := false }
end R314Artifact


namespace R315MakeArtifact

structure Position where
  startByte : Nat
  endByte : Nat
  kind : String
  text : String
  deriving Repr
inductive ScopeTag where
  | definition | moduleExpression | sourceMember
  | expression (id : Nat) | parameter (id : Nat) | localInitializer (id : Nat)
  | catchArm (id : Nat) (arm : Position)
  deriving Repr
structure RootBinding where
  name : String
  realm : String
  path : String
  sameNameOrdinal : Nat
  deriving Repr
inductive ExecutionOwner where | moduleRun | invocation (id : Nat) deriving Repr
inductive SourceRootIdentity where
  | definition (bindingName realm path : String) (sameNameOrdinal : Nat)
  | expression (occurrence : Nat)
  | member (realm path kind : String) (declaration member : Position)
  deriving Repr
structure RuntimeSite where
  bindingName : String
  realm : String
  path : String
  sameNameOrdinal : Nat
  occurrence : Nat
  startByte : Nat
  endByte : Nat
  deriving Repr
inductive Interface where | value | computation deriving Repr
structure Received where
  value : Nat
  view : Nat
  interface : Interface
  dispatch : Option Nat
  deriving Repr
structure RuntimeCell where
  value : Option Received
  deriving Repr
structure RuntimeEnvironment where
  parent : Option Nat
  binderKind : Option String
  binderId : Option Nat
  binderCell : Option Nat
  binderOwner : Option SourceRootIdentity
  dispatchBase : Option Nat
  dispatchWord : Option Nat
  substitution : Option Nat
  deriving Repr
inductive ReceivingViewKind where
  | ordinary | rootComp | callbackEntry (id : Nat) | callbackResult (id : Nat)
  deriving Repr
structure ReceivingView where
  index : Nat
  value : Nat
  image : Option Nat
  unknown : Bool
  kind : ReceivingViewKind
  deriving Repr
structure ImageLink where
  image : Nat
  boundary : Nat
  receiver : Nat
  deriving Repr
structure ViewImageChain where
  view : Nat
  links : List ImageLink
  deriving Repr
inductive RuntimeEvent where
  | request (step order id : Nat) (site : RuntimeSite) (owner : ExecutionOwner)
  | pendingCallee (step order request frame argumentLabel environment : Nat)
      (calleeLabel : Option Nat) (requestSite applySite : RuntimeSite) (owner : ExecutionOwner)
  | calleeReturn (step order frame argumentLabel environment value view : Nat)
      (calleeLabel : Option Nat) (site : RuntimeSite) (owner : ExecutionOwner)
      (interface : Interface) (provider : RuntimeSite)
  | delay (value code environment view : Nat)
  | nameLookup (step order environment parameter cell value view : Nat)
      (site : RuntimeSite) (owner : ExecutionOwner) (consumption : String)
  | nameReceipt (step order receipt value view : Nat)
      (site : RuntimeSite) (owner : ExecutionOwner) (consumption : String)
  | valueBind (step order receiver parameter cell environment value view : Nat) (interface : Interface)
  deriving Repr
inductive Resolution where
  | moduleDef (name : String) (realm : String) (path : String) (ordinal : Nat)
  | parameter (id : Nat) | local (id : Nat) | catchBinder (id : Nat) | caseBinder (id : Nat)
  | unresolved | ambiguous
  deriving Repr
structure EffectId where
  realm : String
  path : String
  declaration : Position
  deriving Repr
structure EffectRow where
  position : Position
  concrete : List EffectId
  variables : List String
  deriving Repr
mutual
inductive SourceType where
  | unit | int | bool | str | variable (name : String) | hole (position : Position)
  | tuple (items : List AnnotationType) | function (argument result : AnnotationType)
  deriving Repr
inductive AnnotationType where
  | mk (value : SourceType) (effects : Option EffectRow)
  deriving Repr
end
structure Annotation where
  owner : String
  position : Position
  type : AnnotationType
  deriving Repr
structure OperationIdentity where
  name : String
  familyRealm : String
  familyPath : String
  familyDeclaration : Position
  declaration : Position
  namePosition : Position
  signaturePosition : Position
  startByte : Nat
  endByte : Nat
  visibility : String
  signature : AnnotationType
  deriving Repr
inductive ValueKind where
  | unit | integer (value : String) | boolean (value : Bool) | string (value : String)
  | primitive (name : String) | tuple (items : List Received)
  | variant (tag : String) (items : List Received)
  | record (fields : List (String × Received)) | closure | computation
  | operation (identity : OperationIdentity)
  deriving Repr
structure RuntimeValue where
  source : RuntimeSite
  kind : ValueKind
  deriving Repr
structure ReturnSnapshot where
  runId : Nat
  frame : Nat
  applySite : RuntimeSite
  argumentLabel : Nat
  callerEnvironment : Nat
  cells : List RuntimeCell
  environments : List RuntimeEnvironment
  values : List RuntimeValue
  receivingViews : List ReceivingView
  receivingImageChains : List ViewImageChain
  sourceNameInitialization : Option Received
  sourceNameParameter : Option Nat
  receivingScanTruncated : Bool
  deriving Repr
structure Formal where
  id : Nat
  spelling : String
  startByte : Nat
  endByte : Nat
  sourcePosition : Position
  scope : ScopeTag
  annotation : Option Annotation
  deriving Repr
inductive BlockStatement where
  | expression (code : Nat) | binding (ordinal localId initializer : Nat)
  deriving Repr
inductive SourceStatement where
  | expression (source : Nat) | binding (ordinal localId initializer : Nat)
  deriving Repr
structure SourceStatementBlock where
  statements : List SourceStatement
  finalExpression : Nat
  deriving Repr
structure InstructionStatementBlock where
  statements : List BlockStatement
  finalExpression : Nat
  deriving Repr
inductive SourceForm where
  | unit | integer (value : String) | boolean (value : Bool) | string (value : String)
  | decodedString (value : String) | name (spelling : String) (resolution : Resolution)
  | apply (syntaxKind : String) (callee argument : Nat) | group (inner : Nat)
  | ascription (annotation : Annotation) (inner : Nat) | lambda (formal : Formal) (body : Nat)
  | operation (identity : OperationIdentity) | block (bindings : List (Nat × Nat)) (finalExpression : Nat)
  | statementBlock (block : SourceStatementBlock)
  deriving Repr
inductive Instruction where
  | unit | integer (value : String) | boolean (value : Bool) | string (value : String)
  | decodedString (value : String) | name (resolution : Resolution) (consumption : String)
  | apply (callee argument : Nat) | forward (inner : Nat) | lambda (formalId body : Nat)
  | operation (identity : OperationIdentity) | block (bindings : List (Nat × Nat)) (finalExpression : Nat)
  | statementBlock (block : InstructionStatementBlock)
  deriving Repr
structure SourceNode where
  ordinal : Nat
  occurrence : Nat
  startByte : Nat
  endByte : Nat
  sourcePosition : Position
  scope : ScopeTag
  form : SourceForm
  childOrdinals : List Nat
  codeLabel : Nat
  instruction : Instruction
  deriving Repr
def sourceText : String := (String.ofList [Char.ofNat 97, Char.ofNat 99, Char.ofNat 116, Char.ofNat 32, Char.ofNat 105, Char.ofNat 111, Char.ofNat 58, Char.ofNat 10, Char.ofNat 32, Char.ofNat 32, Char.ofNat 32, Char.ofNat 32, Char.ofNat 111, Char.ofNat 117, Char.ofNat 114, Char.ofNat 32, Char.ofNat 116, Char.ofNat 105, Char.ofNat 99, Char.ofNat 107, Char.ofNat 58, Char.ofNat 32, Char.ofNat 105, Char.ofNat 110, Char.ofNat 116, Char.ofNat 32, Char.ofNat 45, Char.ofNat 62, Char.ofNat 32, Char.ofNat 105, Char.ofNat 110, Char.ofNat 116, Char.ofNat 10, Char.ofNat 109, Char.ofNat 121, Char.ofNat 32, Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101, Char.ofNat 32, Char.ofNat 115, Char.ofNat 101, Char.ofNat 101, Char.ofNat 100, Char.ofNat 32, Char.ofNat 61, Char.ofNat 32, Char.ofNat 123, Char.ofNat 32, Char.ofNat 105, Char.ofNat 111, Char.ofNat 58, Char.ofNat 58, Char.ofNat 116, Char.ofNat 105, Char.ofNat 99, Char.ofNat 107, Char.ofNat 32, Char.ofNat 115, Char.ofNat 101, Char.ofNat 101, Char.ofNat 100, Char.ofNat 59, Char.ofNat 32, Char.ofNat 92, Char.ofNat 97, Char.ofNat 114, Char.ofNat 103, Char.ofNat 117, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116, Char.ofNat 32, Char.ofNat 45, Char.ofNat 62, Char.ofNat 32, Char.ofNat 97, Char.ofNat 114, Char.ofNat 103, Char.ofNat 117, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116, Char.ofNat 32, Char.ofNat 125, Char.ofNat 10, Char.ofNat 109, Char.ofNat 121, Char.ofNat 32, Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121, Char.ofNat 32, Char.ofNat 118, Char.ofNat 97, Char.ofNat 108, Char.ofNat 117, Char.ofNat 101, Char.ofNat 32, Char.ofNat 61, Char.ofNat 32, Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101, Char.ofNat 32, Char.ofNat 49, Char.ofNat 32, Char.ofNat 118, Char.ofNat 97, Char.ofNat 108, Char.ofNat 117, Char.ofNat 101, Char.ofNat 10, Char.ofNat 109, Char.ofNat 121, Char.ofNat 32, Char.ofNat 104, Char.ofNat 97, Char.ofNat 110, Char.ofNat 100, Char.ofNat 108, Char.ofNat 101, Char.ofNat 32, Char.ofNat 40, Char.ofNat 116, Char.ofNat 104, Char.ofNat 117, Char.ofNat 110, Char.ofNat 107, Char.ofNat 58, Char.ofNat 91, Char.ofNat 105, Char.ofNat 111, Char.ofNat 93, Char.ofNat 32, Char.ofNat 105, Char.ofNat 110, Char.ofNat 116, Char.ofNat 41, Char.ofNat 32, Char.ofNat 61, Char.ofNat 32, Char.ofNat 99, Char.ofNat 97, Char.ofNat 116, Char.ofNat 99, Char.ofNat 104, Char.ofNat 32, Char.ofNat 116, Char.ofNat 104, Char.ofNat 117, Char.ofNat 110, Char.ofNat 107, Char.ofNat 32, Char.ofNat 123, Char.ofNat 32, Char.ofNat 105, Char.ofNat 111, Char.ofNat 58, Char.ofNat 58, Char.ofNat 116, Char.ofNat 105, Char.ofNat 99, Char.ofNat 107, Char.ofNat 40, Char.ofNat 112, Char.ofNat 41, Char.ofNat 44, Char.ofNat 32, Char.ofNat 107, Char.ofNat 32, Char.ofNat 45, Char.ofNat 62, Char.ofNat 32, Char.ofNat 104, Char.ofNat 97, Char.ofNat 110, Char.ofNat 100, Char.ofNat 108, Char.ofNat 101, Char.ofNat 32, Char.ofNat 123, Char.ofNat 32, Char.ofNat 107, Char.ofNat 32, Char.ofNat 49, Char.ofNat 48, Char.ofNat 32, Char.ofNat 125, Char.ofNat 32, Char.ofNat 125, Char.ofNat 10, Char.ofNat 109, Char.ofNat 121, Char.ofNat 32, Char.ofNat 109, Char.ofNat 97, Char.ofNat 105, Char.ofNat 110, Char.ofNat 32, Char.ofNat 61, Char.ofNat 32, Char.ofNat 104, Char.ofNat 97, Char.ofNat 110, Char.ofNat 100, Char.ofNat 108, Char.ofNat 101, Char.ofNat 32, Char.ofNat 123, Char.ofNat 32, Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121, Char.ofNat 32, Char.ofNat 55, Char.ofNat 32, Char.ofNat 125])
def rootBinding : RootBinding := { name := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0 }
def rootInitializer : Nat := 0
def rootFormals : List Formal := [
  { id := 0, spelling := (String.ofList [Char.ofNat 115, Char.ofNat 101, Char.ofNat 101, Char.ofNat 100]), startByte := 41, endByte := 45, sourcePosition := { startByte := 41, endByte := 45, kind := (String.ofList [Char.ofNat 73, Char.ofNat 100, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116, Char.ofNat 105, Char.ofNat 102, Char.ofNat 105, Char.ofNat 101, Char.ofNat 114, Char.ofNat 80, Char.ofNat 97, Char.ofNat 116, Char.ofNat 116, Char.ofNat 101, Char.ofNat 114, Char.ofNat 110]), text := (String.ofList [Char.ofNat 115, Char.ofNat 101, Char.ofNat 101, Char.ofNat 100]) }, scope := ScopeTag.definition, annotation := none },
]
def nodes : List SourceNode := [
  { ordinal := 0, occurrence := 2, startByte := 33, endByte := 88, sourcePosition := { startByte := 33, endByte := 88, kind := (String.ofList [Char.ofNat 66, Char.ofNat 105, Char.ofNat 110, Char.ofNat 100, Char.ofNat 105, Char.ofNat 110, Char.ofNat 103, Char.ofNat 83, Char.ofNat 116, Char.ofNat 97, Char.ofNat 116, Char.ofNat 101, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116]), text := (String.ofList [Char.ofNat 109, Char.ofNat 121, Char.ofNat 32, Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101, Char.ofNat 32, Char.ofNat 115, Char.ofNat 101, Char.ofNat 101, Char.ofNat 100, Char.ofNat 32, Char.ofNat 61, Char.ofNat 32, Char.ofNat 123, Char.ofNat 32, Char.ofNat 105, Char.ofNat 111, Char.ofNat 58, Char.ofNat 58, Char.ofNat 116, Char.ofNat 105, Char.ofNat 99, Char.ofNat 107, Char.ofNat 32, Char.ofNat 115, Char.ofNat 101, Char.ofNat 101, Char.ofNat 100, Char.ofNat 59, Char.ofNat 32, Char.ofNat 92, Char.ofNat 97, Char.ofNat 114, Char.ofNat 103, Char.ofNat 117, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116, Char.ofNat 32, Char.ofNat 45, Char.ofNat 62, Char.ofNat 32, Char.ofNat 97, Char.ofNat 114, Char.ofNat 103, Char.ofNat 117, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116, Char.ofNat 32, Char.ofNat 125]) }, scope := ScopeTag.definition, form := SourceForm.lambda ({ id := 0, spelling := (String.ofList [Char.ofNat 115, Char.ofNat 101, Char.ofNat 101, Char.ofNat 100]), startByte := 41, endByte := 45, sourcePosition := { startByte := 41, endByte := 45, kind := (String.ofList [Char.ofNat 73, Char.ofNat 100, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116, Char.ofNat 105, Char.ofNat 102, Char.ofNat 105, Char.ofNat 101, Char.ofNat 114, Char.ofNat 80, Char.ofNat 97, Char.ofNat 116, Char.ofNat 116, Char.ofNat 101, Char.ofNat 114, Char.ofNat 110]), text := (String.ofList [Char.ofNat 115, Char.ofNat 101, Char.ofNat 101, Char.ofNat 100]) }, scope := ScopeTag.definition, annotation := none }) 1, childOrdinals := [1], codeLabel := 0, instruction := Instruction.lambda 0 1 },
  { ordinal := 1, occurrence := 3, startByte := 48, endByte := 88, sourcePosition := { startByte := 48, endByte := 88, kind := (String.ofList [Char.ofNat 66, Char.ofNat 114, Char.ofNat 97, Char.ofNat 99, Char.ofNat 101, Char.ofNat 100, Char.ofNat 83, Char.ofNat 116, Char.ofNat 97, Char.ofNat 116, Char.ofNat 101, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116, Char.ofNat 66, Char.ofNat 108, Char.ofNat 111, Char.ofNat 99, Char.ofNat 107, Char.ofNat 69, Char.ofNat 120, Char.ofNat 112, Char.ofNat 114, Char.ofNat 101, Char.ofNat 115, Char.ofNat 115, Char.ofNat 105, Char.ofNat 111, Char.ofNat 110]), text := (String.ofList [Char.ofNat 123, Char.ofNat 32, Char.ofNat 105, Char.ofNat 111, Char.ofNat 58, Char.ofNat 58, Char.ofNat 116, Char.ofNat 105, Char.ofNat 99, Char.ofNat 107, Char.ofNat 32, Char.ofNat 115, Char.ofNat 101, Char.ofNat 101, Char.ofNat 100, Char.ofNat 59, Char.ofNat 32, Char.ofNat 92, Char.ofNat 97, Char.ofNat 114, Char.ofNat 103, Char.ofNat 117, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116, Char.ofNat 32, Char.ofNat 45, Char.ofNat 62, Char.ofNat 32, Char.ofNat 97, Char.ofNat 114, Char.ofNat 103, Char.ofNat 117, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116, Char.ofNat 32, Char.ofNat 125]) }, scope := ScopeTag.parameter 0, form := SourceForm.statementBlock { statements := [SourceStatement.expression 3], finalExpression := 2 }, childOrdinals := [3, 2], codeLabel := 1, instruction := Instruction.statementBlock { statements := [BlockStatement.expression 3], finalExpression := 2 } },
  { ordinal := 2, occurrence := 7, startByte := 65, endByte := 86, sourcePosition := { startByte := 65, endByte := 86, kind := (String.ofList [Char.ofNat 76, Char.ofNat 97, Char.ofNat 109, Char.ofNat 98, Char.ofNat 100, Char.ofNat 97, Char.ofNat 69, Char.ofNat 120, Char.ofNat 112, Char.ofNat 114, Char.ofNat 101, Char.ofNat 115, Char.ofNat 115, Char.ofNat 105, Char.ofNat 111, Char.ofNat 110]), text := (String.ofList [Char.ofNat 92, Char.ofNat 97, Char.ofNat 114, Char.ofNat 103, Char.ofNat 117, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116, Char.ofNat 32, Char.ofNat 45, Char.ofNat 62, Char.ofNat 32, Char.ofNat 97, Char.ofNat 114, Char.ofNat 103, Char.ofNat 117, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116]) }, scope := ScopeTag.expression 1, form := SourceForm.lambda ({ id := 1, spelling := (String.ofList [Char.ofNat 97, Char.ofNat 114, Char.ofNat 103, Char.ofNat 117, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116]), startByte := 66, endByte := 74, sourcePosition := { startByte := 65, endByte := 86, kind := (String.ofList [Char.ofNat 76, Char.ofNat 97, Char.ofNat 109, Char.ofNat 98, Char.ofNat 100, Char.ofNat 97, Char.ofNat 69, Char.ofNat 120, Char.ofNat 112, Char.ofNat 114, Char.ofNat 101, Char.ofNat 115, Char.ofNat 115, Char.ofNat 105, Char.ofNat 111, Char.ofNat 110]), text := (String.ofList [Char.ofNat 92, Char.ofNat 97, Char.ofNat 114, Char.ofNat 103, Char.ofNat 117, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116, Char.ofNat 32, Char.ofNat 45, Char.ofNat 62, Char.ofNat 32, Char.ofNat 97, Char.ofNat 114, Char.ofNat 103, Char.ofNat 117, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116]) }, scope := ScopeTag.expression 1, annotation := none }) 6, childOrdinals := [6], codeLabel := 2, instruction := Instruction.lambda 1 6 },
  { ordinal := 3, occurrence := 4, startByte := 59, endByte := 63, sourcePosition := { startByte := 59, endByte := 63, kind := (String.ofList [Char.ofNat 77, Char.ofNat 108, Char.ofNat 65, Char.ofNat 114, Char.ofNat 103, Char.ofNat 117, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116]), text := (String.ofList [Char.ofNat 115, Char.ofNat 101, Char.ofNat 101, Char.ofNat 100]) }, scope := ScopeTag.expression 1, form := SourceForm.apply (String.ofList [Char.ofNat 77, Char.ofNat 108, Char.ofNat 65, Char.ofNat 114, Char.ofNat 103, Char.ofNat 117, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116]) 4 5, childOrdinals := [4, 5], codeLabel := 3, instruction := Instruction.apply 4 5 },
  { ordinal := 4, occurrence := 5, startByte := 52, endByte := 58, sourcePosition := { startByte := 52, endByte := 58, kind := (String.ofList [Char.ofNat 80, Char.ofNat 97, Char.ofNat 116, Char.ofNat 104, Char.ofNat 84, Char.ofNat 97, Char.ofNat 105, Char.ofNat 108]), text := (String.ofList [Char.ofNat 58, Char.ofNat 58, Char.ofNat 116, Char.ofNat 105, Char.ofNat 99, Char.ofNat 107]) }, scope := ScopeTag.expression 1, form := SourceForm.operation ({ name := (String.ofList [Char.ofNat 116, Char.ofNat 105, Char.ofNat 99, Char.ofNat 107]), familyRealm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), familyPath := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), familyDeclaration := { startByte := 0, endByte := 32, kind := (String.ofList [Char.ofNat 65, Char.ofNat 99, Char.ofNat 116, Char.ofNat 68, Char.ofNat 101, Char.ofNat 99, Char.ofNat 108, Char.ofNat 97, Char.ofNat 114, Char.ofNat 97, Char.ofNat 116, Char.ofNat 105, Char.ofNat 111, Char.ofNat 110]), text := (String.ofList [Char.ofNat 97, Char.ofNat 99, Char.ofNat 116, Char.ofNat 32, Char.ofNat 105, Char.ofNat 111, Char.ofNat 58, Char.ofNat 10, Char.ofNat 32, Char.ofNat 32, Char.ofNat 32, Char.ofNat 32, Char.ofNat 111, Char.ofNat 117, Char.ofNat 114, Char.ofNat 32, Char.ofNat 116, Char.ofNat 105, Char.ofNat 99, Char.ofNat 107, Char.ofNat 58, Char.ofNat 32, Char.ofNat 105, Char.ofNat 110, Char.ofNat 116, Char.ofNat 32, Char.ofNat 45, Char.ofNat 62, Char.ofNat 32, Char.ofNat 105, Char.ofNat 110, Char.ofNat 116]) }, declaration := { startByte := 12, endByte := 32, kind := (String.ofList [Char.ofNat 66, Char.ofNat 105, Char.ofNat 110, Char.ofNat 100, Char.ofNat 105, Char.ofNat 110, Char.ofNat 103, Char.ofNat 83, Char.ofNat 116, Char.ofNat 97, Char.ofNat 116, Char.ofNat 101, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116]), text := (String.ofList [Char.ofNat 111, Char.ofNat 117, Char.ofNat 114, Char.ofNat 32, Char.ofNat 116, Char.ofNat 105, Char.ofNat 99, Char.ofNat 107, Char.ofNat 58, Char.ofNat 32, Char.ofNat 105, Char.ofNat 110, Char.ofNat 116, Char.ofNat 32, Char.ofNat 45, Char.ofNat 62, Char.ofNat 32, Char.ofNat 105, Char.ofNat 110, Char.ofNat 116]) }, namePosition := { startByte := 16, endByte := 20, kind := (String.ofList [Char.ofNat 73, Char.ofNat 100, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116, Char.ofNat 105, Char.ofNat 102, Char.ofNat 105, Char.ofNat 101, Char.ofNat 114, Char.ofNat 80, Char.ofNat 97, Char.ofNat 116, Char.ofNat 116, Char.ofNat 101, Char.ofNat 114, Char.ofNat 110]), text := (String.ofList [Char.ofNat 116, Char.ofNat 105, Char.ofNat 99, Char.ofNat 107]) }, signaturePosition := { startByte := 22, endByte := 32, kind := (String.ofList [Char.ofNat 84, Char.ofNat 121, Char.ofNat 112, Char.ofNat 101, Char.ofNat 69, Char.ofNat 120, Char.ofNat 112, Char.ofNat 114, Char.ofNat 101, Char.ofNat 115, Char.ofNat 115, Char.ofNat 105, Char.ofNat 111, Char.ofNat 110]), text := (String.ofList [Char.ofNat 105, Char.ofNat 110, Char.ofNat 116, Char.ofNat 32, Char.ofNat 45, Char.ofNat 62, Char.ofNat 32, Char.ofNat 105, Char.ofNat 110, Char.ofNat 116]) }, startByte := 12, endByte := 32, visibility := (String.ofList [Char.ofNat 79, Char.ofNat 117, Char.ofNat 114]), signature := AnnotationType.mk (SourceType.function (AnnotationType.mk (SourceType.int) (none)) (AnnotationType.mk (SourceType.int) (none))) (none) }), childOrdinals := [], codeLabel := 4, instruction := Instruction.operation ({ name := (String.ofList [Char.ofNat 116, Char.ofNat 105, Char.ofNat 99, Char.ofNat 107]), familyRealm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), familyPath := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), familyDeclaration := { startByte := 0, endByte := 32, kind := (String.ofList [Char.ofNat 65, Char.ofNat 99, Char.ofNat 116, Char.ofNat 68, Char.ofNat 101, Char.ofNat 99, Char.ofNat 108, Char.ofNat 97, Char.ofNat 114, Char.ofNat 97, Char.ofNat 116, Char.ofNat 105, Char.ofNat 111, Char.ofNat 110]), text := (String.ofList [Char.ofNat 97, Char.ofNat 99, Char.ofNat 116, Char.ofNat 32, Char.ofNat 105, Char.ofNat 111, Char.ofNat 58, Char.ofNat 10, Char.ofNat 32, Char.ofNat 32, Char.ofNat 32, Char.ofNat 32, Char.ofNat 111, Char.ofNat 117, Char.ofNat 114, Char.ofNat 32, Char.ofNat 116, Char.ofNat 105, Char.ofNat 99, Char.ofNat 107, Char.ofNat 58, Char.ofNat 32, Char.ofNat 105, Char.ofNat 110, Char.ofNat 116, Char.ofNat 32, Char.ofNat 45, Char.ofNat 62, Char.ofNat 32, Char.ofNat 105, Char.ofNat 110, Char.ofNat 116]) }, declaration := { startByte := 12, endByte := 32, kind := (String.ofList [Char.ofNat 66, Char.ofNat 105, Char.ofNat 110, Char.ofNat 100, Char.ofNat 105, Char.ofNat 110, Char.ofNat 103, Char.ofNat 83, Char.ofNat 116, Char.ofNat 97, Char.ofNat 116, Char.ofNat 101, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116]), text := (String.ofList [Char.ofNat 111, Char.ofNat 117, Char.ofNat 114, Char.ofNat 32, Char.ofNat 116, Char.ofNat 105, Char.ofNat 99, Char.ofNat 107, Char.ofNat 58, Char.ofNat 32, Char.ofNat 105, Char.ofNat 110, Char.ofNat 116, Char.ofNat 32, Char.ofNat 45, Char.ofNat 62, Char.ofNat 32, Char.ofNat 105, Char.ofNat 110, Char.ofNat 116]) }, namePosition := { startByte := 16, endByte := 20, kind := (String.ofList [Char.ofNat 73, Char.ofNat 100, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116, Char.ofNat 105, Char.ofNat 102, Char.ofNat 105, Char.ofNat 101, Char.ofNat 114, Char.ofNat 80, Char.ofNat 97, Char.ofNat 116, Char.ofNat 116, Char.ofNat 101, Char.ofNat 114, Char.ofNat 110]), text := (String.ofList [Char.ofNat 116, Char.ofNat 105, Char.ofNat 99, Char.ofNat 107]) }, signaturePosition := { startByte := 22, endByte := 32, kind := (String.ofList [Char.ofNat 84, Char.ofNat 121, Char.ofNat 112, Char.ofNat 101, Char.ofNat 69, Char.ofNat 120, Char.ofNat 112, Char.ofNat 114, Char.ofNat 101, Char.ofNat 115, Char.ofNat 115, Char.ofNat 105, Char.ofNat 111, Char.ofNat 110]), text := (String.ofList [Char.ofNat 105, Char.ofNat 110, Char.ofNat 116, Char.ofNat 32, Char.ofNat 45, Char.ofNat 62, Char.ofNat 32, Char.ofNat 105, Char.ofNat 110, Char.ofNat 116]) }, startByte := 12, endByte := 32, visibility := (String.ofList [Char.ofNat 79, Char.ofNat 117, Char.ofNat 114]), signature := AnnotationType.mk (SourceType.function (AnnotationType.mk (SourceType.int) (none)) (AnnotationType.mk (SourceType.int) (none))) (none) }) },
  { ordinal := 5, occurrence := 6, startByte := 59, endByte := 63, sourcePosition := { startByte := 59, endByte := 63, kind := (String.ofList [Char.ofNat 73, Char.ofNat 100, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116, Char.ofNat 105, Char.ofNat 102, Char.ofNat 105, Char.ofNat 101, Char.ofNat 114, Char.ofNat 69, Char.ofNat 120, Char.ofNat 112, Char.ofNat 114, Char.ofNat 101, Char.ofNat 115, Char.ofNat 115, Char.ofNat 105, Char.ofNat 111, Char.ofNat 110]), text := (String.ofList [Char.ofNat 115, Char.ofNat 101, Char.ofNat 101, Char.ofNat 100]) }, scope := ScopeTag.expression 1, form := SourceForm.name (String.ofList [Char.ofNat 115, Char.ofNat 101, Char.ofNat 101, Char.ofNat 100]) (Resolution.parameter 0), childOrdinals := [], codeLabel := 5, instruction := Instruction.name (Resolution.parameter 0) (String.ofList [Char.ofNat 79, Char.ofNat 98, Char.ofNat 115, Char.ofNat 101, Char.ofNat 114, Char.ofNat 118, Char.ofNat 101]) },
  { ordinal := 6, occurrence := 8, startByte := 77, endByte := 86, sourcePosition := { startByte := 77, endByte := 86, kind := (String.ofList [Char.ofNat 73, Char.ofNat 100, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116, Char.ofNat 105, Char.ofNat 102, Char.ofNat 105, Char.ofNat 101, Char.ofNat 114, Char.ofNat 69, Char.ofNat 120, Char.ofNat 112, Char.ofNat 114, Char.ofNat 101, Char.ofNat 115, Char.ofNat 115, Char.ofNat 105, Char.ofNat 111, Char.ofNat 110]), text := (String.ofList [Char.ofNat 32, Char.ofNat 97, Char.ofNat 114, Char.ofNat 103, Char.ofNat 117, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116]) }, scope := ScopeTag.parameter 1, form := SourceForm.name (String.ofList [Char.ofNat 97, Char.ofNat 114, Char.ofNat 103, Char.ofNat 117, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116]) (Resolution.parameter 1), childOrdinals := [], codeLabel := 6, instruction := Instruction.name (Resolution.parameter 1) (String.ofList [Char.ofNat 79, Char.ofNat 98, Char.ofNat 115, Char.ofNat 101, Char.ofNat 114, Char.ofNat 118, Char.ofNat 101]) },
]

end R315MakeArtifact

namespace R315Artifact
structure BindingUsePublication where
  makeRoot : R315MakeArtifact.RootBinding
  makeDefinitionRoot : R314Artifact.SourceRootIdentity
  declaration : R314Artifact.Position
  bindingAnnotation : Option R314Artifact.Annotation
  hirVisibility : String
  sourceIndexPublic : Bool
  initializer : Nat
  useSite : R314Artifact.RuntimeSite
  useOwner : R314Artifact.ExecutionOwner
  useStep : Nat
  useEnvironment : Nat
  useScope : R314Artifact.ScopeTag
  resolution : R314Artifact.Resolution
  consumes : String
  globalCell : Nat
  cellValue : Nat
  cellView : Nat
  cellInterface : R314Artifact.Interface
  providerSite : R314Artifact.RuntimeSite
  providerFormal : Nat
  providerBody : Nat
  providerEnvironment : Nat
  providerEnvironmentParent : Option Nat
  providerInterfaceIsValue : Bool
  useEnvironmentParent : Option Nat
  useEnvironmentBinderKind : Option String
  useEnvironmentBinderId : Option Nat
  useEnvironmentBinderCell : Option Nat
  useEnvironmentBinderOwner : Option R314Artifact.SourceRootIdentity
  dispatchBase : Option Nat
  dispatchWord : Option Nat
  substitution : Option Nat
  runId : Nat
  deriving Repr
structure ModuleBindingRow where
  name : String
  realm : String
  path : String
  sameNameOrdinal : Nat
  definitionRoot : R314Artifact.SourceRootIdentity
  declaration : R314Artifact.Position
  bindingAnnotation : Option R314Artifact.Annotation
  hirVisibility : String
  sourceIndexPublic : Bool
  runtimeCell : Nat
  deriving Repr
def moduleBindingsInSourceOrder : List ModuleBindingRow := [{ name := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, definitionRoot := R314Artifact.SourceRootIdentity.definition (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101]) (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]) (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]) 0, declaration := { startByte := 33, endByte := 88, kind := (String.ofList [Char.ofNat 66, Char.ofNat 105, Char.ofNat 110, Char.ofNat 100, Char.ofNat 105, Char.ofNat 110, Char.ofNat 103, Char.ofNat 83, Char.ofNat 116, Char.ofNat 97, Char.ofNat 116, Char.ofNat 101, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116]), text := (String.ofList [Char.ofNat 109, Char.ofNat 121, Char.ofNat 32, Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101, Char.ofNat 32, Char.ofNat 115, Char.ofNat 101, Char.ofNat 101, Char.ofNat 100, Char.ofNat 32, Char.ofNat 61, Char.ofNat 32, Char.ofNat 123, Char.ofNat 32, Char.ofNat 105, Char.ofNat 111, Char.ofNat 58, Char.ofNat 58, Char.ofNat 116, Char.ofNat 105, Char.ofNat 99, Char.ofNat 107, Char.ofNat 32, Char.ofNat 115, Char.ofNat 101, Char.ofNat 101, Char.ofNat 100, Char.ofNat 59, Char.ofNat 32, Char.ofNat 92, Char.ofNat 97, Char.ofNat 114, Char.ofNat 103, Char.ofNat 117, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116, Char.ofNat 32, Char.ofNat 45, Char.ofNat 62, Char.ofNat 32, Char.ofNat 97, Char.ofNat 114, Char.ofNat 103, Char.ofNat 117, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116, Char.ofNat 32, Char.ofNat 125]) }, bindingAnnotation := none, hirVisibility := (String.ofList [Char.ofNat 80, Char.ofNat 114, Char.ofNat 105, Char.ofNat 118, Char.ofNat 97, Char.ofNat 116, Char.ofNat 101]), sourceIndexPublic := false, runtimeCell := 0 }, { name := (String.ofList [Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, definitionRoot := R314Artifact.SourceRootIdentity.definition (String.ofList [Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121]) (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]) (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]) 0, declaration := { startByte := 89, endByte := 118, kind := (String.ofList [Char.ofNat 66, Char.ofNat 105, Char.ofNat 110, Char.ofNat 100, Char.ofNat 105, Char.ofNat 110, Char.ofNat 103, Char.ofNat 83, Char.ofNat 116, Char.ofNat 97, Char.ofNat 116, Char.ofNat 101, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116]), text := (String.ofList [Char.ofNat 109, Char.ofNat 121, Char.ofNat 32, Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121, Char.ofNat 32, Char.ofNat 118, Char.ofNat 97, Char.ofNat 108, Char.ofNat 117, Char.ofNat 101, Char.ofNat 32, Char.ofNat 61, Char.ofNat 32, Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101, Char.ofNat 32, Char.ofNat 49, Char.ofNat 32, Char.ofNat 118, Char.ofNat 97, Char.ofNat 108, Char.ofNat 117, Char.ofNat 101]) }, bindingAnnotation := none, hirVisibility := (String.ofList [Char.ofNat 80, Char.ofNat 114, Char.ofNat 105, Char.ofNat 118, Char.ofNat 97, Char.ofNat 116, Char.ofNat 101]), sourceIndexPublic := false, runtimeCell := 1 }, { name := (String.ofList [Char.ofNat 104, Char.ofNat 97, Char.ofNat 110, Char.ofNat 100, Char.ofNat 108, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, definitionRoot := R314Artifact.SourceRootIdentity.definition (String.ofList [Char.ofNat 104, Char.ofNat 97, Char.ofNat 110, Char.ofNat 100, Char.ofNat 108, Char.ofNat 101]) (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]) (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]) 0, declaration := { startByte := 119, endByte := 197, kind := (String.ofList [Char.ofNat 66, Char.ofNat 105, Char.ofNat 110, Char.ofNat 100, Char.ofNat 105, Char.ofNat 110, Char.ofNat 103, Char.ofNat 83, Char.ofNat 116, Char.ofNat 97, Char.ofNat 116, Char.ofNat 101, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116]), text := (String.ofList [Char.ofNat 109, Char.ofNat 121, Char.ofNat 32, Char.ofNat 104, Char.ofNat 97, Char.ofNat 110, Char.ofNat 100, Char.ofNat 108, Char.ofNat 101, Char.ofNat 32, Char.ofNat 40, Char.ofNat 116, Char.ofNat 104, Char.ofNat 117, Char.ofNat 110, Char.ofNat 107, Char.ofNat 58, Char.ofNat 91, Char.ofNat 105, Char.ofNat 111, Char.ofNat 93, Char.ofNat 32, Char.ofNat 105, Char.ofNat 110, Char.ofNat 116, Char.ofNat 41, Char.ofNat 32, Char.ofNat 61, Char.ofNat 32, Char.ofNat 99, Char.ofNat 97, Char.ofNat 116, Char.ofNat 99, Char.ofNat 104, Char.ofNat 32, Char.ofNat 116, Char.ofNat 104, Char.ofNat 117, Char.ofNat 110, Char.ofNat 107, Char.ofNat 32, Char.ofNat 123, Char.ofNat 32, Char.ofNat 105, Char.ofNat 111, Char.ofNat 58, Char.ofNat 58, Char.ofNat 116, Char.ofNat 105, Char.ofNat 99, Char.ofNat 107, Char.ofNat 40, Char.ofNat 112, Char.ofNat 41, Char.ofNat 44, Char.ofNat 32, Char.ofNat 107, Char.ofNat 32, Char.ofNat 45, Char.ofNat 62, Char.ofNat 32, Char.ofNat 104, Char.ofNat 97, Char.ofNat 110, Char.ofNat 100, Char.ofNat 108, Char.ofNat 101, Char.ofNat 32, Char.ofNat 123, Char.ofNat 32, Char.ofNat 107, Char.ofNat 32, Char.ofNat 49, Char.ofNat 48, Char.ofNat 32, Char.ofNat 125, Char.ofNat 32, Char.ofNat 125]) }, bindingAnnotation := none, hirVisibility := (String.ofList [Char.ofNat 80, Char.ofNat 114, Char.ofNat 105, Char.ofNat 118, Char.ofNat 97, Char.ofNat 116, Char.ofNat 101]), sourceIndexPublic := false, runtimeCell := 2 }, { name := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 105, Char.ofNat 110]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, definitionRoot := R314Artifact.SourceRootIdentity.definition (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 105, Char.ofNat 110]) (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]) (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]) 0, declaration := { startByte := 198, endByte := 226, kind := (String.ofList [Char.ofNat 66, Char.ofNat 105, Char.ofNat 110, Char.ofNat 100, Char.ofNat 105, Char.ofNat 110, Char.ofNat 103, Char.ofNat 83, Char.ofNat 116, Char.ofNat 97, Char.ofNat 116, Char.ofNat 101, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116]), text := (String.ofList [Char.ofNat 109, Char.ofNat 121, Char.ofNat 32, Char.ofNat 109, Char.ofNat 97, Char.ofNat 105, Char.ofNat 110, Char.ofNat 32, Char.ofNat 61, Char.ofNat 32, Char.ofNat 104, Char.ofNat 97, Char.ofNat 110, Char.ofNat 100, Char.ofNat 108, Char.ofNat 101, Char.ofNat 32, Char.ofNat 123, Char.ofNat 32, Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121, Char.ofNat 32, Char.ofNat 55, Char.ofNat 32, Char.ofNat 125]) }, bindingAnnotation := none, hirVisibility := (String.ofList [Char.ofNat 80, Char.ofNat 114, Char.ofNat 105, Char.ofNat 118, Char.ofNat 97, Char.ofNat 116, Char.ofNat 101]), sourceIndexPublic := false, runtimeCell := 3 }]
def makeBindingUse : BindingUsePublication := { makeRoot := R315MakeArtifact.rootBinding, makeDefinitionRoot := R314Artifact.SourceRootIdentity.definition (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101]) (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]) (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]) 0, declaration := { startByte := 33, endByte := 88, kind := (String.ofList [Char.ofNat 66, Char.ofNat 105, Char.ofNat 110, Char.ofNat 100, Char.ofNat 105, Char.ofNat 110, Char.ofNat 103, Char.ofNat 83, Char.ofNat 116, Char.ofNat 97, Char.ofNat 116, Char.ofNat 101, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116]), text := (String.ofList [Char.ofNat 109, Char.ofNat 121, Char.ofNat 32, Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101, Char.ofNat 32, Char.ofNat 115, Char.ofNat 101, Char.ofNat 101, Char.ofNat 100, Char.ofNat 32, Char.ofNat 61, Char.ofNat 32, Char.ofNat 123, Char.ofNat 32, Char.ofNat 105, Char.ofNat 111, Char.ofNat 58, Char.ofNat 58, Char.ofNat 116, Char.ofNat 105, Char.ofNat 99, Char.ofNat 107, Char.ofNat 32, Char.ofNat 115, Char.ofNat 101, Char.ofNat 101, Char.ofNat 100, Char.ofNat 59, Char.ofNat 32, Char.ofNat 92, Char.ofNat 97, Char.ofNat 114, Char.ofNat 103, Char.ofNat 117, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116, Char.ofNat 32, Char.ofNat 45, Char.ofNat 62, Char.ofNat 32, Char.ofNat 97, Char.ofNat 114, Char.ofNat 103, Char.ofNat 117, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116, Char.ofNat 32, Char.ofNat 125]) }, bindingAnnotation := none, hirVisibility := (String.ofList [Char.ofNat 80, Char.ofNat 114, Char.ofNat 105, Char.ofNat 118, Char.ofNat 97, Char.ofNat 116, Char.ofNat 101]), sourceIndexPublic := false, initializer := 0, useSite := { bindingName := (String.ofList [Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 14, startByte := 106, endByte := 110 }, useOwner := R314Artifact.ExecutionOwner.invocation 1, useStep := 18, useEnvironment := 2, useScope := R314Artifact.ScopeTag.parameter 0, resolution := R314Artifact.Resolution.moduleDef (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101]) (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]) (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]) 0, consumes := (String.ofList [Char.ofNat 79, Char.ofNat 98, Char.ofNat 115, Char.ofNat 101, Char.ofNat 114, Char.ofNat 118, Char.ofNat 101]), globalCell := 0, cellValue := 5, cellView := 6, cellInterface := R314Artifact.Interface.value, providerSite := { bindingName := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 2, startByte := 33, endByte := 88 }, providerFormal := 0, providerBody := 1, providerEnvironment := 0, providerEnvironmentParent := none, providerInterfaceIsValue := true, useEnvironmentParent := some 0, useEnvironmentBinderKind := some (String.ofList [Char.ofNat 112, Char.ofNat 97, Char.ofNat 114, Char.ofNat 97, Char.ofNat 109, Char.ofNat 101, Char.ofNat 116, Char.ofNat 101, Char.ofNat 114]), useEnvironmentBinderId := some 0, useEnvironmentBinderCell := some 5, useEnvironmentBinderOwner := some (R314Artifact.SourceRootIdentity.definition (String.ofList [Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121]) (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]) (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]) 0), dispatchBase := none, dispatchWord := none, substitution := none, runId := 129221288479048 }
end R315Artifact


namespace R323Artifact
open R314Artifact
def requestEvent : Nat := 0
def operation : String := (String.ofList [Char.ofNat 116, Char.ofNat 105, Char.ofNat 99, Char.ofNat 107])
def operationIdentity : R314Artifact.OperationIdentity := { name := (String.ofList [Char.ofNat 116, Char.ofNat 105, Char.ofNat 99, Char.ofNat 107]), familyRealm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), familyPath := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), familyDeclaration := { startByte := 0, endByte := 32, kind := (String.ofList [Char.ofNat 65, Char.ofNat 99, Char.ofNat 116, Char.ofNat 68, Char.ofNat 101, Char.ofNat 99, Char.ofNat 108, Char.ofNat 97, Char.ofNat 114, Char.ofNat 97, Char.ofNat 116, Char.ofNat 105, Char.ofNat 111, Char.ofNat 110]), text := (String.ofList [Char.ofNat 97, Char.ofNat 99, Char.ofNat 116, Char.ofNat 32, Char.ofNat 105, Char.ofNat 111, Char.ofNat 58, Char.ofNat 10, Char.ofNat 32, Char.ofNat 32, Char.ofNat 32, Char.ofNat 32, Char.ofNat 111, Char.ofNat 117, Char.ofNat 114, Char.ofNat 32, Char.ofNat 116, Char.ofNat 105, Char.ofNat 99, Char.ofNat 107, Char.ofNat 58, Char.ofNat 32, Char.ofNat 105, Char.ofNat 110, Char.ofNat 116, Char.ofNat 32, Char.ofNat 45, Char.ofNat 62, Char.ofNat 32, Char.ofNat 105, Char.ofNat 110, Char.ofNat 116]) }, declaration := { startByte := 12, endByte := 32, kind := (String.ofList [Char.ofNat 66, Char.ofNat 105, Char.ofNat 110, Char.ofNat 100, Char.ofNat 105, Char.ofNat 110, Char.ofNat 103, Char.ofNat 83, Char.ofNat 116, Char.ofNat 97, Char.ofNat 116, Char.ofNat 101, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116]), text := (String.ofList [Char.ofNat 111, Char.ofNat 117, Char.ofNat 114, Char.ofNat 32, Char.ofNat 116, Char.ofNat 105, Char.ofNat 99, Char.ofNat 107, Char.ofNat 58, Char.ofNat 32, Char.ofNat 105, Char.ofNat 110, Char.ofNat 116, Char.ofNat 32, Char.ofNat 45, Char.ofNat 62, Char.ofNat 32, Char.ofNat 105, Char.ofNat 110, Char.ofNat 116]) }, namePosition := { startByte := 16, endByte := 20, kind := (String.ofList [Char.ofNat 73, Char.ofNat 100, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116, Char.ofNat 105, Char.ofNat 102, Char.ofNat 105, Char.ofNat 101, Char.ofNat 114, Char.ofNat 80, Char.ofNat 97, Char.ofNat 116, Char.ofNat 116, Char.ofNat 101, Char.ofNat 114, Char.ofNat 110]), text := (String.ofList [Char.ofNat 116, Char.ofNat 105, Char.ofNat 99, Char.ofNat 107]) }, signaturePosition := { startByte := 22, endByte := 32, kind := (String.ofList [Char.ofNat 84, Char.ofNat 121, Char.ofNat 112, Char.ofNat 101, Char.ofNat 69, Char.ofNat 120, Char.ofNat 112, Char.ofNat 114, Char.ofNat 101, Char.ofNat 115, Char.ofNat 115, Char.ofNat 105, Char.ofNat 111, Char.ofNat 110]), text := (String.ofList [Char.ofNat 105, Char.ofNat 110, Char.ofNat 116, Char.ofNat 32, Char.ofNat 45, Char.ofNat 62, Char.ofNat 32, Char.ofNat 105, Char.ofNat 110, Char.ofNat 116]) }, startByte := 12, endByte := 32, visibility := (String.ofList [Char.ofNat 79, Char.ofNat 117, Char.ofNat 114]), signature := R314Artifact.AnnotationType.mk (R314Artifact.SourceType.function (R314Artifact.AnnotationType.mk (R314Artifact.SourceType.int) (none)) (R314Artifact.AnnotationType.mk (R314Artifact.SourceType.int) (none))) (none) }
def requestSite : R314Artifact.RuntimeSite := { bindingName := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 4, startByte := 59, endByte := 63 }
def requestOwner : R314Artifact.ExecutionOwner := R314Artifact.ExecutionOwner.invocation 2
def requestOwnerWasLive : Bool := true
def payload : R314Artifact.Received := { value := 7, view := 8, interface := R314Artifact.Interface.value, dispatch := none }
def payloadRuntimeValue : R314Artifact.RuntimeValue := { source := { bindingName := (String.ofList [Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 15, startByte := 111, endByte := 112 }, kind := R314Artifact.ValueKind.integer (String.ofList [Char.ofNat 49]) }
def templateHandle : Nat := 0
def templateRoot : Nat := 6
def templateNodeCount : Nat := 7
def captureOwner : R314Artifact.ExecutionOwner := R314Artifact.ExecutionOwner.invocation 0
structure R323CodeRef where
  label : Nat
  site : R314Artifact.RuntimeSite
  deriving Repr
structure R323CalleeFrame where
  frameId : Nat
  callee : Option R323CodeRef
  argument : R323CodeRef
  environment : Nat
  site : R314Artifact.RuntimeSite
  deriving Repr
structure R323BlockExpressionFrame where
  codeLabel : Nat
  codeSite : R314Artifact.RuntimeSite
  next : Nat
  environment : Nat
  deriving Repr
structure R323RootCompReturn where
  view : Nat
  receipt : Nat
  occurrence : Nat
  deriving Repr
inductive R323Frame where
  | callee (frame : R323CalleeFrame)
  | blockExpression (frame : R323BlockExpressionFrame)
  | rootCompReturn (execution : R323RootCompReturn)
  | owner (owner : R314Artifact.ExecutionOwner)
  deriving Repr
def savedFrameOrder : List R323Frame := [R323Frame.blockExpression { codeLabel := 1, codeSite := { bindingName := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 3, startByte := 48, endByte := 88 }, next := 1, environment := 3 }, R323Frame.owner (R314Artifact.ExecutionOwner.invocation 2), R323Frame.callee { frameId := 2, callee := some ({ label := 9, site := { bindingName := (String.ofList [Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 13, startByte := 111, endByte := 112 } }), argument := { label := 10, site := { bindingName := (String.ofList [Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 16, startByte := 113, endByte := 118 } }, environment := 2, site := { bindingName := (String.ofList [Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 12, startByte := 113, endByte := 118 } }, R323Frame.owner (R314Artifact.ExecutionOwner.invocation 1), R323Frame.rootCompReturn { view := 2, receipt := 2, occurrence := 0 }]
def templateFrameOrder : List R323Frame := [R323Frame.blockExpression { codeLabel := 1, codeSite := { bindingName := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 3, startByte := 48, endByte := 88 }, next := 1, environment := 3 }, R323Frame.owner (R314Artifact.ExecutionOwner.invocation 2), R323Frame.callee { frameId := 2, callee := some ({ label := 9, site := { bindingName := (String.ofList [Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 13, startByte := 111, endByte := 112 } }), argument := { label := 10, site := { bindingName := (String.ofList [Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 16, startByte := 113, endByte := 118 } }, environment := 2, site := { bindingName := (String.ofList [Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 12, startByte := 113, endByte := 118 } }, R323Frame.owner (R314Artifact.ExecutionOwner.invocation 1), R323Frame.rootCompReturn { view := 2, receipt := 2, occurrence := 0 }]
def templateInnerByNode : List (Option Nat) := [none, some 0, some 1, some 2, some 3, some 4, some 5]
def outerCalleeFrame : Nat := 2
def outerCalleeSite : R314Artifact.RuntimeSite := { bindingName := (String.ofList [Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 12, startByte := 113, endByte := 118 }
def resumeRequestEvent : Nat := 0
def resumeTemplateHandle : Nat := 0
def responseValue : Nat := 14
def responseView : Nat := 16
def response : R314Artifact.Received := { value := 14, view := 16, interface := R314Artifact.Interface.value, dispatch := none }
def responseRuntimeValue : R314Artifact.RuntimeValue := { source := { bindingName := (String.ofList [Char.ofNat 104, Char.ofNat 97, Char.ofNat 110, Char.ofNat 100, Char.ofNat 108, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 27, startByte := 191, endByte := 193 }, kind := R314Artifact.ValueKind.integer (String.ofList [Char.ofNat 49, Char.ofNat 48]) }
def responseStep : Nat := 48
def responseSite : R314Artifact.RuntimeSite := { bindingName := (String.ofList [Char.ofNat 104, Char.ofNat 97, Char.ofNat 110, Char.ofNat 100, Char.ofNat 108, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 25, startByte := 191, endByte := 193 }
def responseOwner : R314Artifact.ExecutionOwner := R314Artifact.ExecutionOwner.invocation 5
def responseOwnerWasLive : Bool := true
def responseHoleNode : Nat := 0
def responseHoleOwner : R314Artifact.ExecutionOwner := R314Artifact.ExecutionOwner.invocation 7
def responseHoleOwnerWasLive : Bool := true
def responseHoleStep : Nat := 55
def selectedReceiverActivation : Nat := 8
def selectedReceiverOwner : R314Artifact.ExecutionOwner := R314Artifact.ExecutionOwner.invocation 8
def selectedReceiverPreviousOwner : R314Artifact.ExecutionOwner := R314Artifact.ExecutionOwner.invocation 6
def selectedReceiverCallSite : R314Artifact.RuntimeSite := { bindingName := (String.ofList [Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 12, startByte := 113, endByte := 118 }
def selectedReceiverProviderSite : R314Artifact.RuntimeSite := { bindingName := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 7, startByte := 65, endByte := 86 }
def selectedReceiverReturnValue : Nat := 4
def selectedReceiverReturnView : Nat := 5
def selectedReceiverReturnInterface : R314Artifact.Interface := R314Artifact.Interface.value
def selectedReceiverReturnDispatch : Option Nat := none
def selectedReceiverReturnRuntimeValue : R314Artifact.RuntimeValue := { source := { bindingName := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 105, Char.ofNat 110]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 35, startByte := 223, endByte := 224 }, kind := R314Artifact.ValueKind.integer (String.ofList [Char.ofNat 55]) }
def selectedReceiverReturnStep : Nat := 63
def selectedReceiverPostExitActivation : Nat := 8
def selectedReceiverPostExitPreviousOwner : R314Artifact.ExecutionOwner := R314Artifact.ExecutionOwner.invocation 6
def selectedReceiverPostExitOwnerBefore : R314Artifact.ExecutionOwner := R314Artifact.ExecutionOwner.invocation 8
def selectedReceiverPostExitOwnerAfter : R314Artifact.ExecutionOwner := R314Artifact.ExecutionOwner.invocation 6
def selectedReceiverPostExitNativeActiveReceiversBefore : List Nat := [0, 4, 5, 6, 8]
def selectedReceiverPostExitNativeActiveReceiversAfter : List Nat := [0, 4, 5, 6]
structure R338InvocationSnapshot where
  id : Nat
  call : R314Artifact.RuntimeSite
  provider : R314Artifact.RuntimeSite
  active : Bool
  deriving Repr
def selectedReceiverPostExitInvocationTableBefore : List R338InvocationSnapshot := [{ id := 0, call := { bindingName := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 105, Char.ofNat 110]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 30, startByte := 215, endByte := 226 }, provider := { bindingName := (String.ofList [Char.ofNat 104, Char.ofNat 97, Char.ofNat 110, Char.ofNat 100, Char.ofNat 108, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 19, startByte := 119, endByte := 197 }, active := true }, { id := 1, call := { bindingName := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 105, Char.ofNat 110]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 33, startByte := 223, endByte := 224 }, provider := { bindingName := (String.ofList [Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 11, startByte := 89, endByte := 118 }, active := false }, { id := 2, call := { bindingName := (String.ofList [Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 13, startByte := 111, endByte := 112 }, provider := { bindingName := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 2, startByte := 33, endByte := 88 }, active := false }, { id := 3, call := { bindingName := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 4, startByte := 59, endByte := 63 }, provider := { bindingName := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 5, startByte := 52, endByte := 58 }, active := false }, { id := 4, call := { bindingName := (String.ofList [Char.ofNat 104, Char.ofNat 97, Char.ofNat 110, Char.ofNat 100, Char.ofNat 108, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 22, startByte := 187, endByte := 195 }, provider := { bindingName := (String.ofList [Char.ofNat 104, Char.ofNat 97, Char.ofNat 110, Char.ofNat 100, Char.ofNat 108, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 19, startByte := 119, endByte := 197 }, active := true }, { id := 5, call := { bindingName := (String.ofList [Char.ofNat 104, Char.ofNat 97, Char.ofNat 110, Char.ofNat 100, Char.ofNat 108, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 25, startByte := 191, endByte := 193 }, provider := { bindingName := (String.ofList [Char.ofNat 104, Char.ofNat 97, Char.ofNat 110, Char.ofNat 100, Char.ofNat 108, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 20, startByte := 148, endByte := 197 }, active := true }, { id := 6, call := { bindingName := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 105, Char.ofNat 110]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 33, startByte := 223, endByte := 224 }, provider := { bindingName := (String.ofList [Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 11, startByte := 89, endByte := 118 }, active := true }, { id := 7, call := { bindingName := (String.ofList [Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 13, startByte := 111, endByte := 112 }, provider := { bindingName := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 2, startByte := 33, endByte := 88 }, active := false }, { id := 8, call := { bindingName := (String.ofList [Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 12, startByte := 113, endByte := 118 }, provider := { bindingName := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 7, startByte := 65, endByte := 86 }, active := true }]
def selectedReceiverPostExitInvocationTableAfter : List R338InvocationSnapshot := [{ id := 0, call := { bindingName := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 105, Char.ofNat 110]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 30, startByte := 215, endByte := 226 }, provider := { bindingName := (String.ofList [Char.ofNat 104, Char.ofNat 97, Char.ofNat 110, Char.ofNat 100, Char.ofNat 108, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 19, startByte := 119, endByte := 197 }, active := true }, { id := 1, call := { bindingName := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 105, Char.ofNat 110]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 33, startByte := 223, endByte := 224 }, provider := { bindingName := (String.ofList [Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 11, startByte := 89, endByte := 118 }, active := false }, { id := 2, call := { bindingName := (String.ofList [Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 13, startByte := 111, endByte := 112 }, provider := { bindingName := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 2, startByte := 33, endByte := 88 }, active := false }, { id := 3, call := { bindingName := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 4, startByte := 59, endByte := 63 }, provider := { bindingName := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 5, startByte := 52, endByte := 58 }, active := false }, { id := 4, call := { bindingName := (String.ofList [Char.ofNat 104, Char.ofNat 97, Char.ofNat 110, Char.ofNat 100, Char.ofNat 108, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 22, startByte := 187, endByte := 195 }, provider := { bindingName := (String.ofList [Char.ofNat 104, Char.ofNat 97, Char.ofNat 110, Char.ofNat 100, Char.ofNat 108, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 19, startByte := 119, endByte := 197 }, active := true }, { id := 5, call := { bindingName := (String.ofList [Char.ofNat 104, Char.ofNat 97, Char.ofNat 110, Char.ofNat 100, Char.ofNat 108, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 25, startByte := 191, endByte := 193 }, provider := { bindingName := (String.ofList [Char.ofNat 104, Char.ofNat 97, Char.ofNat 110, Char.ofNat 100, Char.ofNat 108, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 20, startByte := 148, endByte := 197 }, active := true }, { id := 6, call := { bindingName := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 105, Char.ofNat 110]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 33, startByte := 223, endByte := 224 }, provider := { bindingName := (String.ofList [Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 11, startByte := 89, endByte := 118 }, active := true }, { id := 7, call := { bindingName := (String.ofList [Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 13, startByte := 111, endByte := 112 }, provider := { bindingName := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 2, startByte := 33, endByte := 88 }, active := false }, { id := 8, call := { bindingName := (String.ofList [Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 12, startByte := 113, endByte := 118 }, provider := { bindingName := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 7, startByte := 65, endByte := 86 }, active := false }]
def selectedReceiverPostExitCallSite : R314Artifact.RuntimeSite := { bindingName := (String.ofList [Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 12, startByte := 113, endByte := 118 }
def selectedReceiverPostExitProviderSite : R314Artifact.RuntimeSite := { bindingName := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 7, startByte := 65, endByte := 86 }
def selectedReceiverPostExitReturnValue : Nat := 4
def selectedReceiverPostExitReturnView : Nat := 5
def selectedReceiverPostExitReturnInterface : R314Artifact.Interface := R314Artifact.Interface.value
def selectedReceiverPostExitReturnDispatch : Option Nat := none
def selectedReceiverPostExitIncoming : R314Artifact.Received := { value := 4, view := 5, interface := R314Artifact.Interface.value, dispatch := none }
def selectedReceiverPostExitStepBefore : Nat := 63
def selectedReceiverPostExitStepAfter : Nat := 63
def selectedDefinitionResult : Nat := 4
def selectedDefinitionResultView : Nat := 5
def selectedDefinitionResultOwner : R314Artifact.ExecutionOwner := R314Artifact.ExecutionOwner.moduleRun
def selectedDefinitionResultInterface : R314Artifact.Interface := R314Artifact.Interface.value
def selectedDefinitionResultDispatch : Option Nat := none
def selectedDefinitionResultRuntimeValue : R314Artifact.RuntimeValue := { source := { bindingName := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 105, Char.ofNat 110]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 35, startByte := 223, endByte := 224 }, kind := R314Artifact.ValueKind.integer (String.ofList [Char.ofNat 55]) }
def selectedDefinitionResultStep : Nat := 73
structure OwnerReplay where
  node : Nat
  original : R314Artifact.ExecutionOwner
  resolved : R314Artifact.ExecutionOwner
  resolvedWasActive : Bool
  owner : R314Artifact.ExecutionOwner
  owned : Bool
  previous : R314Artifact.ExecutionOwner
  ownerLive : Bool
  currentOwnerAfter : R314Artifact.ExecutionOwner
  control : List (Nat × Nat)
  callSite : Option R314Artifact.RuntimeSite
  providerSite : Option R314Artifact.RuntimeSite
  deriving Repr
def ownerReplay : List OwnerReplay := [{ node := 6, original := R314Artifact.ExecutionOwner.invocation 0, resolved := R314Artifact.ExecutionOwner.invocation 0, resolvedWasActive := true, owner := R314Artifact.ExecutionOwner.invocation 0, owned := false, previous := R314Artifact.ExecutionOwner.invocation 5, ownerLive := true, currentOwnerAfter := R314Artifact.ExecutionOwner.invocation 0, control := [], callSite := some ({ bindingName := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 105, Char.ofNat 110]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 30, startByte := 215, endByte := 226 }), providerSite := some ({ bindingName := (String.ofList [Char.ofNat 104, Char.ofNat 97, Char.ofNat 110, Char.ofNat 100, Char.ofNat 108, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 19, startByte := 119, endByte := 197 }) }, { node := 4, original := R314Artifact.ExecutionOwner.invocation 1, resolved := R314Artifact.ExecutionOwner.invocation 1, resolvedWasActive := false, owner := R314Artifact.ExecutionOwner.invocation 6, owned := true, previous := R314Artifact.ExecutionOwner.invocation 0, ownerLive := true, currentOwnerAfter := R314Artifact.ExecutionOwner.invocation 6, control := [(0, 0)], callSite := some ({ bindingName := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 105, Char.ofNat 110]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 33, startByte := 223, endByte := 224 }), providerSite := some ({ bindingName := (String.ofList [Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 11, startByte := 89, endByte := 118 }) }, { node := 2, original := R314Artifact.ExecutionOwner.invocation 2, resolved := R314Artifact.ExecutionOwner.invocation 2, resolvedWasActive := false, owner := R314Artifact.ExecutionOwner.invocation 7, owned := true, previous := R314Artifact.ExecutionOwner.invocation 6, ownerLive := true, currentOwnerAfter := R314Artifact.ExecutionOwner.invocation 7, control := [(0, 0), (1, 6)], callSite := some ({ bindingName := (String.ofList [Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 13, startByte := 111, endByte := 112 }), providerSite := some ({ bindingName := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 2, startByte := 33, endByte := 88 }) }]
end R323Artifact
-- END EXACT R338 GENERATED PAYLOAD
-- BEGIN EXACT R335 HISTORICAL WRAPPER (leading import hoisted)
namespace Legacy
namespace R314Artifact

structure Position where
  startByte : Nat
  endByte : Nat
  kind : String
  text : String
  deriving Repr
inductive ScopeTag where
  | definition | moduleExpression | sourceMember
  | expression (id : Nat) | parameter (id : Nat) | localInitializer (id : Nat)
  | catchArm (id : Nat) (arm : Position)
  deriving Repr
structure RootBinding where
  name : String
  realm : String
  path : String
  sameNameOrdinal : Nat
  deriving Repr
inductive ExecutionOwner where | moduleRun | invocation (id : Nat) deriving Repr
inductive SourceRootIdentity where
  | definition (bindingName realm path : String) (sameNameOrdinal : Nat)
  | expression (occurrence : Nat)
  | member (realm path kind : String) (declaration member : Position)
  deriving Repr
structure RuntimeSite where
  bindingName : String
  realm : String
  path : String
  sameNameOrdinal : Nat
  occurrence : Nat
  startByte : Nat
  endByte : Nat
  deriving Repr
inductive Interface where | value | computation deriving Repr
structure Received where
  value : Nat
  view : Nat
  interface : Interface
  dispatch : Option Nat
  deriving Repr
structure RuntimeCell where
  value : Option Received
  deriving Repr
structure RuntimeEnvironment where
  parent : Option Nat
  binderKind : Option String
  binderId : Option Nat
  binderCell : Option Nat
  binderOwner : Option SourceRootIdentity
  dispatchBase : Option Nat
  dispatchWord : Option Nat
  substitution : Option Nat
  deriving Repr
inductive ReceivingViewKind where
  | ordinary | rootComp | callbackEntry (id : Nat) | callbackResult (id : Nat)
  deriving Repr
structure ReceivingView where
  index : Nat
  value : Nat
  image : Option Nat
  unknown : Bool
  kind : ReceivingViewKind
  deriving Repr
structure ImageLink where
  image : Nat
  boundary : Nat
  receiver : Nat
  deriving Repr
structure ViewImageChain where
  view : Nat
  links : List ImageLink
  deriving Repr
inductive RuntimeEvent where
  | request (step order id : Nat) (site : RuntimeSite) (owner : ExecutionOwner)
  | pendingCallee (step order request frame argumentLabel environment : Nat)
      (calleeLabel : Option Nat) (requestSite applySite : RuntimeSite) (owner : ExecutionOwner)
  | calleeReturn (step order frame argumentLabel environment value view : Nat)
      (calleeLabel : Option Nat) (site : RuntimeSite) (owner : ExecutionOwner)
      (interface : Interface) (provider : RuntimeSite)
  | delay (value code environment view : Nat)
  | nameLookup (step order environment parameter cell value view : Nat)
      (site : RuntimeSite) (owner : ExecutionOwner) (consumption : String)
  | nameReceipt (step order receipt value view : Nat)
      (site : RuntimeSite) (owner : ExecutionOwner) (consumption : String)
  | valueBind (step order receiver parameter cell environment value view : Nat) (interface : Interface)
  deriving Repr
inductive Resolution where
  | moduleDef (name : String) (realm : String) (path : String) (ordinal : Nat)
  | parameter (id : Nat) | local (id : Nat) | catchBinder (id : Nat) | caseBinder (id : Nat)
  | unresolved | ambiguous
  deriving Repr
structure EffectId where
  realm : String
  path : String
  declaration : Position
  deriving Repr
structure EffectRow where
  position : Position
  concrete : List EffectId
  variables : List String
  deriving Repr
mutual
inductive SourceType where
  | unit | int | bool | str | variable (name : String) | hole (position : Position)
  | tuple (items : List AnnotationType) | function (argument result : AnnotationType)
  deriving Repr
inductive AnnotationType where
  | mk (value : SourceType) (effects : Option EffectRow)
  deriving Repr
end
structure Annotation where
  owner : String
  position : Position
  type : AnnotationType
  deriving Repr
structure OperationIdentity where
  name : String
  familyRealm : String
  familyPath : String
  familyDeclaration : Position
  declaration : Position
  namePosition : Position
  signaturePosition : Position
  startByte : Nat
  endByte : Nat
  visibility : String
  signature : AnnotationType
  deriving Repr
inductive ValueKind where
  | unit | integer (value : String) | boolean (value : Bool) | string (value : String)
  | primitive (name : String) | tuple (items : List Received)
  | variant (tag : String) (items : List Received)
  | record (fields : List (String × Received)) | closure | computation
  | operation (identity : OperationIdentity)
  deriving Repr
structure RuntimeValue where
  source : RuntimeSite
  kind : ValueKind
  deriving Repr
structure ReturnSnapshot where
  runId : Nat
  frame : Nat
  applySite : RuntimeSite
  argumentLabel : Nat
  callerEnvironment : Nat
  cells : List RuntimeCell
  environments : List RuntimeEnvironment
  values : List RuntimeValue
  receivingViews : List ReceivingView
  receivingImageChains : List ViewImageChain
  sourceNameInitialization : Option Received
  sourceNameParameter : Option Nat
  receivingScanTruncated : Bool
  deriving Repr
structure Formal where
  id : Nat
  spelling : String
  startByte : Nat
  endByte : Nat
  sourcePosition : Position
  scope : ScopeTag
  annotation : Option Annotation
  deriving Repr
inductive BlockStatement where
  | expression (code : Nat) | binding (ordinal localId initializer : Nat)
  deriving Repr
inductive SourceStatement where
  | expression (source : Nat) | binding (ordinal localId initializer : Nat)
  deriving Repr
structure SourceStatementBlock where
  statements : List SourceStatement
  finalExpression : Nat
  deriving Repr
structure InstructionStatementBlock where
  statements : List BlockStatement
  finalExpression : Nat
  deriving Repr
inductive SourceForm where
  | unit | integer (value : String) | boolean (value : Bool) | string (value : String)
  | decodedString (value : String) | name (spelling : String) (resolution : Resolution)
  | apply (syntaxKind : String) (callee argument : Nat) | group (inner : Nat)
  | ascription (annotation : Annotation) (inner : Nat) | lambda (formal : Formal) (body : Nat)
  | operation (identity : OperationIdentity) | block (bindings : List (Nat × Nat)) (finalExpression : Nat)
  | statementBlock (block : SourceStatementBlock)
  deriving Repr
inductive Instruction where
  | unit | integer (value : String) | boolean (value : Bool) | string (value : String)
  | decodedString (value : String) | name (resolution : Resolution) (consumption : String)
  | apply (callee argument : Nat) | forward (inner : Nat) | lambda (formalId body : Nat)
  | operation (identity : OperationIdentity) | block (bindings : List (Nat × Nat)) (finalExpression : Nat)
  | statementBlock (block : InstructionStatementBlock)
  deriving Repr
structure SourceNode where
  ordinal : Nat
  occurrence : Nat
  startByte : Nat
  endByte : Nat
  sourcePosition : Position
  scope : ScopeTag
  form : SourceForm
  childOrdinals : List Nat
  codeLabel : Nat
  instruction : Instruction
  deriving Repr
def sourceText : String := (String.ofList [Char.ofNat 97, Char.ofNat 99, Char.ofNat 116, Char.ofNat 32, Char.ofNat 105, Char.ofNat 111, Char.ofNat 58, Char.ofNat 10, Char.ofNat 32, Char.ofNat 32, Char.ofNat 32, Char.ofNat 32, Char.ofNat 111, Char.ofNat 117, Char.ofNat 114, Char.ofNat 32, Char.ofNat 116, Char.ofNat 105, Char.ofNat 99, Char.ofNat 107, Char.ofNat 58, Char.ofNat 32, Char.ofNat 105, Char.ofNat 110, Char.ofNat 116, Char.ofNat 32, Char.ofNat 45, Char.ofNat 62, Char.ofNat 32, Char.ofNat 105, Char.ofNat 110, Char.ofNat 116, Char.ofNat 10, Char.ofNat 109, Char.ofNat 121, Char.ofNat 32, Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101, Char.ofNat 32, Char.ofNat 115, Char.ofNat 101, Char.ofNat 101, Char.ofNat 100, Char.ofNat 32, Char.ofNat 61, Char.ofNat 32, Char.ofNat 123, Char.ofNat 32, Char.ofNat 105, Char.ofNat 111, Char.ofNat 58, Char.ofNat 58, Char.ofNat 116, Char.ofNat 105, Char.ofNat 99, Char.ofNat 107, Char.ofNat 32, Char.ofNat 115, Char.ofNat 101, Char.ofNat 101, Char.ofNat 100, Char.ofNat 59, Char.ofNat 32, Char.ofNat 92, Char.ofNat 97, Char.ofNat 114, Char.ofNat 103, Char.ofNat 117, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116, Char.ofNat 32, Char.ofNat 45, Char.ofNat 62, Char.ofNat 32, Char.ofNat 97, Char.ofNat 114, Char.ofNat 103, Char.ofNat 117, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116, Char.ofNat 32, Char.ofNat 125, Char.ofNat 10, Char.ofNat 109, Char.ofNat 121, Char.ofNat 32, Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121, Char.ofNat 32, Char.ofNat 118, Char.ofNat 97, Char.ofNat 108, Char.ofNat 117, Char.ofNat 101, Char.ofNat 32, Char.ofNat 61, Char.ofNat 32, Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101, Char.ofNat 32, Char.ofNat 49, Char.ofNat 32, Char.ofNat 118, Char.ofNat 97, Char.ofNat 108, Char.ofNat 117, Char.ofNat 101, Char.ofNat 10, Char.ofNat 109, Char.ofNat 121, Char.ofNat 32, Char.ofNat 104, Char.ofNat 97, Char.ofNat 110, Char.ofNat 100, Char.ofNat 108, Char.ofNat 101, Char.ofNat 32, Char.ofNat 40, Char.ofNat 116, Char.ofNat 104, Char.ofNat 117, Char.ofNat 110, Char.ofNat 107, Char.ofNat 58, Char.ofNat 91, Char.ofNat 105, Char.ofNat 111, Char.ofNat 93, Char.ofNat 32, Char.ofNat 105, Char.ofNat 110, Char.ofNat 116, Char.ofNat 41, Char.ofNat 32, Char.ofNat 61, Char.ofNat 32, Char.ofNat 99, Char.ofNat 97, Char.ofNat 116, Char.ofNat 99, Char.ofNat 104, Char.ofNat 32, Char.ofNat 116, Char.ofNat 104, Char.ofNat 117, Char.ofNat 110, Char.ofNat 107, Char.ofNat 32, Char.ofNat 123, Char.ofNat 32, Char.ofNat 105, Char.ofNat 111, Char.ofNat 58, Char.ofNat 58, Char.ofNat 116, Char.ofNat 105, Char.ofNat 99, Char.ofNat 107, Char.ofNat 40, Char.ofNat 112, Char.ofNat 41, Char.ofNat 44, Char.ofNat 32, Char.ofNat 107, Char.ofNat 32, Char.ofNat 45, Char.ofNat 62, Char.ofNat 32, Char.ofNat 104, Char.ofNat 97, Char.ofNat 110, Char.ofNat 100, Char.ofNat 108, Char.ofNat 101, Char.ofNat 32, Char.ofNat 123, Char.ofNat 32, Char.ofNat 107, Char.ofNat 32, Char.ofNat 49, Char.ofNat 48, Char.ofNat 32, Char.ofNat 125, Char.ofNat 32, Char.ofNat 125, Char.ofNat 10, Char.ofNat 109, Char.ofNat 121, Char.ofNat 32, Char.ofNat 109, Char.ofNat 97, Char.ofNat 105, Char.ofNat 110, Char.ofNat 32, Char.ofNat 61, Char.ofNat 32, Char.ofNat 104, Char.ofNat 97, Char.ofNat 110, Char.ofNat 100, Char.ofNat 108, Char.ofNat 101, Char.ofNat 32, Char.ofNat 123, Char.ofNat 32, Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121, Char.ofNat 32, Char.ofNat 55, Char.ofNat 32, Char.ofNat 125])
def rootBinding : RootBinding := { name := (String.ofList [Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0 }
def rootInitializer : Nat := 0
def rootFormals : List Formal := [
  { id := 0, spelling := (String.ofList [Char.ofNat 118, Char.ofNat 97, Char.ofNat 108, Char.ofNat 117, Char.ofNat 101]), startByte := 98, endByte := 103, sourcePosition := { startByte := 98, endByte := 103, kind := (String.ofList [Char.ofNat 73, Char.ofNat 100, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116, Char.ofNat 105, Char.ofNat 102, Char.ofNat 105, Char.ofNat 101, Char.ofNat 114, Char.ofNat 80, Char.ofNat 97, Char.ofNat 116, Char.ofNat 116, Char.ofNat 101, Char.ofNat 114, Char.ofNat 110]), text := (String.ofList [Char.ofNat 118, Char.ofNat 97, Char.ofNat 108, Char.ofNat 117, Char.ofNat 101]) }, scope := ScopeTag.definition, annotation := none },
]
def nodes : List SourceNode := [
  { ordinal := 0, occurrence := 11, startByte := 89, endByte := 118, sourcePosition := { startByte := 89, endByte := 118, kind := (String.ofList [Char.ofNat 66, Char.ofNat 105, Char.ofNat 110, Char.ofNat 100, Char.ofNat 105, Char.ofNat 110, Char.ofNat 103, Char.ofNat 83, Char.ofNat 116, Char.ofNat 97, Char.ofNat 116, Char.ofNat 101, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116]), text := (String.ofList [Char.ofNat 109, Char.ofNat 121, Char.ofNat 32, Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121, Char.ofNat 32, Char.ofNat 118, Char.ofNat 97, Char.ofNat 108, Char.ofNat 117, Char.ofNat 101, Char.ofNat 32, Char.ofNat 61, Char.ofNat 32, Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101, Char.ofNat 32, Char.ofNat 49, Char.ofNat 32, Char.ofNat 118, Char.ofNat 97, Char.ofNat 108, Char.ofNat 117, Char.ofNat 101]) }, scope := ScopeTag.definition, form := SourceForm.lambda ({ id := 0, spelling := (String.ofList [Char.ofNat 118, Char.ofNat 97, Char.ofNat 108, Char.ofNat 117, Char.ofNat 101]), startByte := 98, endByte := 103, sourcePosition := { startByte := 98, endByte := 103, kind := (String.ofList [Char.ofNat 73, Char.ofNat 100, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116, Char.ofNat 105, Char.ofNat 102, Char.ofNat 105, Char.ofNat 101, Char.ofNat 114, Char.ofNat 80, Char.ofNat 97, Char.ofNat 116, Char.ofNat 116, Char.ofNat 101, Char.ofNat 114, Char.ofNat 110]), text := (String.ofList [Char.ofNat 118, Char.ofNat 97, Char.ofNat 108, Char.ofNat 117, Char.ofNat 101]) }, scope := ScopeTag.definition, annotation := none }) 1, childOrdinals := [1], codeLabel := 7, instruction := Instruction.lambda 0 8 },
  { ordinal := 1, occurrence := 12, startByte := 113, endByte := 118, sourcePosition := { startByte := 113, endByte := 118, kind := (String.ofList [Char.ofNat 77, Char.ofNat 108, Char.ofNat 65, Char.ofNat 114, Char.ofNat 103, Char.ofNat 117, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116]), text := (String.ofList [Char.ofNat 118, Char.ofNat 97, Char.ofNat 108, Char.ofNat 117, Char.ofNat 101]) }, scope := ScopeTag.parameter 0, form := SourceForm.apply (String.ofList [Char.ofNat 77, Char.ofNat 108, Char.ofNat 65, Char.ofNat 114, Char.ofNat 103, Char.ofNat 117, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116]) 2 3, childOrdinals := [2, 3], codeLabel := 8, instruction := Instruction.apply 9 10 },
  { ordinal := 2, occurrence := 13, startByte := 111, endByte := 112, sourcePosition := { startByte := 111, endByte := 112, kind := (String.ofList [Char.ofNat 77, Char.ofNat 108, Char.ofNat 65, Char.ofNat 114, Char.ofNat 103, Char.ofNat 117, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116]), text := (String.ofList [Char.ofNat 49]) }, scope := ScopeTag.parameter 0, form := SourceForm.apply (String.ofList [Char.ofNat 77, Char.ofNat 108, Char.ofNat 65, Char.ofNat 114, Char.ofNat 103, Char.ofNat 117, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116]) 4 5, childOrdinals := [4, 5], codeLabel := 9, instruction := Instruction.apply 11 12 },
  { ordinal := 3, occurrence := 16, startByte := 113, endByte := 118, sourcePosition := { startByte := 113, endByte := 118, kind := (String.ofList [Char.ofNat 73, Char.ofNat 100, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116, Char.ofNat 105, Char.ofNat 102, Char.ofNat 105, Char.ofNat 101, Char.ofNat 114, Char.ofNat 69, Char.ofNat 120, Char.ofNat 112, Char.ofNat 114, Char.ofNat 101, Char.ofNat 115, Char.ofNat 115, Char.ofNat 105, Char.ofNat 111, Char.ofNat 110]), text := (String.ofList [Char.ofNat 118, Char.ofNat 97, Char.ofNat 108, Char.ofNat 117, Char.ofNat 101]) }, scope := ScopeTag.parameter 0, form := SourceForm.name (String.ofList [Char.ofNat 118, Char.ofNat 97, Char.ofNat 108, Char.ofNat 117, Char.ofNat 101]) (Resolution.parameter 0), childOrdinals := [], codeLabel := 10, instruction := Instruction.name (Resolution.parameter 0) (String.ofList [Char.ofNat 79, Char.ofNat 98, Char.ofNat 115, Char.ofNat 101, Char.ofNat 114, Char.ofNat 118, Char.ofNat 101]) },
  { ordinal := 4, occurrence := 14, startByte := 106, endByte := 110, sourcePosition := { startByte := 106, endByte := 110, kind := (String.ofList [Char.ofNat 73, Char.ofNat 100, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116, Char.ofNat 105, Char.ofNat 102, Char.ofNat 105, Char.ofNat 101, Char.ofNat 114, Char.ofNat 69, Char.ofNat 120, Char.ofNat 112, Char.ofNat 114, Char.ofNat 101, Char.ofNat 115, Char.ofNat 115, Char.ofNat 105, Char.ofNat 111, Char.ofNat 110]), text := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101]) }, scope := ScopeTag.parameter 0, form := SourceForm.name (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101]) (Resolution.moduleDef (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101]) (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]) (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]) 0), childOrdinals := [], codeLabel := 11, instruction := Instruction.name (Resolution.moduleDef (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101]) (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]) (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]) 0) (String.ofList [Char.ofNat 79, Char.ofNat 98, Char.ofNat 115, Char.ofNat 101, Char.ofNat 114, Char.ofNat 118, Char.ofNat 101]) },
  { ordinal := 5, occurrence := 15, startByte := 111, endByte := 112, sourcePosition := { startByte := 111, endByte := 112, kind := (String.ofList [Char.ofNat 73, Char.ofNat 110, Char.ofNat 116, Char.ofNat 101, Char.ofNat 103, Char.ofNat 101, Char.ofNat 114, Char.ofNat 76, Char.ofNat 105, Char.ofNat 116, Char.ofNat 101, Char.ofNat 114, Char.ofNat 97, Char.ofNat 108]), text := (String.ofList [Char.ofNat 49]) }, scope := ScopeTag.parameter 0, form := SourceForm.integer (String.ofList [Char.ofNat 49]), childOrdinals := [], codeLabel := 12, instruction := Instruction.integer (String.ofList [Char.ofNat 49]) },
]
def runId : Nat := 124250723672840
def events : List RuntimeEvent := [RuntimeEvent.request 32 14 0 ({ bindingName := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 4, startByte := 59, endByte := 63 }) (ExecutionOwner.invocation 2),
RuntimeEvent.pendingCallee 32 15 0 2 10 2 (some 9) ({ bindingName := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 4, startByte := 59, endByte := 63 }) ({ bindingName := (String.ofList [Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 12, startByte := 113, endByte := 118 }) (ExecutionOwner.invocation 2),
RuntimeEvent.calleeReturn 59 22 2 10 2 15 17 (some 9) ({ bindingName := (String.ofList [Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 12, startByte := 113, endByte := 118 }) (ExecutionOwner.invocation 6) Interface.value ({ bindingName := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 7, startByte := 65, endByte := 86 }),
RuntimeEvent.delay 16 10 2 18,
RuntimeEvent.nameLookup 60 24 2 0 5 4 5 (({ bindingName := (String.ofList [Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 16, startByte := 113, endByte := 118 })) (ExecutionOwner.invocation 8) ((String.ofList [Char.ofNat 79, Char.ofNat 98, Char.ofNat 115, Char.ofNat 101, Char.ofNat 114, Char.ofNat 118, Char.ofNat 101])),
RuntimeEvent.nameReceipt 60 25 10 4 5 (({ bindingName := (String.ofList [Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 16, startByte := 113, endByte := 118 })) (ExecutionOwner.invocation 8) ((String.ofList [Char.ofNat 79, Char.ofNat 98, Char.ofNat 115, Char.ofNat 101, Char.ofNat 114, Char.ofNat 118, Char.ofNat 101])),
RuntimeEvent.valueBind 15 7 1 0 5 2 4 5 Interface.value,
RuntimeEvent.valueBind 23 10 2 0 6 3 7 8 Interface.value,
RuntimeEvent.valueBind 61 26 8 1 10 7 4 5 Interface.value]
def returnSnapshot : ReturnSnapshot := { runId := 124250723672840, frame := 2, applySite := { bindingName := (String.ofList [Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 12, startByte := 113, endByte := 118 }, argumentLabel := 10, callerEnvironment := 2, cells := [{ value := some { value := 5, view := 6, interface := Interface.value, dispatch := none } }, { value := some { value := 2, view := 3, interface := Interface.value, dispatch := none } }, { value := some { value := 0, view := 0, interface := Interface.value, dispatch := none } }, { value := none }, { value := some { value := 1, view := 2, interface := Interface.computation, dispatch := none } }, { value := some { value := 4, view := 5, interface := Interface.value, dispatch := none } }, { value := some { value := 7, view := 8, interface := Interface.value, dispatch := none } }, { value := some { value := 7, view := 8, interface := Interface.value, dispatch := none } }, { value := some { value := 11, view := 12, interface := Interface.value, dispatch := none } }, { value := some { value := 12, view := 14, interface := Interface.computation, dispatch := none } }], environments := [{ parent := none, binderKind := none, binderId := none, binderCell := none, binderOwner := none, dispatchBase := none, dispatchWord := none, substitution := none }, { parent := some 0, binderKind := some (String.ofList [Char.ofNat 112, Char.ofNat 97, Char.ofNat 114, Char.ofNat 97, Char.ofNat 109, Char.ofNat 101, Char.ofNat 116, Char.ofNat 101, Char.ofNat 114]), binderId := some 0, binderCell := some 4, binderOwner := some (SourceRootIdentity.definition (String.ofList [Char.ofNat 104, Char.ofNat 97, Char.ofNat 110, Char.ofNat 100, Char.ofNat 108, Char.ofNat 101]) (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]) (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]) 0), dispatchBase := none, dispatchWord := none, substitution := none }, { parent := some 0, binderKind := some (String.ofList [Char.ofNat 112, Char.ofNat 97, Char.ofNat 114, Char.ofNat 97, Char.ofNat 109, Char.ofNat 101, Char.ofNat 116, Char.ofNat 101, Char.ofNat 114]), binderId := some 0, binderCell := some 5, binderOwner := some (SourceRootIdentity.definition (String.ofList [Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121]) (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]) (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]) 0), dispatchBase := none, dispatchWord := none, substitution := none }, { parent := some 0, binderKind := some (String.ofList [Char.ofNat 112, Char.ofNat 97, Char.ofNat 114, Char.ofNat 97, Char.ofNat 109, Char.ofNat 101, Char.ofNat 116, Char.ofNat 101, Char.ofNat 114]), binderId := some 0, binderCell := some 6, binderOwner := some (SourceRootIdentity.definition (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101]) (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]) (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]) 0), dispatchBase := none, dispatchWord := none, substitution := none }, { parent := some 1, binderKind := some (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 116, Char.ofNat 99, Char.ofNat 104]), binderId := some 0, binderCell := some 7, binderOwner := some (SourceRootIdentity.definition (String.ofList [Char.ofNat 104, Char.ofNat 97, Char.ofNat 110, Char.ofNat 100, Char.ofNat 108, Char.ofNat 101]) (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]) (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]) 0), dispatchBase := none, dispatchWord := none, substitution := none }, { parent := some 4, binderKind := some (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 116, Char.ofNat 99, Char.ofNat 104]), binderId := some 1, binderCell := some 8, binderOwner := some (SourceRootIdentity.definition (String.ofList [Char.ofNat 104, Char.ofNat 97, Char.ofNat 110, Char.ofNat 100, Char.ofNat 108, Char.ofNat 101]) (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]) (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]) 0), dispatchBase := none, dispatchWord := none, substitution := none }, { parent := some 0, binderKind := some (String.ofList [Char.ofNat 112, Char.ofNat 97, Char.ofNat 114, Char.ofNat 97, Char.ofNat 109, Char.ofNat 101, Char.ofNat 116, Char.ofNat 101, Char.ofNat 114]), binderId := some 0, binderCell := some 9, binderOwner := some (SourceRootIdentity.definition (String.ofList [Char.ofNat 104, Char.ofNat 97, Char.ofNat 110, Char.ofNat 100, Char.ofNat 108, Char.ofNat 101]) (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]) (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]) 0), dispatchBase := none, dispatchWord := none, substitution := none }], values := [{ source := { bindingName := (String.ofList [Char.ofNat 104, Char.ofNat 97, Char.ofNat 110, Char.ofNat 100, Char.ofNat 108, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 19, startByte := 119, endByte := 197 }, kind := ValueKind.closure }, { source := { bindingName := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 105, Char.ofNat 110]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 30, startByte := 215, endByte := 226 }, kind := ValueKind.computation }, { source := { bindingName := (String.ofList [Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 11, startByte := 89, endByte := 118 }, kind := ValueKind.closure }, { source := { bindingName := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 105, Char.ofNat 110]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 33, startByte := 223, endByte := 224 }, kind := ValueKind.computation }, { source := { bindingName := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 105, Char.ofNat 110]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 35, startByte := 223, endByte := 224 }, kind := ValueKind.integer (String.ofList [Char.ofNat 55]) }, { source := { bindingName := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 2, startByte := 33, endByte := 88 }, kind := ValueKind.closure }, { source := { bindingName := (String.ofList [Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 13, startByte := 111, endByte := 112 }, kind := ValueKind.computation }, { source := { bindingName := (String.ofList [Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 15, startByte := 111, endByte := 112 }, kind := ValueKind.integer (String.ofList [Char.ofNat 49]) }, { source := { bindingName := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 5, startByte := 52, endByte := 58 }, kind := ValueKind.operation ({ name := (String.ofList [Char.ofNat 116, Char.ofNat 105, Char.ofNat 99, Char.ofNat 107]), familyRealm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), familyPath := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), familyDeclaration := { startByte := 0, endByte := 32, kind := (String.ofList [Char.ofNat 65, Char.ofNat 99, Char.ofNat 116, Char.ofNat 68, Char.ofNat 101, Char.ofNat 99, Char.ofNat 108, Char.ofNat 97, Char.ofNat 114, Char.ofNat 97, Char.ofNat 116, Char.ofNat 105, Char.ofNat 111, Char.ofNat 110]), text := (String.ofList [Char.ofNat 97, Char.ofNat 99, Char.ofNat 116, Char.ofNat 32, Char.ofNat 105, Char.ofNat 111, Char.ofNat 58, Char.ofNat 10, Char.ofNat 32, Char.ofNat 32, Char.ofNat 32, Char.ofNat 32, Char.ofNat 111, Char.ofNat 117, Char.ofNat 114, Char.ofNat 32, Char.ofNat 116, Char.ofNat 105, Char.ofNat 99, Char.ofNat 107, Char.ofNat 58, Char.ofNat 32, Char.ofNat 105, Char.ofNat 110, Char.ofNat 116, Char.ofNat 32, Char.ofNat 45, Char.ofNat 62, Char.ofNat 32, Char.ofNat 105, Char.ofNat 110, Char.ofNat 116]) }, declaration := { startByte := 12, endByte := 32, kind := (String.ofList [Char.ofNat 66, Char.ofNat 105, Char.ofNat 110, Char.ofNat 100, Char.ofNat 105, Char.ofNat 110, Char.ofNat 103, Char.ofNat 83, Char.ofNat 116, Char.ofNat 97, Char.ofNat 116, Char.ofNat 101, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116]), text := (String.ofList [Char.ofNat 111, Char.ofNat 117, Char.ofNat 114, Char.ofNat 32, Char.ofNat 116, Char.ofNat 105, Char.ofNat 99, Char.ofNat 107, Char.ofNat 58, Char.ofNat 32, Char.ofNat 105, Char.ofNat 110, Char.ofNat 116, Char.ofNat 32, Char.ofNat 45, Char.ofNat 62, Char.ofNat 32, Char.ofNat 105, Char.ofNat 110, Char.ofNat 116]) }, namePosition := { startByte := 16, endByte := 20, kind := (String.ofList [Char.ofNat 73, Char.ofNat 100, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116, Char.ofNat 105, Char.ofNat 102, Char.ofNat 105, Char.ofNat 101, Char.ofNat 114, Char.ofNat 80, Char.ofNat 97, Char.ofNat 116, Char.ofNat 116, Char.ofNat 101, Char.ofNat 114, Char.ofNat 110]), text := (String.ofList [Char.ofNat 116, Char.ofNat 105, Char.ofNat 99, Char.ofNat 107]) }, signaturePosition := { startByte := 22, endByte := 32, kind := (String.ofList [Char.ofNat 84, Char.ofNat 121, Char.ofNat 112, Char.ofNat 101, Char.ofNat 69, Char.ofNat 120, Char.ofNat 112, Char.ofNat 114, Char.ofNat 101, Char.ofNat 115, Char.ofNat 115, Char.ofNat 105, Char.ofNat 111, Char.ofNat 110]), text := (String.ofList [Char.ofNat 105, Char.ofNat 110, Char.ofNat 116, Char.ofNat 32, Char.ofNat 45, Char.ofNat 62, Char.ofNat 32, Char.ofNat 105, Char.ofNat 110, Char.ofNat 116]) }, startByte := 12, endByte := 32, visibility := (String.ofList [Char.ofNat 79, Char.ofNat 117, Char.ofNat 114]), signature := AnnotationType.mk (SourceType.function (AnnotationType.mk (SourceType.int) (none)) (AnnotationType.mk (SourceType.int) (none))) (none) }) }, { source := { bindingName := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 4, startByte := 59, endByte := 63 }, kind := ValueKind.computation }, { source := { bindingName := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 4, startByte := 59, endByte := 63 }, kind := ValueKind.computation }, { source := { bindingName := (String.ofList [Char.ofNat 104, Char.ofNat 97, Char.ofNat 110, Char.ofNat 100, Char.ofNat 108, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 20, startByte := 148, endByte := 197 }, kind := ValueKind.closure }, { source := { bindingName := (String.ofList [Char.ofNat 104, Char.ofNat 97, Char.ofNat 110, Char.ofNat 100, Char.ofNat 108, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 22, startByte := 187, endByte := 195 }, kind := ValueKind.computation }, { source := { bindingName := (String.ofList [Char.ofNat 104, Char.ofNat 97, Char.ofNat 110, Char.ofNat 100, Char.ofNat 108, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 25, startByte := 191, endByte := 193 }, kind := ValueKind.computation }, { source := { bindingName := (String.ofList [Char.ofNat 104, Char.ofNat 97, Char.ofNat 110, Char.ofNat 100, Char.ofNat 108, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 27, startByte := 191, endByte := 193 }, kind := ValueKind.integer (String.ofList [Char.ofNat 49, Char.ofNat 48]) }, { source := { bindingName := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 7, startByte := 65, endByte := 86 }, kind := ValueKind.closure }], receivingViews := [{ index := 0, value := 0, image := none, unknown := true, kind := ReceivingViewKind.ordinary }, { index := 1, value := 1, image := none, unknown := true, kind := ReceivingViewKind.ordinary }, { index := 2, value := 1, image := some 0, unknown := true, kind := ReceivingViewKind.rootComp }, { index := 3, value := 2, image := none, unknown := true, kind := ReceivingViewKind.ordinary }, { index := 4, value := 3, image := none, unknown := true, kind := ReceivingViewKind.ordinary }, { index := 5, value := 4, image := none, unknown := false, kind := ReceivingViewKind.ordinary }, { index := 6, value := 5, image := none, unknown := true, kind := ReceivingViewKind.ordinary }, { index := 7, value := 6, image := none, unknown := true, kind := ReceivingViewKind.ordinary }, { index := 8, value := 7, image := none, unknown := false, kind := ReceivingViewKind.ordinary }, { index := 9, value := 8, image := none, unknown := true, kind := ReceivingViewKind.ordinary }, { index := 10, value := 9, image := none, unknown := true, kind := ReceivingViewKind.ordinary }, { index := 11, value := 10, image := none, unknown := true, kind := ReceivingViewKind.ordinary }, { index := 12, value := 11, image := none, unknown := true, kind := ReceivingViewKind.ordinary }, { index := 13, value := 12, image := none, unknown := true, kind := ReceivingViewKind.ordinary }, { index := 14, value := 12, image := some 1, unknown := true, kind := ReceivingViewKind.rootComp }, { index := 15, value := 13, image := none, unknown := true, kind := ReceivingViewKind.ordinary }, { index := 16, value := 14, image := none, unknown := false, kind := ReceivingViewKind.ordinary }, { index := 17, value := 15, image := none, unknown := true, kind := ReceivingViewKind.ordinary }], receivingImageChains := [{ view := 0, links := [] }, { view := 1, links := [] }, { view := 2, links := [{ image := 0, boundary := 0, receiver := 0 }] }, { view := 3, links := [] }, { view := 4, links := [] }, { view := 5, links := [] }, { view := 6, links := [] }, { view := 7, links := [] }, { view := 8, links := [] }, { view := 9, links := [] }, { view := 10, links := [] }, { view := 11, links := [] }, { view := 12, links := [] }, { view := 13, links := [] }, { view := 14, links := [{ image := 1, boundary := 1, receiver := 4 }] }, { view := 15, links := [] }, { view := 16, links := [] }, { view := 17, links := [] }], sourceNameInitialization := some { value := 4, view := 5, interface := Interface.value, dispatch := none }, sourceNameParameter := some 0, receivingScanTruncated := false }
end R314Artifact


namespace R315MakeArtifact

structure Position where
  startByte : Nat
  endByte : Nat
  kind : String
  text : String
  deriving Repr
inductive ScopeTag where
  | definition | moduleExpression | sourceMember
  | expression (id : Nat) | parameter (id : Nat) | localInitializer (id : Nat)
  | catchArm (id : Nat) (arm : Position)
  deriving Repr
structure RootBinding where
  name : String
  realm : String
  path : String
  sameNameOrdinal : Nat
  deriving Repr
inductive ExecutionOwner where | moduleRun | invocation (id : Nat) deriving Repr
inductive SourceRootIdentity where
  | definition (bindingName realm path : String) (sameNameOrdinal : Nat)
  | expression (occurrence : Nat)
  | member (realm path kind : String) (declaration member : Position)
  deriving Repr
structure RuntimeSite where
  bindingName : String
  realm : String
  path : String
  sameNameOrdinal : Nat
  occurrence : Nat
  startByte : Nat
  endByte : Nat
  deriving Repr
inductive Interface where | value | computation deriving Repr
structure Received where
  value : Nat
  view : Nat
  interface : Interface
  dispatch : Option Nat
  deriving Repr
structure RuntimeCell where
  value : Option Received
  deriving Repr
structure RuntimeEnvironment where
  parent : Option Nat
  binderKind : Option String
  binderId : Option Nat
  binderCell : Option Nat
  binderOwner : Option SourceRootIdentity
  dispatchBase : Option Nat
  dispatchWord : Option Nat
  substitution : Option Nat
  deriving Repr
inductive ReceivingViewKind where
  | ordinary | rootComp | callbackEntry (id : Nat) | callbackResult (id : Nat)
  deriving Repr
structure ReceivingView where
  index : Nat
  value : Nat
  image : Option Nat
  unknown : Bool
  kind : ReceivingViewKind
  deriving Repr
structure ImageLink where
  image : Nat
  boundary : Nat
  receiver : Nat
  deriving Repr
structure ViewImageChain where
  view : Nat
  links : List ImageLink
  deriving Repr
inductive RuntimeEvent where
  | request (step order id : Nat) (site : RuntimeSite) (owner : ExecutionOwner)
  | pendingCallee (step order request frame argumentLabel environment : Nat)
      (calleeLabel : Option Nat) (requestSite applySite : RuntimeSite) (owner : ExecutionOwner)
  | calleeReturn (step order frame argumentLabel environment value view : Nat)
      (calleeLabel : Option Nat) (site : RuntimeSite) (owner : ExecutionOwner)
      (interface : Interface) (provider : RuntimeSite)
  | delay (value code environment view : Nat)
  | nameLookup (step order environment parameter cell value view : Nat)
      (site : RuntimeSite) (owner : ExecutionOwner) (consumption : String)
  | nameReceipt (step order receipt value view : Nat)
      (site : RuntimeSite) (owner : ExecutionOwner) (consumption : String)
  | valueBind (step order receiver parameter cell environment value view : Nat) (interface : Interface)
  deriving Repr
inductive Resolution where
  | moduleDef (name : String) (realm : String) (path : String) (ordinal : Nat)
  | parameter (id : Nat) | local (id : Nat) | catchBinder (id : Nat) | caseBinder (id : Nat)
  | unresolved | ambiguous
  deriving Repr
structure EffectId where
  realm : String
  path : String
  declaration : Position
  deriving Repr
structure EffectRow where
  position : Position
  concrete : List EffectId
  variables : List String
  deriving Repr
mutual
inductive SourceType where
  | unit | int | bool | str | variable (name : String) | hole (position : Position)
  | tuple (items : List AnnotationType) | function (argument result : AnnotationType)
  deriving Repr
inductive AnnotationType where
  | mk (value : SourceType) (effects : Option EffectRow)
  deriving Repr
end
structure Annotation where
  owner : String
  position : Position
  type : AnnotationType
  deriving Repr
structure OperationIdentity where
  name : String
  familyRealm : String
  familyPath : String
  familyDeclaration : Position
  declaration : Position
  namePosition : Position
  signaturePosition : Position
  startByte : Nat
  endByte : Nat
  visibility : String
  signature : AnnotationType
  deriving Repr
inductive ValueKind where
  | unit | integer (value : String) | boolean (value : Bool) | string (value : String)
  | primitive (name : String) | tuple (items : List Received)
  | variant (tag : String) (items : List Received)
  | record (fields : List (String × Received)) | closure | computation
  | operation (identity : OperationIdentity)
  deriving Repr
structure RuntimeValue where
  source : RuntimeSite
  kind : ValueKind
  deriving Repr
structure ReturnSnapshot where
  runId : Nat
  frame : Nat
  applySite : RuntimeSite
  argumentLabel : Nat
  callerEnvironment : Nat
  cells : List RuntimeCell
  environments : List RuntimeEnvironment
  values : List RuntimeValue
  receivingViews : List ReceivingView
  receivingImageChains : List ViewImageChain
  sourceNameInitialization : Option Received
  sourceNameParameter : Option Nat
  receivingScanTruncated : Bool
  deriving Repr
structure Formal where
  id : Nat
  spelling : String
  startByte : Nat
  endByte : Nat
  sourcePosition : Position
  scope : ScopeTag
  annotation : Option Annotation
  deriving Repr
inductive BlockStatement where
  | expression (code : Nat) | binding (ordinal localId initializer : Nat)
  deriving Repr
inductive SourceStatement where
  | expression (source : Nat) | binding (ordinal localId initializer : Nat)
  deriving Repr
structure SourceStatementBlock where
  statements : List SourceStatement
  finalExpression : Nat
  deriving Repr
structure InstructionStatementBlock where
  statements : List BlockStatement
  finalExpression : Nat
  deriving Repr
inductive SourceForm where
  | unit | integer (value : String) | boolean (value : Bool) | string (value : String)
  | decodedString (value : String) | name (spelling : String) (resolution : Resolution)
  | apply (syntaxKind : String) (callee argument : Nat) | group (inner : Nat)
  | ascription (annotation : Annotation) (inner : Nat) | lambda (formal : Formal) (body : Nat)
  | operation (identity : OperationIdentity) | block (bindings : List (Nat × Nat)) (finalExpression : Nat)
  | statementBlock (block : SourceStatementBlock)
  deriving Repr
inductive Instruction where
  | unit | integer (value : String) | boolean (value : Bool) | string (value : String)
  | decodedString (value : String) | name (resolution : Resolution) (consumption : String)
  | apply (callee argument : Nat) | forward (inner : Nat) | lambda (formalId body : Nat)
  | operation (identity : OperationIdentity) | block (bindings : List (Nat × Nat)) (finalExpression : Nat)
  | statementBlock (block : InstructionStatementBlock)
  deriving Repr
structure SourceNode where
  ordinal : Nat
  occurrence : Nat
  startByte : Nat
  endByte : Nat
  sourcePosition : Position
  scope : ScopeTag
  form : SourceForm
  childOrdinals : List Nat
  codeLabel : Nat
  instruction : Instruction
  deriving Repr
def sourceText : String := (String.ofList [Char.ofNat 97, Char.ofNat 99, Char.ofNat 116, Char.ofNat 32, Char.ofNat 105, Char.ofNat 111, Char.ofNat 58, Char.ofNat 10, Char.ofNat 32, Char.ofNat 32, Char.ofNat 32, Char.ofNat 32, Char.ofNat 111, Char.ofNat 117, Char.ofNat 114, Char.ofNat 32, Char.ofNat 116, Char.ofNat 105, Char.ofNat 99, Char.ofNat 107, Char.ofNat 58, Char.ofNat 32, Char.ofNat 105, Char.ofNat 110, Char.ofNat 116, Char.ofNat 32, Char.ofNat 45, Char.ofNat 62, Char.ofNat 32, Char.ofNat 105, Char.ofNat 110, Char.ofNat 116, Char.ofNat 10, Char.ofNat 109, Char.ofNat 121, Char.ofNat 32, Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101, Char.ofNat 32, Char.ofNat 115, Char.ofNat 101, Char.ofNat 101, Char.ofNat 100, Char.ofNat 32, Char.ofNat 61, Char.ofNat 32, Char.ofNat 123, Char.ofNat 32, Char.ofNat 105, Char.ofNat 111, Char.ofNat 58, Char.ofNat 58, Char.ofNat 116, Char.ofNat 105, Char.ofNat 99, Char.ofNat 107, Char.ofNat 32, Char.ofNat 115, Char.ofNat 101, Char.ofNat 101, Char.ofNat 100, Char.ofNat 59, Char.ofNat 32, Char.ofNat 92, Char.ofNat 97, Char.ofNat 114, Char.ofNat 103, Char.ofNat 117, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116, Char.ofNat 32, Char.ofNat 45, Char.ofNat 62, Char.ofNat 32, Char.ofNat 97, Char.ofNat 114, Char.ofNat 103, Char.ofNat 117, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116, Char.ofNat 32, Char.ofNat 125, Char.ofNat 10, Char.ofNat 109, Char.ofNat 121, Char.ofNat 32, Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121, Char.ofNat 32, Char.ofNat 118, Char.ofNat 97, Char.ofNat 108, Char.ofNat 117, Char.ofNat 101, Char.ofNat 32, Char.ofNat 61, Char.ofNat 32, Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101, Char.ofNat 32, Char.ofNat 49, Char.ofNat 32, Char.ofNat 118, Char.ofNat 97, Char.ofNat 108, Char.ofNat 117, Char.ofNat 101, Char.ofNat 10, Char.ofNat 109, Char.ofNat 121, Char.ofNat 32, Char.ofNat 104, Char.ofNat 97, Char.ofNat 110, Char.ofNat 100, Char.ofNat 108, Char.ofNat 101, Char.ofNat 32, Char.ofNat 40, Char.ofNat 116, Char.ofNat 104, Char.ofNat 117, Char.ofNat 110, Char.ofNat 107, Char.ofNat 58, Char.ofNat 91, Char.ofNat 105, Char.ofNat 111, Char.ofNat 93, Char.ofNat 32, Char.ofNat 105, Char.ofNat 110, Char.ofNat 116, Char.ofNat 41, Char.ofNat 32, Char.ofNat 61, Char.ofNat 32, Char.ofNat 99, Char.ofNat 97, Char.ofNat 116, Char.ofNat 99, Char.ofNat 104, Char.ofNat 32, Char.ofNat 116, Char.ofNat 104, Char.ofNat 117, Char.ofNat 110, Char.ofNat 107, Char.ofNat 32, Char.ofNat 123, Char.ofNat 32, Char.ofNat 105, Char.ofNat 111, Char.ofNat 58, Char.ofNat 58, Char.ofNat 116, Char.ofNat 105, Char.ofNat 99, Char.ofNat 107, Char.ofNat 40, Char.ofNat 112, Char.ofNat 41, Char.ofNat 44, Char.ofNat 32, Char.ofNat 107, Char.ofNat 32, Char.ofNat 45, Char.ofNat 62, Char.ofNat 32, Char.ofNat 104, Char.ofNat 97, Char.ofNat 110, Char.ofNat 100, Char.ofNat 108, Char.ofNat 101, Char.ofNat 32, Char.ofNat 123, Char.ofNat 32, Char.ofNat 107, Char.ofNat 32, Char.ofNat 49, Char.ofNat 48, Char.ofNat 32, Char.ofNat 125, Char.ofNat 32, Char.ofNat 125, Char.ofNat 10, Char.ofNat 109, Char.ofNat 121, Char.ofNat 32, Char.ofNat 109, Char.ofNat 97, Char.ofNat 105, Char.ofNat 110, Char.ofNat 32, Char.ofNat 61, Char.ofNat 32, Char.ofNat 104, Char.ofNat 97, Char.ofNat 110, Char.ofNat 100, Char.ofNat 108, Char.ofNat 101, Char.ofNat 32, Char.ofNat 123, Char.ofNat 32, Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121, Char.ofNat 32, Char.ofNat 55, Char.ofNat 32, Char.ofNat 125])
def rootBinding : RootBinding := { name := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0 }
def rootInitializer : Nat := 0
def rootFormals : List Formal := [
  { id := 0, spelling := (String.ofList [Char.ofNat 115, Char.ofNat 101, Char.ofNat 101, Char.ofNat 100]), startByte := 41, endByte := 45, sourcePosition := { startByte := 41, endByte := 45, kind := (String.ofList [Char.ofNat 73, Char.ofNat 100, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116, Char.ofNat 105, Char.ofNat 102, Char.ofNat 105, Char.ofNat 101, Char.ofNat 114, Char.ofNat 80, Char.ofNat 97, Char.ofNat 116, Char.ofNat 116, Char.ofNat 101, Char.ofNat 114, Char.ofNat 110]), text := (String.ofList [Char.ofNat 115, Char.ofNat 101, Char.ofNat 101, Char.ofNat 100]) }, scope := ScopeTag.definition, annotation := none },
]
def nodes : List SourceNode := [
  { ordinal := 0, occurrence := 2, startByte := 33, endByte := 88, sourcePosition := { startByte := 33, endByte := 88, kind := (String.ofList [Char.ofNat 66, Char.ofNat 105, Char.ofNat 110, Char.ofNat 100, Char.ofNat 105, Char.ofNat 110, Char.ofNat 103, Char.ofNat 83, Char.ofNat 116, Char.ofNat 97, Char.ofNat 116, Char.ofNat 101, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116]), text := (String.ofList [Char.ofNat 109, Char.ofNat 121, Char.ofNat 32, Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101, Char.ofNat 32, Char.ofNat 115, Char.ofNat 101, Char.ofNat 101, Char.ofNat 100, Char.ofNat 32, Char.ofNat 61, Char.ofNat 32, Char.ofNat 123, Char.ofNat 32, Char.ofNat 105, Char.ofNat 111, Char.ofNat 58, Char.ofNat 58, Char.ofNat 116, Char.ofNat 105, Char.ofNat 99, Char.ofNat 107, Char.ofNat 32, Char.ofNat 115, Char.ofNat 101, Char.ofNat 101, Char.ofNat 100, Char.ofNat 59, Char.ofNat 32, Char.ofNat 92, Char.ofNat 97, Char.ofNat 114, Char.ofNat 103, Char.ofNat 117, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116, Char.ofNat 32, Char.ofNat 45, Char.ofNat 62, Char.ofNat 32, Char.ofNat 97, Char.ofNat 114, Char.ofNat 103, Char.ofNat 117, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116, Char.ofNat 32, Char.ofNat 125]) }, scope := ScopeTag.definition, form := SourceForm.lambda ({ id := 0, spelling := (String.ofList [Char.ofNat 115, Char.ofNat 101, Char.ofNat 101, Char.ofNat 100]), startByte := 41, endByte := 45, sourcePosition := { startByte := 41, endByte := 45, kind := (String.ofList [Char.ofNat 73, Char.ofNat 100, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116, Char.ofNat 105, Char.ofNat 102, Char.ofNat 105, Char.ofNat 101, Char.ofNat 114, Char.ofNat 80, Char.ofNat 97, Char.ofNat 116, Char.ofNat 116, Char.ofNat 101, Char.ofNat 114, Char.ofNat 110]), text := (String.ofList [Char.ofNat 115, Char.ofNat 101, Char.ofNat 101, Char.ofNat 100]) }, scope := ScopeTag.definition, annotation := none }) 1, childOrdinals := [1], codeLabel := 0, instruction := Instruction.lambda 0 1 },
  { ordinal := 1, occurrence := 3, startByte := 48, endByte := 88, sourcePosition := { startByte := 48, endByte := 88, kind := (String.ofList [Char.ofNat 66, Char.ofNat 114, Char.ofNat 97, Char.ofNat 99, Char.ofNat 101, Char.ofNat 100, Char.ofNat 83, Char.ofNat 116, Char.ofNat 97, Char.ofNat 116, Char.ofNat 101, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116, Char.ofNat 66, Char.ofNat 108, Char.ofNat 111, Char.ofNat 99, Char.ofNat 107, Char.ofNat 69, Char.ofNat 120, Char.ofNat 112, Char.ofNat 114, Char.ofNat 101, Char.ofNat 115, Char.ofNat 115, Char.ofNat 105, Char.ofNat 111, Char.ofNat 110]), text := (String.ofList [Char.ofNat 123, Char.ofNat 32, Char.ofNat 105, Char.ofNat 111, Char.ofNat 58, Char.ofNat 58, Char.ofNat 116, Char.ofNat 105, Char.ofNat 99, Char.ofNat 107, Char.ofNat 32, Char.ofNat 115, Char.ofNat 101, Char.ofNat 101, Char.ofNat 100, Char.ofNat 59, Char.ofNat 32, Char.ofNat 92, Char.ofNat 97, Char.ofNat 114, Char.ofNat 103, Char.ofNat 117, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116, Char.ofNat 32, Char.ofNat 45, Char.ofNat 62, Char.ofNat 32, Char.ofNat 97, Char.ofNat 114, Char.ofNat 103, Char.ofNat 117, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116, Char.ofNat 32, Char.ofNat 125]) }, scope := ScopeTag.parameter 0, form := SourceForm.statementBlock { statements := [SourceStatement.expression 3], finalExpression := 2 }, childOrdinals := [3, 2], codeLabel := 1, instruction := Instruction.statementBlock { statements := [BlockStatement.expression 3], finalExpression := 2 } },
  { ordinal := 2, occurrence := 7, startByte := 65, endByte := 86, sourcePosition := { startByte := 65, endByte := 86, kind := (String.ofList [Char.ofNat 76, Char.ofNat 97, Char.ofNat 109, Char.ofNat 98, Char.ofNat 100, Char.ofNat 97, Char.ofNat 69, Char.ofNat 120, Char.ofNat 112, Char.ofNat 114, Char.ofNat 101, Char.ofNat 115, Char.ofNat 115, Char.ofNat 105, Char.ofNat 111, Char.ofNat 110]), text := (String.ofList [Char.ofNat 92, Char.ofNat 97, Char.ofNat 114, Char.ofNat 103, Char.ofNat 117, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116, Char.ofNat 32, Char.ofNat 45, Char.ofNat 62, Char.ofNat 32, Char.ofNat 97, Char.ofNat 114, Char.ofNat 103, Char.ofNat 117, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116]) }, scope := ScopeTag.expression 1, form := SourceForm.lambda ({ id := 1, spelling := (String.ofList [Char.ofNat 97, Char.ofNat 114, Char.ofNat 103, Char.ofNat 117, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116]), startByte := 66, endByte := 74, sourcePosition := { startByte := 65, endByte := 86, kind := (String.ofList [Char.ofNat 76, Char.ofNat 97, Char.ofNat 109, Char.ofNat 98, Char.ofNat 100, Char.ofNat 97, Char.ofNat 69, Char.ofNat 120, Char.ofNat 112, Char.ofNat 114, Char.ofNat 101, Char.ofNat 115, Char.ofNat 115, Char.ofNat 105, Char.ofNat 111, Char.ofNat 110]), text := (String.ofList [Char.ofNat 92, Char.ofNat 97, Char.ofNat 114, Char.ofNat 103, Char.ofNat 117, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116, Char.ofNat 32, Char.ofNat 45, Char.ofNat 62, Char.ofNat 32, Char.ofNat 97, Char.ofNat 114, Char.ofNat 103, Char.ofNat 117, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116]) }, scope := ScopeTag.expression 1, annotation := none }) 6, childOrdinals := [6], codeLabel := 2, instruction := Instruction.lambda 1 6 },
  { ordinal := 3, occurrence := 4, startByte := 59, endByte := 63, sourcePosition := { startByte := 59, endByte := 63, kind := (String.ofList [Char.ofNat 77, Char.ofNat 108, Char.ofNat 65, Char.ofNat 114, Char.ofNat 103, Char.ofNat 117, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116]), text := (String.ofList [Char.ofNat 115, Char.ofNat 101, Char.ofNat 101, Char.ofNat 100]) }, scope := ScopeTag.expression 1, form := SourceForm.apply (String.ofList [Char.ofNat 77, Char.ofNat 108, Char.ofNat 65, Char.ofNat 114, Char.ofNat 103, Char.ofNat 117, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116]) 4 5, childOrdinals := [4, 5], codeLabel := 3, instruction := Instruction.apply 4 5 },
  { ordinal := 4, occurrence := 5, startByte := 52, endByte := 58, sourcePosition := { startByte := 52, endByte := 58, kind := (String.ofList [Char.ofNat 80, Char.ofNat 97, Char.ofNat 116, Char.ofNat 104, Char.ofNat 84, Char.ofNat 97, Char.ofNat 105, Char.ofNat 108]), text := (String.ofList [Char.ofNat 58, Char.ofNat 58, Char.ofNat 116, Char.ofNat 105, Char.ofNat 99, Char.ofNat 107]) }, scope := ScopeTag.expression 1, form := SourceForm.operation ({ name := (String.ofList [Char.ofNat 116, Char.ofNat 105, Char.ofNat 99, Char.ofNat 107]), familyRealm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), familyPath := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), familyDeclaration := { startByte := 0, endByte := 32, kind := (String.ofList [Char.ofNat 65, Char.ofNat 99, Char.ofNat 116, Char.ofNat 68, Char.ofNat 101, Char.ofNat 99, Char.ofNat 108, Char.ofNat 97, Char.ofNat 114, Char.ofNat 97, Char.ofNat 116, Char.ofNat 105, Char.ofNat 111, Char.ofNat 110]), text := (String.ofList [Char.ofNat 97, Char.ofNat 99, Char.ofNat 116, Char.ofNat 32, Char.ofNat 105, Char.ofNat 111, Char.ofNat 58, Char.ofNat 10, Char.ofNat 32, Char.ofNat 32, Char.ofNat 32, Char.ofNat 32, Char.ofNat 111, Char.ofNat 117, Char.ofNat 114, Char.ofNat 32, Char.ofNat 116, Char.ofNat 105, Char.ofNat 99, Char.ofNat 107, Char.ofNat 58, Char.ofNat 32, Char.ofNat 105, Char.ofNat 110, Char.ofNat 116, Char.ofNat 32, Char.ofNat 45, Char.ofNat 62, Char.ofNat 32, Char.ofNat 105, Char.ofNat 110, Char.ofNat 116]) }, declaration := { startByte := 12, endByte := 32, kind := (String.ofList [Char.ofNat 66, Char.ofNat 105, Char.ofNat 110, Char.ofNat 100, Char.ofNat 105, Char.ofNat 110, Char.ofNat 103, Char.ofNat 83, Char.ofNat 116, Char.ofNat 97, Char.ofNat 116, Char.ofNat 101, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116]), text := (String.ofList [Char.ofNat 111, Char.ofNat 117, Char.ofNat 114, Char.ofNat 32, Char.ofNat 116, Char.ofNat 105, Char.ofNat 99, Char.ofNat 107, Char.ofNat 58, Char.ofNat 32, Char.ofNat 105, Char.ofNat 110, Char.ofNat 116, Char.ofNat 32, Char.ofNat 45, Char.ofNat 62, Char.ofNat 32, Char.ofNat 105, Char.ofNat 110, Char.ofNat 116]) }, namePosition := { startByte := 16, endByte := 20, kind := (String.ofList [Char.ofNat 73, Char.ofNat 100, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116, Char.ofNat 105, Char.ofNat 102, Char.ofNat 105, Char.ofNat 101, Char.ofNat 114, Char.ofNat 80, Char.ofNat 97, Char.ofNat 116, Char.ofNat 116, Char.ofNat 101, Char.ofNat 114, Char.ofNat 110]), text := (String.ofList [Char.ofNat 116, Char.ofNat 105, Char.ofNat 99, Char.ofNat 107]) }, signaturePosition := { startByte := 22, endByte := 32, kind := (String.ofList [Char.ofNat 84, Char.ofNat 121, Char.ofNat 112, Char.ofNat 101, Char.ofNat 69, Char.ofNat 120, Char.ofNat 112, Char.ofNat 114, Char.ofNat 101, Char.ofNat 115, Char.ofNat 115, Char.ofNat 105, Char.ofNat 111, Char.ofNat 110]), text := (String.ofList [Char.ofNat 105, Char.ofNat 110, Char.ofNat 116, Char.ofNat 32, Char.ofNat 45, Char.ofNat 62, Char.ofNat 32, Char.ofNat 105, Char.ofNat 110, Char.ofNat 116]) }, startByte := 12, endByte := 32, visibility := (String.ofList [Char.ofNat 79, Char.ofNat 117, Char.ofNat 114]), signature := AnnotationType.mk (SourceType.function (AnnotationType.mk (SourceType.int) (none)) (AnnotationType.mk (SourceType.int) (none))) (none) }), childOrdinals := [], codeLabel := 4, instruction := Instruction.operation ({ name := (String.ofList [Char.ofNat 116, Char.ofNat 105, Char.ofNat 99, Char.ofNat 107]), familyRealm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), familyPath := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), familyDeclaration := { startByte := 0, endByte := 32, kind := (String.ofList [Char.ofNat 65, Char.ofNat 99, Char.ofNat 116, Char.ofNat 68, Char.ofNat 101, Char.ofNat 99, Char.ofNat 108, Char.ofNat 97, Char.ofNat 114, Char.ofNat 97, Char.ofNat 116, Char.ofNat 105, Char.ofNat 111, Char.ofNat 110]), text := (String.ofList [Char.ofNat 97, Char.ofNat 99, Char.ofNat 116, Char.ofNat 32, Char.ofNat 105, Char.ofNat 111, Char.ofNat 58, Char.ofNat 10, Char.ofNat 32, Char.ofNat 32, Char.ofNat 32, Char.ofNat 32, Char.ofNat 111, Char.ofNat 117, Char.ofNat 114, Char.ofNat 32, Char.ofNat 116, Char.ofNat 105, Char.ofNat 99, Char.ofNat 107, Char.ofNat 58, Char.ofNat 32, Char.ofNat 105, Char.ofNat 110, Char.ofNat 116, Char.ofNat 32, Char.ofNat 45, Char.ofNat 62, Char.ofNat 32, Char.ofNat 105, Char.ofNat 110, Char.ofNat 116]) }, declaration := { startByte := 12, endByte := 32, kind := (String.ofList [Char.ofNat 66, Char.ofNat 105, Char.ofNat 110, Char.ofNat 100, Char.ofNat 105, Char.ofNat 110, Char.ofNat 103, Char.ofNat 83, Char.ofNat 116, Char.ofNat 97, Char.ofNat 116, Char.ofNat 101, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116]), text := (String.ofList [Char.ofNat 111, Char.ofNat 117, Char.ofNat 114, Char.ofNat 32, Char.ofNat 116, Char.ofNat 105, Char.ofNat 99, Char.ofNat 107, Char.ofNat 58, Char.ofNat 32, Char.ofNat 105, Char.ofNat 110, Char.ofNat 116, Char.ofNat 32, Char.ofNat 45, Char.ofNat 62, Char.ofNat 32, Char.ofNat 105, Char.ofNat 110, Char.ofNat 116]) }, namePosition := { startByte := 16, endByte := 20, kind := (String.ofList [Char.ofNat 73, Char.ofNat 100, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116, Char.ofNat 105, Char.ofNat 102, Char.ofNat 105, Char.ofNat 101, Char.ofNat 114, Char.ofNat 80, Char.ofNat 97, Char.ofNat 116, Char.ofNat 116, Char.ofNat 101, Char.ofNat 114, Char.ofNat 110]), text := (String.ofList [Char.ofNat 116, Char.ofNat 105, Char.ofNat 99, Char.ofNat 107]) }, signaturePosition := { startByte := 22, endByte := 32, kind := (String.ofList [Char.ofNat 84, Char.ofNat 121, Char.ofNat 112, Char.ofNat 101, Char.ofNat 69, Char.ofNat 120, Char.ofNat 112, Char.ofNat 114, Char.ofNat 101, Char.ofNat 115, Char.ofNat 115, Char.ofNat 105, Char.ofNat 111, Char.ofNat 110]), text := (String.ofList [Char.ofNat 105, Char.ofNat 110, Char.ofNat 116, Char.ofNat 32, Char.ofNat 45, Char.ofNat 62, Char.ofNat 32, Char.ofNat 105, Char.ofNat 110, Char.ofNat 116]) }, startByte := 12, endByte := 32, visibility := (String.ofList [Char.ofNat 79, Char.ofNat 117, Char.ofNat 114]), signature := AnnotationType.mk (SourceType.function (AnnotationType.mk (SourceType.int) (none)) (AnnotationType.mk (SourceType.int) (none))) (none) }) },
  { ordinal := 5, occurrence := 6, startByte := 59, endByte := 63, sourcePosition := { startByte := 59, endByte := 63, kind := (String.ofList [Char.ofNat 73, Char.ofNat 100, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116, Char.ofNat 105, Char.ofNat 102, Char.ofNat 105, Char.ofNat 101, Char.ofNat 114, Char.ofNat 69, Char.ofNat 120, Char.ofNat 112, Char.ofNat 114, Char.ofNat 101, Char.ofNat 115, Char.ofNat 115, Char.ofNat 105, Char.ofNat 111, Char.ofNat 110]), text := (String.ofList [Char.ofNat 115, Char.ofNat 101, Char.ofNat 101, Char.ofNat 100]) }, scope := ScopeTag.expression 1, form := SourceForm.name (String.ofList [Char.ofNat 115, Char.ofNat 101, Char.ofNat 101, Char.ofNat 100]) (Resolution.parameter 0), childOrdinals := [], codeLabel := 5, instruction := Instruction.name (Resolution.parameter 0) (String.ofList [Char.ofNat 79, Char.ofNat 98, Char.ofNat 115, Char.ofNat 101, Char.ofNat 114, Char.ofNat 118, Char.ofNat 101]) },
  { ordinal := 6, occurrence := 8, startByte := 77, endByte := 86, sourcePosition := { startByte := 77, endByte := 86, kind := (String.ofList [Char.ofNat 73, Char.ofNat 100, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116, Char.ofNat 105, Char.ofNat 102, Char.ofNat 105, Char.ofNat 101, Char.ofNat 114, Char.ofNat 69, Char.ofNat 120, Char.ofNat 112, Char.ofNat 114, Char.ofNat 101, Char.ofNat 115, Char.ofNat 115, Char.ofNat 105, Char.ofNat 111, Char.ofNat 110]), text := (String.ofList [Char.ofNat 32, Char.ofNat 97, Char.ofNat 114, Char.ofNat 103, Char.ofNat 117, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116]) }, scope := ScopeTag.parameter 1, form := SourceForm.name (String.ofList [Char.ofNat 97, Char.ofNat 114, Char.ofNat 103, Char.ofNat 117, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116]) (Resolution.parameter 1), childOrdinals := [], codeLabel := 6, instruction := Instruction.name (Resolution.parameter 1) (String.ofList [Char.ofNat 79, Char.ofNat 98, Char.ofNat 115, Char.ofNat 101, Char.ofNat 114, Char.ofNat 118, Char.ofNat 101]) },
]

end R315MakeArtifact

namespace R315Artifact
structure BindingUsePublication where
  makeRoot : R315MakeArtifact.RootBinding
  makeDefinitionRoot : R314Artifact.SourceRootIdentity
  declaration : R314Artifact.Position
  bindingAnnotation : Option R314Artifact.Annotation
  hirVisibility : String
  sourceIndexPublic : Bool
  initializer : Nat
  useSite : R314Artifact.RuntimeSite
  useOwner : R314Artifact.ExecutionOwner
  useStep : Nat
  useEnvironment : Nat
  useScope : R314Artifact.ScopeTag
  resolution : R314Artifact.Resolution
  consumes : String
  globalCell : Nat
  cellValue : Nat
  cellView : Nat
  cellInterface : R314Artifact.Interface
  providerSite : R314Artifact.RuntimeSite
  providerFormal : Nat
  providerBody : Nat
  providerEnvironment : Nat
  providerEnvironmentParent : Option Nat
  providerInterfaceIsValue : Bool
  useEnvironmentParent : Option Nat
  useEnvironmentBinderKind : Option String
  useEnvironmentBinderId : Option Nat
  useEnvironmentBinderCell : Option Nat
  useEnvironmentBinderOwner : Option R314Artifact.SourceRootIdentity
  dispatchBase : Option Nat
  dispatchWord : Option Nat
  substitution : Option Nat
  runId : Nat
  deriving Repr
structure ModuleBindingRow where
  name : String
  realm : String
  path : String
  sameNameOrdinal : Nat
  definitionRoot : R314Artifact.SourceRootIdentity
  declaration : R314Artifact.Position
  bindingAnnotation : Option R314Artifact.Annotation
  hirVisibility : String
  sourceIndexPublic : Bool
  runtimeCell : Nat
  deriving Repr
def moduleBindingsInSourceOrder : List ModuleBindingRow := [{ name := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, definitionRoot := R314Artifact.SourceRootIdentity.definition (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101]) (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]) (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]) 0, declaration := { startByte := 33, endByte := 88, kind := (String.ofList [Char.ofNat 66, Char.ofNat 105, Char.ofNat 110, Char.ofNat 100, Char.ofNat 105, Char.ofNat 110, Char.ofNat 103, Char.ofNat 83, Char.ofNat 116, Char.ofNat 97, Char.ofNat 116, Char.ofNat 101, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116]), text := (String.ofList [Char.ofNat 109, Char.ofNat 121, Char.ofNat 32, Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101, Char.ofNat 32, Char.ofNat 115, Char.ofNat 101, Char.ofNat 101, Char.ofNat 100, Char.ofNat 32, Char.ofNat 61, Char.ofNat 32, Char.ofNat 123, Char.ofNat 32, Char.ofNat 105, Char.ofNat 111, Char.ofNat 58, Char.ofNat 58, Char.ofNat 116, Char.ofNat 105, Char.ofNat 99, Char.ofNat 107, Char.ofNat 32, Char.ofNat 115, Char.ofNat 101, Char.ofNat 101, Char.ofNat 100, Char.ofNat 59, Char.ofNat 32, Char.ofNat 92, Char.ofNat 97, Char.ofNat 114, Char.ofNat 103, Char.ofNat 117, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116, Char.ofNat 32, Char.ofNat 45, Char.ofNat 62, Char.ofNat 32, Char.ofNat 97, Char.ofNat 114, Char.ofNat 103, Char.ofNat 117, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116, Char.ofNat 32, Char.ofNat 125]) }, bindingAnnotation := none, hirVisibility := (String.ofList [Char.ofNat 80, Char.ofNat 114, Char.ofNat 105, Char.ofNat 118, Char.ofNat 97, Char.ofNat 116, Char.ofNat 101]), sourceIndexPublic := false, runtimeCell := 0 }, { name := (String.ofList [Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, definitionRoot := R314Artifact.SourceRootIdentity.definition (String.ofList [Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121]) (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]) (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]) 0, declaration := { startByte := 89, endByte := 118, kind := (String.ofList [Char.ofNat 66, Char.ofNat 105, Char.ofNat 110, Char.ofNat 100, Char.ofNat 105, Char.ofNat 110, Char.ofNat 103, Char.ofNat 83, Char.ofNat 116, Char.ofNat 97, Char.ofNat 116, Char.ofNat 101, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116]), text := (String.ofList [Char.ofNat 109, Char.ofNat 121, Char.ofNat 32, Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121, Char.ofNat 32, Char.ofNat 118, Char.ofNat 97, Char.ofNat 108, Char.ofNat 117, Char.ofNat 101, Char.ofNat 32, Char.ofNat 61, Char.ofNat 32, Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101, Char.ofNat 32, Char.ofNat 49, Char.ofNat 32, Char.ofNat 118, Char.ofNat 97, Char.ofNat 108, Char.ofNat 117, Char.ofNat 101]) }, bindingAnnotation := none, hirVisibility := (String.ofList [Char.ofNat 80, Char.ofNat 114, Char.ofNat 105, Char.ofNat 118, Char.ofNat 97, Char.ofNat 116, Char.ofNat 101]), sourceIndexPublic := false, runtimeCell := 1 }, { name := (String.ofList [Char.ofNat 104, Char.ofNat 97, Char.ofNat 110, Char.ofNat 100, Char.ofNat 108, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, definitionRoot := R314Artifact.SourceRootIdentity.definition (String.ofList [Char.ofNat 104, Char.ofNat 97, Char.ofNat 110, Char.ofNat 100, Char.ofNat 108, Char.ofNat 101]) (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]) (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]) 0, declaration := { startByte := 119, endByte := 197, kind := (String.ofList [Char.ofNat 66, Char.ofNat 105, Char.ofNat 110, Char.ofNat 100, Char.ofNat 105, Char.ofNat 110, Char.ofNat 103, Char.ofNat 83, Char.ofNat 116, Char.ofNat 97, Char.ofNat 116, Char.ofNat 101, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116]), text := (String.ofList [Char.ofNat 109, Char.ofNat 121, Char.ofNat 32, Char.ofNat 104, Char.ofNat 97, Char.ofNat 110, Char.ofNat 100, Char.ofNat 108, Char.ofNat 101, Char.ofNat 32, Char.ofNat 40, Char.ofNat 116, Char.ofNat 104, Char.ofNat 117, Char.ofNat 110, Char.ofNat 107, Char.ofNat 58, Char.ofNat 91, Char.ofNat 105, Char.ofNat 111, Char.ofNat 93, Char.ofNat 32, Char.ofNat 105, Char.ofNat 110, Char.ofNat 116, Char.ofNat 41, Char.ofNat 32, Char.ofNat 61, Char.ofNat 32, Char.ofNat 99, Char.ofNat 97, Char.ofNat 116, Char.ofNat 99, Char.ofNat 104, Char.ofNat 32, Char.ofNat 116, Char.ofNat 104, Char.ofNat 117, Char.ofNat 110, Char.ofNat 107, Char.ofNat 32, Char.ofNat 123, Char.ofNat 32, Char.ofNat 105, Char.ofNat 111, Char.ofNat 58, Char.ofNat 58, Char.ofNat 116, Char.ofNat 105, Char.ofNat 99, Char.ofNat 107, Char.ofNat 40, Char.ofNat 112, Char.ofNat 41, Char.ofNat 44, Char.ofNat 32, Char.ofNat 107, Char.ofNat 32, Char.ofNat 45, Char.ofNat 62, Char.ofNat 32, Char.ofNat 104, Char.ofNat 97, Char.ofNat 110, Char.ofNat 100, Char.ofNat 108, Char.ofNat 101, Char.ofNat 32, Char.ofNat 123, Char.ofNat 32, Char.ofNat 107, Char.ofNat 32, Char.ofNat 49, Char.ofNat 48, Char.ofNat 32, Char.ofNat 125, Char.ofNat 32, Char.ofNat 125]) }, bindingAnnotation := none, hirVisibility := (String.ofList [Char.ofNat 80, Char.ofNat 114, Char.ofNat 105, Char.ofNat 118, Char.ofNat 97, Char.ofNat 116, Char.ofNat 101]), sourceIndexPublic := false, runtimeCell := 2 }, { name := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 105, Char.ofNat 110]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, definitionRoot := R314Artifact.SourceRootIdentity.definition (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 105, Char.ofNat 110]) (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]) (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]) 0, declaration := { startByte := 198, endByte := 226, kind := (String.ofList [Char.ofNat 66, Char.ofNat 105, Char.ofNat 110, Char.ofNat 100, Char.ofNat 105, Char.ofNat 110, Char.ofNat 103, Char.ofNat 83, Char.ofNat 116, Char.ofNat 97, Char.ofNat 116, Char.ofNat 101, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116]), text := (String.ofList [Char.ofNat 109, Char.ofNat 121, Char.ofNat 32, Char.ofNat 109, Char.ofNat 97, Char.ofNat 105, Char.ofNat 110, Char.ofNat 32, Char.ofNat 61, Char.ofNat 32, Char.ofNat 104, Char.ofNat 97, Char.ofNat 110, Char.ofNat 100, Char.ofNat 108, Char.ofNat 101, Char.ofNat 32, Char.ofNat 123, Char.ofNat 32, Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121, Char.ofNat 32, Char.ofNat 55, Char.ofNat 32, Char.ofNat 125]) }, bindingAnnotation := none, hirVisibility := (String.ofList [Char.ofNat 80, Char.ofNat 114, Char.ofNat 105, Char.ofNat 118, Char.ofNat 97, Char.ofNat 116, Char.ofNat 101]), sourceIndexPublic := false, runtimeCell := 3 }]
def makeBindingUse : BindingUsePublication := { makeRoot := R315MakeArtifact.rootBinding, makeDefinitionRoot := R314Artifact.SourceRootIdentity.definition (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101]) (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]) (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]) 0, declaration := { startByte := 33, endByte := 88, kind := (String.ofList [Char.ofNat 66, Char.ofNat 105, Char.ofNat 110, Char.ofNat 100, Char.ofNat 105, Char.ofNat 110, Char.ofNat 103, Char.ofNat 83, Char.ofNat 116, Char.ofNat 97, Char.ofNat 116, Char.ofNat 101, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116]), text := (String.ofList [Char.ofNat 109, Char.ofNat 121, Char.ofNat 32, Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101, Char.ofNat 32, Char.ofNat 115, Char.ofNat 101, Char.ofNat 101, Char.ofNat 100, Char.ofNat 32, Char.ofNat 61, Char.ofNat 32, Char.ofNat 123, Char.ofNat 32, Char.ofNat 105, Char.ofNat 111, Char.ofNat 58, Char.ofNat 58, Char.ofNat 116, Char.ofNat 105, Char.ofNat 99, Char.ofNat 107, Char.ofNat 32, Char.ofNat 115, Char.ofNat 101, Char.ofNat 101, Char.ofNat 100, Char.ofNat 59, Char.ofNat 32, Char.ofNat 92, Char.ofNat 97, Char.ofNat 114, Char.ofNat 103, Char.ofNat 117, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116, Char.ofNat 32, Char.ofNat 45, Char.ofNat 62, Char.ofNat 32, Char.ofNat 97, Char.ofNat 114, Char.ofNat 103, Char.ofNat 117, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116, Char.ofNat 32, Char.ofNat 125]) }, bindingAnnotation := none, hirVisibility := (String.ofList [Char.ofNat 80, Char.ofNat 114, Char.ofNat 105, Char.ofNat 118, Char.ofNat 97, Char.ofNat 116, Char.ofNat 101]), sourceIndexPublic := false, initializer := 0, useSite := { bindingName := (String.ofList [Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 14, startByte := 106, endByte := 110 }, useOwner := R314Artifact.ExecutionOwner.invocation 1, useStep := 18, useEnvironment := 2, useScope := R314Artifact.ScopeTag.parameter 0, resolution := R314Artifact.Resolution.moduleDef (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101]) (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]) (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]) 0, consumes := (String.ofList [Char.ofNat 79, Char.ofNat 98, Char.ofNat 115, Char.ofNat 101, Char.ofNat 114, Char.ofNat 118, Char.ofNat 101]), globalCell := 0, cellValue := 5, cellView := 6, cellInterface := R314Artifact.Interface.value, providerSite := { bindingName := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 2, startByte := 33, endByte := 88 }, providerFormal := 0, providerBody := 1, providerEnvironment := 0, providerEnvironmentParent := none, providerInterfaceIsValue := true, useEnvironmentParent := some 0, useEnvironmentBinderKind := some (String.ofList [Char.ofNat 112, Char.ofNat 97, Char.ofNat 114, Char.ofNat 97, Char.ofNat 109, Char.ofNat 101, Char.ofNat 116, Char.ofNat 101, Char.ofNat 114]), useEnvironmentBinderId := some 0, useEnvironmentBinderCell := some 5, useEnvironmentBinderOwner := some (R314Artifact.SourceRootIdentity.definition (String.ofList [Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121]) (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]) (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]) 0), dispatchBase := none, dispatchWord := none, substitution := none, runId := 124250723672840 }
end R315Artifact


namespace R323Artifact
open R314Artifact
def requestEvent : Nat := 0
def operation : String := (String.ofList [Char.ofNat 116, Char.ofNat 105, Char.ofNat 99, Char.ofNat 107])
def operationIdentity : R314Artifact.OperationIdentity := { name := (String.ofList [Char.ofNat 116, Char.ofNat 105, Char.ofNat 99, Char.ofNat 107]), familyRealm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), familyPath := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), familyDeclaration := { startByte := 0, endByte := 32, kind := (String.ofList [Char.ofNat 65, Char.ofNat 99, Char.ofNat 116, Char.ofNat 68, Char.ofNat 101, Char.ofNat 99, Char.ofNat 108, Char.ofNat 97, Char.ofNat 114, Char.ofNat 97, Char.ofNat 116, Char.ofNat 105, Char.ofNat 111, Char.ofNat 110]), text := (String.ofList [Char.ofNat 97, Char.ofNat 99, Char.ofNat 116, Char.ofNat 32, Char.ofNat 105, Char.ofNat 111, Char.ofNat 58, Char.ofNat 10, Char.ofNat 32, Char.ofNat 32, Char.ofNat 32, Char.ofNat 32, Char.ofNat 111, Char.ofNat 117, Char.ofNat 114, Char.ofNat 32, Char.ofNat 116, Char.ofNat 105, Char.ofNat 99, Char.ofNat 107, Char.ofNat 58, Char.ofNat 32, Char.ofNat 105, Char.ofNat 110, Char.ofNat 116, Char.ofNat 32, Char.ofNat 45, Char.ofNat 62, Char.ofNat 32, Char.ofNat 105, Char.ofNat 110, Char.ofNat 116]) }, declaration := { startByte := 12, endByte := 32, kind := (String.ofList [Char.ofNat 66, Char.ofNat 105, Char.ofNat 110, Char.ofNat 100, Char.ofNat 105, Char.ofNat 110, Char.ofNat 103, Char.ofNat 83, Char.ofNat 116, Char.ofNat 97, Char.ofNat 116, Char.ofNat 101, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116]), text := (String.ofList [Char.ofNat 111, Char.ofNat 117, Char.ofNat 114, Char.ofNat 32, Char.ofNat 116, Char.ofNat 105, Char.ofNat 99, Char.ofNat 107, Char.ofNat 58, Char.ofNat 32, Char.ofNat 105, Char.ofNat 110, Char.ofNat 116, Char.ofNat 32, Char.ofNat 45, Char.ofNat 62, Char.ofNat 32, Char.ofNat 105, Char.ofNat 110, Char.ofNat 116]) }, namePosition := { startByte := 16, endByte := 20, kind := (String.ofList [Char.ofNat 73, Char.ofNat 100, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116, Char.ofNat 105, Char.ofNat 102, Char.ofNat 105, Char.ofNat 101, Char.ofNat 114, Char.ofNat 80, Char.ofNat 97, Char.ofNat 116, Char.ofNat 116, Char.ofNat 101, Char.ofNat 114, Char.ofNat 110]), text := (String.ofList [Char.ofNat 116, Char.ofNat 105, Char.ofNat 99, Char.ofNat 107]) }, signaturePosition := { startByte := 22, endByte := 32, kind := (String.ofList [Char.ofNat 84, Char.ofNat 121, Char.ofNat 112, Char.ofNat 101, Char.ofNat 69, Char.ofNat 120, Char.ofNat 112, Char.ofNat 114, Char.ofNat 101, Char.ofNat 115, Char.ofNat 115, Char.ofNat 105, Char.ofNat 111, Char.ofNat 110]), text := (String.ofList [Char.ofNat 105, Char.ofNat 110, Char.ofNat 116, Char.ofNat 32, Char.ofNat 45, Char.ofNat 62, Char.ofNat 32, Char.ofNat 105, Char.ofNat 110, Char.ofNat 116]) }, startByte := 12, endByte := 32, visibility := (String.ofList [Char.ofNat 79, Char.ofNat 117, Char.ofNat 114]), signature := R314Artifact.AnnotationType.mk (R314Artifact.SourceType.function (R314Artifact.AnnotationType.mk (R314Artifact.SourceType.int) (none)) (R314Artifact.AnnotationType.mk (R314Artifact.SourceType.int) (none))) (none) }
def requestSite : R314Artifact.RuntimeSite := { bindingName := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 4, startByte := 59, endByte := 63 }
def requestOwner : R314Artifact.ExecutionOwner := R314Artifact.ExecutionOwner.invocation 2
def requestOwnerWasLive : Bool := true
def payload : R314Artifact.Received := { value := 7, view := 8, interface := R314Artifact.Interface.value, dispatch := none }
def payloadRuntimeValue : R314Artifact.RuntimeValue := { source := { bindingName := (String.ofList [Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 15, startByte := 111, endByte := 112 }, kind := R314Artifact.ValueKind.integer (String.ofList [Char.ofNat 49]) }
def templateHandle : Nat := 0
def templateRoot : Nat := 6
def templateNodeCount : Nat := 7
def captureOwner : R314Artifact.ExecutionOwner := R314Artifact.ExecutionOwner.invocation 0
structure R323CodeRef where
  label : Nat
  site : R314Artifact.RuntimeSite
  deriving Repr
structure R323CalleeFrame where
  frameId : Nat
  callee : Option R323CodeRef
  argument : R323CodeRef
  environment : Nat
  site : R314Artifact.RuntimeSite
  deriving Repr
structure R323BlockExpressionFrame where
  codeLabel : Nat
  codeSite : R314Artifact.RuntimeSite
  next : Nat
  environment : Nat
  deriving Repr
structure R323RootCompReturn where
  view : Nat
  receipt : Nat
  occurrence : Nat
  deriving Repr
inductive R323Frame where
  | callee (frame : R323CalleeFrame)
  | blockExpression (frame : R323BlockExpressionFrame)
  | rootCompReturn (execution : R323RootCompReturn)
  | owner (owner : R314Artifact.ExecutionOwner)
  deriving Repr
def savedFrameOrder : List R323Frame := [R323Frame.blockExpression { codeLabel := 1, codeSite := { bindingName := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 3, startByte := 48, endByte := 88 }, next := 1, environment := 3 }, R323Frame.owner (R314Artifact.ExecutionOwner.invocation 2), R323Frame.callee { frameId := 2, callee := some ({ label := 9, site := { bindingName := (String.ofList [Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 13, startByte := 111, endByte := 112 } }), argument := { label := 10, site := { bindingName := (String.ofList [Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 16, startByte := 113, endByte := 118 } }, environment := 2, site := { bindingName := (String.ofList [Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 12, startByte := 113, endByte := 118 } }, R323Frame.owner (R314Artifact.ExecutionOwner.invocation 1), R323Frame.rootCompReturn { view := 2, receipt := 2, occurrence := 0 }]
def templateFrameOrder : List R323Frame := [R323Frame.blockExpression { codeLabel := 1, codeSite := { bindingName := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 3, startByte := 48, endByte := 88 }, next := 1, environment := 3 }, R323Frame.owner (R314Artifact.ExecutionOwner.invocation 2), R323Frame.callee { frameId := 2, callee := some ({ label := 9, site := { bindingName := (String.ofList [Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 13, startByte := 111, endByte := 112 } }), argument := { label := 10, site := { bindingName := (String.ofList [Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 16, startByte := 113, endByte := 118 } }, environment := 2, site := { bindingName := (String.ofList [Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 12, startByte := 113, endByte := 118 } }, R323Frame.owner (R314Artifact.ExecutionOwner.invocation 1), R323Frame.rootCompReturn { view := 2, receipt := 2, occurrence := 0 }]
def templateInnerByNode : List (Option Nat) := [none, some 0, some 1, some 2, some 3, some 4, some 5]
def outerCalleeFrame : Nat := 2
def outerCalleeSite : R314Artifact.RuntimeSite := { bindingName := (String.ofList [Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 12, startByte := 113, endByte := 118 }
def resumeRequestEvent : Nat := 0
def resumeTemplateHandle : Nat := 0
def responseValue : Nat := 14
def responseView : Nat := 16
def response : R314Artifact.Received := { value := 14, view := 16, interface := R314Artifact.Interface.value, dispatch := none }
def responseRuntimeValue : R314Artifact.RuntimeValue := { source := { bindingName := (String.ofList [Char.ofNat 104, Char.ofNat 97, Char.ofNat 110, Char.ofNat 100, Char.ofNat 108, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 27, startByte := 191, endByte := 193 }, kind := R314Artifact.ValueKind.integer (String.ofList [Char.ofNat 49, Char.ofNat 48]) }
def responseStep : Nat := 48
def responseSite : R314Artifact.RuntimeSite := { bindingName := (String.ofList [Char.ofNat 104, Char.ofNat 97, Char.ofNat 110, Char.ofNat 100, Char.ofNat 108, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 25, startByte := 191, endByte := 193 }
def responseOwner : R314Artifact.ExecutionOwner := R314Artifact.ExecutionOwner.invocation 5
def responseOwnerWasLive : Bool := true
def responseHoleNode : Nat := 0
def responseHoleOwner : R314Artifact.ExecutionOwner := R314Artifact.ExecutionOwner.invocation 7
def responseHoleOwnerWasLive : Bool := true
def responseHoleStep : Nat := 55
def selectedReceiverActivation : Nat := 8
def selectedReceiverOwner : R314Artifact.ExecutionOwner := R314Artifact.ExecutionOwner.invocation 8
def selectedReceiverPreviousOwner : R314Artifact.ExecutionOwner := R314Artifact.ExecutionOwner.invocation 6
def selectedReceiverCallSite : R314Artifact.RuntimeSite := { bindingName := (String.ofList [Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 12, startByte := 113, endByte := 118 }
def selectedReceiverProviderSite : R314Artifact.RuntimeSite := { bindingName := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 7, startByte := 65, endByte := 86 }
def selectedReceiverReturnValue : Nat := 4
def selectedReceiverReturnView : Nat := 5
def selectedReceiverReturnInterface : R314Artifact.Interface := R314Artifact.Interface.value
def selectedReceiverReturnDispatch : Option Nat := none
def selectedReceiverReturnRuntimeValue : R314Artifact.RuntimeValue := { source := { bindingName := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 105, Char.ofNat 110]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 35, startByte := 223, endByte := 224 }, kind := R314Artifact.ValueKind.integer (String.ofList [Char.ofNat 55]) }
def selectedReceiverReturnStep : Nat := 63
def selectedDefinitionResult : Nat := 4
def selectedDefinitionResultView : Nat := 5
def selectedDefinitionResultOwner : R314Artifact.ExecutionOwner := R314Artifact.ExecutionOwner.moduleRun
def selectedDefinitionResultInterface : R314Artifact.Interface := R314Artifact.Interface.value
def selectedDefinitionResultDispatch : Option Nat := none
def selectedDefinitionResultRuntimeValue : R314Artifact.RuntimeValue := { source := { bindingName := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 105, Char.ofNat 110]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 35, startByte := 223, endByte := 224 }, kind := R314Artifact.ValueKind.integer (String.ofList [Char.ofNat 55]) }
def selectedDefinitionResultStep : Nat := 73
structure OwnerReplay where
  node : Nat
  original : R314Artifact.ExecutionOwner
  resolved : R314Artifact.ExecutionOwner
  resolvedWasActive : Bool
  owner : R314Artifact.ExecutionOwner
  owned : Bool
  previous : R314Artifact.ExecutionOwner
  ownerLive : Bool
  currentOwnerAfter : R314Artifact.ExecutionOwner
  control : List (Nat × Nat)
  callSite : Option R314Artifact.RuntimeSite
  providerSite : Option R314Artifact.RuntimeSite
  deriving Repr
def ownerReplay : List OwnerReplay := [{ node := 6, original := R314Artifact.ExecutionOwner.invocation 0, resolved := R314Artifact.ExecutionOwner.invocation 0, resolvedWasActive := true, owner := R314Artifact.ExecutionOwner.invocation 0, owned := false, previous := R314Artifact.ExecutionOwner.invocation 5, ownerLive := true, currentOwnerAfter := R314Artifact.ExecutionOwner.invocation 0, control := [], callSite := some ({ bindingName := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 105, Char.ofNat 110]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 30, startByte := 215, endByte := 226 }), providerSite := some ({ bindingName := (String.ofList [Char.ofNat 104, Char.ofNat 97, Char.ofNat 110, Char.ofNat 100, Char.ofNat 108, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 19, startByte := 119, endByte := 197 }) }, { node := 4, original := R314Artifact.ExecutionOwner.invocation 1, resolved := R314Artifact.ExecutionOwner.invocation 1, resolvedWasActive := false, owner := R314Artifact.ExecutionOwner.invocation 6, owned := true, previous := R314Artifact.ExecutionOwner.invocation 0, ownerLive := true, currentOwnerAfter := R314Artifact.ExecutionOwner.invocation 6, control := [(0, 0)], callSite := some ({ bindingName := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 105, Char.ofNat 110]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 33, startByte := 223, endByte := 224 }), providerSite := some ({ bindingName := (String.ofList [Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 11, startByte := 89, endByte := 118 }) }, { node := 2, original := R314Artifact.ExecutionOwner.invocation 2, resolved := R314Artifact.ExecutionOwner.invocation 2, resolvedWasActive := false, owner := R314Artifact.ExecutionOwner.invocation 7, owned := true, previous := R314Artifact.ExecutionOwner.invocation 6, ownerLive := true, currentOwnerAfter := R314Artifact.ExecutionOwner.invocation 7, control := [(0, 0), (1, 6)], callSite := some ({ bindingName := (String.ofList [Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 13, startByte := 111, endByte := 112 }), providerSite := some ({ bindingName := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 2, startByte := 33, endByte := 88 }) }]
end R323Artifact

end Legacy
-- END EXACT R335 HISTORICAL WRAPPER
end YulangClosure.OriginalWitnessIntegrationR339.Native

namespace YulangClosure.OriginalWitnessIntegrationR339.Native.Selected
open NativeClosureEnvironment SourceIdentityWorld OriginalSourceInterpretation
open OriginalParameterSemantics OriginalReceiverReturnRefinementR338
open R323Artifact

-- Interpret source-owner constructors only, without touching semantic Provider.
def owner : R314Artifact.ExecutionOwner → Owner
  | .moduleRun => .moduleRun
  | .invocation id => .invocation id

def entry : R314Artifact.Interface → Entry
  | .value => .value
  | .computation => .computation

def rows (table : List R338InvocationSnapshot) : List (Invocation R314Artifact.RuntimeSite) :=
  table.map fun row => ⟨row.call, row.provider, row.active⟩

def snapshotBefore : NativeControl R314Artifact.RuntimeSite :=
  ⟨rows selectedReceiverPostExitInvocationTableBefore,
    selectedReceiverPostExitNativeActiveReceiversBefore,
    owner selectedReceiverPostExitOwnerBefore⟩

def snapshotAfter : NativeControl R314Artifact.RuntimeSite :=
  ⟨rows selectedReceiverPostExitInvocationTableAfter,
    selectedReceiverPostExitNativeActiveReceiversAfter,
    owner selectedReceiverPostExitOwnerAfter⟩

def input : Received Nat :=
  ⟨selectedReceiverPostExitIncoming.value, entry selectedReceiverPostExitIncoming.interface,
    selectedReceiverPostExitIncoming.view, selectedReceiverPostExitIncoming.dispatch⟩

def observed : Received Nat :=
  ⟨selectedReceiverPostExitReturnValue, entry selectedReceiverPostExitReturnInterface,
    selectedReceiverPostExitReturnView, selectedReceiverPostExitReturnDispatch⟩

def selectedInvocation : Invocation R314Artifact.RuntimeSite :=
  ⟨selectedReceiverPostExitCallSite, selectedReceiverPostExitProviderSite, true⟩

def activation := selectedReceiverPostExitActivation
def previous := owner selectedReceiverPostExitPreviousOwner

theorem table_indices :
    selectedReceiverPostExitInvocationTableBefore.map (·.id) = List.range 9 ∧
    selectedReceiverPostExitInvocationTableAfter.map (·.id) = List.range 9 := ⟨rfl, rfl⟩

/-- Entire computed native outcome equals the observed post table/stack/owner.
No successful transition or postcondition is an assumption. -/
theorem native_exit : nativeLeaveOwned snapshotBefore activation previous =
    .ok snapshotAfter := by rfl

theorem input_guards :
    snapshotBefore.current = .invocation activation ∧
    snapshotBefore.activeReceivers.reverse = activation :: [6, 5, 4, 0] ∧
    snapshotBefore.invocations[activation]? = some selectedInvocation ∧
    selectedInvocation.active = true := ⟨rfl, rfl, rfl, rfl⟩

theorem packet_from_input : input.asValue = observed := rfl

/-- Source call/provider and packet match R335 receipts retained in SAME run. -/
theorem selected_trace_join :
    activation = selectedReceiverActivation ∧
    previous = owner selectedReceiverPreviousOwner ∧
    selectedInvocation.call = selectedReceiverCallSite ∧
    selectedInvocation.provider = selectedReceiverProviderSite ∧
    observed.value = selectedReceiverReturnValue ∧
    observed.view = selectedReceiverReturnView ∧
    observed.dispatch = selectedReceiverReturnDispatch ∧
    observed.interface = entry selectedReceiverReturnInterface ∧
    observed.value = selectedDefinitionResult ∧
    observed.view = selectedDefinitionResultView ∧
    observed.dispatch = selectedDefinitionResultDispatch ∧
    observed.interface = entry selectedDefinitionResultInterface ∧
    selectedReceiverPostExitStepBefore = selectedReceiverReturnStep ∧
    selectedReceiverPostExitStepAfter < selectedDefinitionResultStep := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide⟩

/-- Historical artifact equality compares static addresses/packet fields, not
runtime run identity across separate runs. -/
theorem authentic_r335_legacy_join :
    activation = Legacy.R323Artifact.selectedReceiverActivation ∧
    observed.value = Legacy.R323Artifact.selectedReceiverReturnValue ∧
    observed.view = Legacy.R323Artifact.selectedReceiverReturnView ∧
    observed.dispatch = Legacy.R323Artifact.selectedReceiverReturnDispatch ∧
    selectedInvocation.call.occurrence = Legacy.R323Artifact.selectedReceiverCallSite.occurrence ∧
    selectedInvocation.provider.occurrence = Legacy.R323Artifact.selectedReceiverProviderSite.occurrence ∧
    selectedReceiverPostExitStepBefore = Legacy.R323Artifact.selectedReceiverReturnStep :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Stores are arbitrary: snapshots do not pretend to record environment,
cells or receiving stores. Preservation follows from the actual branch model. -/
theorem world_return (world : World K D Nat ViewData R314Artifact.RuntimeSite Rest) :
    let before := { world with control := snapshotBefore.project }
    receiverReturn before activation previous input =
      .returned { world with control := snapshotAfter.project } observed ∧
    returnOwned before activation previous input =
      some ({ world with control := snapshotAfter.project }, observed) := by
  have projected := native_leave_refines snapshotBefore activation previous
  rw [native_exit] at projected
  have left : leaveOwned snapshotBefore.project activation previous = .ok snapshotAfter.project :=
    projected.symm
  constructor
  · simp only [receiverReturn, left]
    rfl
  · rw [← receiver_return_refines]
    simp only [receiverReturn, left]
    rfl

/-- The computed complete projected world equals the actual observed control
with arbitrary untouched stores. Equality is derived from the input-run proof. -/
theorem computed_world_is_observed (world : World K D Nat ViewData R314Artifact.RuntimeSite Rest) :
    exited { world with control := snapshotBefore.project } activation previous
      [6, 5, 4, 0] selectedInvocation = { world with control := snapshotAfter.project } := by
  have constructed := receiver_return_construct { world with control := snapshotBefore.project }
    activation previous input [6, 5, 4, 0] selectedInvocation
    input_guards.1 input_guards.2.1 input_guards.2.2.1 input_guards.2.2.2
  exact congrArg Prod.fst (Option.some.inj (constructed.2.1.symm.trans (world_return world).2))

def beforeEvent {b : Sorts} {D ViewData Rest Body View : Type}
    (event : Event (NS b D Nat ViewData R314Artifact.RuntimeSite Rest Body View)) :=
  { event with current := { event.current with
      world := { event.current.world with control := snapshotBefore.project } } }

def afterEvent {b : Sorts} {D ViewData Rest Body View : Type}
    (event : Event (NS b D Nat ViewData R314Artifact.RuntimeSite Rest Body View)) :=
  { event with current := { event.current with
      world := { event.current.world with control := snapshotAfter.project } } }

theorem computed_event_is_observed {b : Sorts} {D ViewData Rest Body View : Type}
    (event : Event (NS b D Nat ViewData R314Artifact.RuntimeSite Rest Body View)) :
    exitEvent (beforeEvent event) activation previous [6, 5, 4, 0] selectedInvocation =
      afterEvent event := by
  unfold exitEvent beforeEvent afterEvent
  rw [computed_world_is_observed]

/-- Apply actual guards to R337's original Event consumer, now at the observed
post-exit control, without any event inequality hypothesis. -/
theorem event_changes {b : Sorts} {D ViewData Rest Body View : Type}
    (event : Event (NS b D Nat ViewData R314Artifact.RuntimeSite Rest Body View)) :
    afterEvent event ≠ beforeEvent event := by
  have different := exit_event_differs (beforeEvent event) activation previous input
    [6, 5, 4, 0] selectedInvocation
    input_guards.1 input_guards.2.1 input_guards.2.2.1 input_guards.2.2.2
  rw [computed_event_is_observed] at different
  exact different

/-- Apply the original Return clause at this actual post-exit control, keeping
all of its remaining semantic obligations explicit. Raw native value 4 is
interpreted using the SAME original eta, not substituted for a semantic value. -/
theorem original_trace_iff {b : Sorts} {D ViewData Rest Body View : Type}
    (inputs : Inputs (NS b D Nat ViewData R314Artifact.RuntimeSite Rest Body View))
    (event : Event (NS b D Nat ViewData R314Artifact.RuntimeSite Rest Body View))
    (descriptor : b.Descriptor) (observation : b.Observation) (interface : b.Interface)
    (form : inputs.traceForm ⟨interface, observation, afterEvent event⟩ =
      .pureReturn ⟨descriptor, event.eta.views.value observed.value,
        event.eta.views.root observed.value, afterEvent event⟩) :
    let trace : TraceRow (NS b D Nat ViewData R314Artifact.RuntimeSite Rest Body View) :=
      ⟨interface, observation, afterEvent event⟩
    Meaning inputs (.trace trace) ↔
      inputs.eventCoherent (afterEvent event) ∧ (inputs.observationGuards trace).Valid ∧
      Meaning inputs (.world (afterEvent event)) ∧
      Meaning inputs (.value ⟨descriptor, event.eta.views.value observed.value,
        event.eta.views.root observed.value, afterEvent event⟩) ∧
      (inputs.observationFields trace).Holds (Meaning inputs) := by
  have fixed : nativeResult (beforeEvent event) descriptor input activation previous
      [6, 5, 4, 0] selectedInvocation =
      ⟨descriptor, event.eta.views.value observed.value,
        event.eta.views.root observed.value, afterEvent event⟩ := by
    unfold nativeResult
    rw [computed_event_is_observed]
    rfl
  have readout : inputs.traceForm ⟨interface, observation,
      exitEvent (beforeEvent event) activation previous [6, 5, 4, 0] selectedInvocation⟩ =
      .pureReturn (nativeResult (beforeEvent event) descriptor input activation previous
        [6, 5, 4, 0] selectedInvocation) := by
    rw [computed_event_is_observed, fixed]
    exact form
  have applied := post_exit_return_iff inputs (beforeEvent event) activation previous
    [6, 5, 4, 0] selectedInvocation descriptor input observation interface readout
  dsimp only at applied ⊢
  rw [computed_event_is_observed, fixed] at applied
  exact applied

end YulangClosure.OriginalWitnessIntegrationR339.Native.Selected

namespace YulangClosure.OriginalWitnessIntegrationR339

/-! Explicit structural bridges to the old imported source namespace. These
maps preserve every represented field; no nominal schema equality is assumed.
The native operation remains a source declaration, not a semantic Provider. -/
namespace Correspondence

def position (p : Native.R314Artifact.Position) :
    OriginalModuleContextBindingR315.Native.Make.Position :=
  ⟨p.startByte, p.endByte, p.kind, p.text⟩

def effectId (e : Native.R314Artifact.EffectId) :
    OriginalModuleContextBindingR315.Native.Make.EffectId :=
  ⟨e.realm, e.path, position e.declaration⟩

def effectRow (e : Native.R314Artifact.EffectRow) :
    OriginalModuleContextBindingR315.Native.Make.EffectRow :=
  ⟨position e.position, e.concrete.map effectId, e.variables⟩

/-- All exported annotation constructors and optional effect rows are retained.
This is data translation, without interpreting the signature's semantics. -/
def annotation : Native.R314Artifact.AnnotationType →
    OriginalModuleContextBindingR315.Native.Make.AnnotationType
  | .mk .unit effects => .mk .unit (effects.map effectRow)
  | .mk .int effects => .mk .int (effects.map effectRow)
  | .mk .bool effects => .mk .bool (effects.map effectRow)
  | .mk .str effects => .mk .str (effects.map effectRow)
  | .mk (.variable name) effects => .mk (.variable name) (effects.map effectRow)
  | .mk (.hole p) effects => .mk (.hole (position p)) (effects.map effectRow)
  | .mk (.tuple items) effects => .mk (.tuple (items.map annotation)) (effects.map effectRow)
  | .mk (.function argument result) effects =>
      .mk (.function (annotation argument) (annotation result)) (effects.map effectRow)

def operation (d : Native.R314Artifact.OperationIdentity) :
    OriginalModuleContextBindingR315.Native.Make.OperationIdentity :=
  ⟨d.name, d.familyRealm, d.familyPath, position d.familyDeclaration,
    position d.declaration, position d.namePosition, position d.signaturePosition,
    d.startByte, d.endByte, d.visibility, annotation d.signature⟩

def site (s : Native.R314Artifact.RuntimeSite) :
    OriginalModuleContextBindingR315.Native.Current.RuntimeSite :=
  ⟨s.bindingName, s.realm, s.path, s.sameNameOrdinal, s.occurrence, s.startByte, s.endByte⟩

/-- Exact source bytes agree with the original committed source witness and
with the older comparison artifact. This says nothing about run identity. -/
theorem source_identity :
    Native.R314Artifact.sourceText = OriginalModuleContextBindingR315.Native.Current.sourceText ∧
    Native.R315MakeArtifact.sourceText = OriginalModuleContextBindingR315.Native.Make.sourceText ∧
    Native.R314Artifact.sourceText = Native.Legacy.R314Artifact.sourceText :=
  ⟨rfl, rfl, rfl⟩

/-- Full physical operation identity AND full exported signature agree with
R321's actual source declaration; operation spelling alone is insufficient. -/
theorem tick_identity :
    operation Native.R323Artifact.operationIdentity = OriginalTickDeclaredResponseR321.tick := by
  simp only [operation, Native.R323Artifact.operationIdentity, annotation]
  rfl

/-- All physical source address components, including realm/path and ordinal,
connect the selected native invocation to the old imported source occurrence. -/
theorem call_site_identity :
    site Native.R323Artifact.selectedReceiverPostExitCallSite =
      OriginalModuleContextBindingR315.Native.Current.returnSnapshot.applySite := rfl

/-- The current composite keeps its run ID verbatim and its source/global-cell
witnesses share that ID. The historical comparison remains a DIFFERENT run. -/
theorem run_identity :
    Native.R314Artifact.runId = 129221288479048 ∧
    Native.R314Artifact.runId = Native.R314Artifact.returnSnapshot.runId ∧
    Native.R314Artifact.runId = Native.R315Artifact.makeBindingUse.runId ∧
    Native.R314Artifact.runId ≠ Native.Legacy.R314Artifact.runId := by
  exact ⟨rfl, rfl, rfl, by decide⟩

end Correspondence

/-- Both original-module applications coexist in one checked environment.
The operation VALUE Return and the selected resumed receiver exit are distinct
phases. No equality of their values, events or semantic providers is claimed. -/
theorem primitive_and_selected_exit
    {C Dict Rest Schema : Type} (origin : OriginalSource.Declaration)
    (raw : OriginalCalleeDelayProvenance.Raw C Dict Rest Schema) :
    OriginalSourceScopedInterpretationR335.readPrimitive origin []
      OriginalModuleContextBindingR315.makeInitializer
      (OriginalSourceScopedInterpretationR335.tickRequest origin).operands.callee.key
      .primitiveDeclarationInstance =
        some (OriginalSourceScopedInterpretationR335.tickPrimitive origin) ∧
    SourceIdentityWorld.Matches
      (OriginalCalleeDelayProvenance.project
        (OriginalPrimitiveValueReturnR338.tickData origin raw)).world.receiving
      (OriginalPrimitiveValueReturnR338.returned raw) ∧
    OriginalReceiverReturnRefinementR338.nativeLeaveOwned
      Native.Selected.snapshotBefore Native.Selected.activation Native.Selected.previous =
        .ok Native.Selected.snapshotAfter := by
  have primitive := OriginalPrimitiveValueReturnR338.tick_declared_value_return origin raw
  exact ⟨primitive.1, primitive.2.2, Native.Selected.native_exit⟩

end YulangClosure.OriginalWitnessIntegrationR339
