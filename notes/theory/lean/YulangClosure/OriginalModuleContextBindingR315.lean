import YulangClosure.OriginalScopedSourceEventMapR314
import YulangClosure.OriginalSourceContractResolutionR311

/-!
R315: original module-binding construction at the R314 source occurrence.
Authority: adopted SG §§3.1, 3.3, 4, 5.2; selected EI §§3.1–3.4.
The published Name instance and original semantic atoms remain independent
obligations. No alternate kernel or formal-binding interpretation is selected.
-/



-- BEGIN authenticated native payload
namespace YulangClosure.OriginalModuleContextBindingR315.Native
namespace Current

structure Position where
  startByte : Nat
  endByte : Nat
  kind : String
  text : String

inductive ScopeTag where
  | definition | moduleExpression | sourceMember
  | expression (id : Nat) | parameter (id : Nat) | localInitializer (id : Nat)
  | catchArm (id : Nat) (arm : Position)

structure RootBinding where
  name : String
  realm : String
  path : String
  sameNameOrdinal : Nat

inductive ExecutionOwner where | moduleRun | invocation (id : Nat)
inductive SourceRootIdentity where
  | definition (bindingName realm path : String) (sameNameOrdinal : Nat)
  | expression (occurrence : Nat)
  | member (realm path kind : String) (declaration member : Position)

structure RuntimeSite where
  bindingName : String
  realm : String
  path : String
  sameNameOrdinal : Nat
  occurrence : Nat
  startByte : Nat
  endByte : Nat

inductive Interface where | value | computation
structure Received where
  value : Nat
  view : Nat
  interface : Interface
  dispatch : Option Nat

structure RuntimeCell where
  value : Option Received

structure RuntimeEnvironment where
  parent : Option Nat
  binderKind : Option String
  binderId : Option Nat
  binderCell : Option Nat
  binderOwner : Option SourceRootIdentity
  dispatchBase : Option Nat
  dispatchWord : Option Nat
  substitution : Option Nat

inductive ReceivingViewKind where
  | ordinary | rootComp | callbackEntry (id : Nat) | callbackResult (id : Nat)

structure ReceivingView where
  index : Nat
  value : Nat
  image : Option Nat
  unknown : Bool
  kind : ReceivingViewKind

structure ImageLink where
  image : Nat
  boundary : Nat
  receiver : Nat

structure ViewImageChain where
  view : Nat
  links : List ImageLink

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

inductive Resolution where
  | moduleDef (name : String) (realm : String) (path : String) (ordinal : Nat)
  | parameter (id : Nat) | local (id : Nat) | catchBinder (id : Nat) | caseBinder (id : Nat)
  | unresolved | ambiguous

structure EffectId where
  realm : String
  path : String
  declaration : Position

structure EffectRow where
  position : Position
  concrete : List EffectId
  variables : List String

mutual
inductive SourceType where
  | unit | int | bool | str | variable (name : String) | hole (position : Position)
  | tuple (items : List AnnotationType) | function (argument result : AnnotationType)

inductive AnnotationType where
  | mk (value : SourceType) (effects : Option EffectRow)

end
structure Annotation where
  owner : String
  position : Position
  type : AnnotationType

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

inductive ValueKind where
  | unit | integer (value : String) | boolean (value : Bool) | string (value : String)
  | primitive (name : String) | tuple (items : List Received)
  | variant (tag : String) (items : List Received)
  | record (fields : List (String × Received)) | closure | computation
  | operation (identity : OperationIdentity)

structure RuntimeValue where
  source : RuntimeSite
  kind : ValueKind

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

structure Formal where
  id : Nat
  spelling : String
  startByte : Nat
  endByte : Nat
  sourcePosition : Position
  scope : ScopeTag
  annotation : Option Annotation

inductive BlockStatement where
  | expression (code : Nat) | binding (ordinal localId initializer : Nat)

inductive SourceStatement where
  | expression (source : Nat) | binding (ordinal localId initializer : Nat)

structure SourceStatementBlock where
  statements : List SourceStatement
  finalExpression : Nat

structure InstructionStatementBlock where
  statements : List BlockStatement
  finalExpression : Nat

inductive SourceForm where
  | unit | integer (value : String) | boolean (value : Bool) | string (value : String)
  | decodedString (value : String) | name (spelling : String) (resolution : Resolution)
  | apply (syntaxKind : String) (callee argument : Nat) | group (inner : Nat)
  | ascription (annotation : Annotation) (inner : Nat) | lambda (formal : Formal) (body : Nat)
  | operation (identity : OperationIdentity) | block (bindings : List (Nat × Nat)) (finalExpression : Nat)
  | statementBlock (block : SourceStatementBlock)

inductive Instruction where
  | unit | integer (value : String) | boolean (value : Bool) | string (value : String)
  | decodedString (value : String) | name (resolution : Resolution) (consumption : String)
  | apply (callee argument : Nat) | forward (inner : Nat) | lambda (formalId body : Nat)
  | operation (identity : OperationIdentity) | block (bindings : List (Nat × Nat)) (finalExpression : Nat)
  | statementBlock (block : InstructionStatementBlock)

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
def runId : Nat := 135158189492808
def events : List RuntimeEvent := [RuntimeEvent.request 32 14 0 ({ bindingName := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 4, startByte := 59, endByte := 63 }) (ExecutionOwner.invocation 2),
RuntimeEvent.pendingCallee 32 15 0 2 10 2 (some 9) ({ bindingName := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 4, startByte := 59, endByte := 63 }) ({ bindingName := (String.ofList [Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 12, startByte := 113, endByte := 118 }) (ExecutionOwner.invocation 2),
RuntimeEvent.calleeReturn 59 22 2 10 2 15 17 (some 9) ({ bindingName := (String.ofList [Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 12, startByte := 113, endByte := 118 }) (ExecutionOwner.invocation 6) Interface.value ({ bindingName := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 7, startByte := 65, endByte := 86 }),
RuntimeEvent.delay 16 10 2 18,
RuntimeEvent.nameLookup 60 24 2 0 5 4 5 (({ bindingName := (String.ofList [Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 16, startByte := 113, endByte := 118 })) (ExecutionOwner.invocation 8) ((String.ofList [Char.ofNat 79, Char.ofNat 98, Char.ofNat 115, Char.ofNat 101, Char.ofNat 114, Char.ofNat 118, Char.ofNat 101])),
RuntimeEvent.nameReceipt 60 25 10 4 5 (({ bindingName := (String.ofList [Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 16, startByte := 113, endByte := 118 })) (ExecutionOwner.invocation 8) ((String.ofList [Char.ofNat 79, Char.ofNat 98, Char.ofNat 115, Char.ofNat 101, Char.ofNat 114, Char.ofNat 118, Char.ofNat 101])),
RuntimeEvent.valueBind 15 7 1 0 5 2 4 5 Interface.value,
RuntimeEvent.valueBind 23 10 2 0 6 3 7 8 Interface.value,
RuntimeEvent.valueBind 61 26 8 1 10 7 4 5 Interface.value]
def returnSnapshot : ReturnSnapshot := { runId := 135158189492808, frame := 2, applySite := { bindingName := (String.ofList [Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 12, startByte := 113, endByte := 118 }, argumentLabel := 10, callerEnvironment := 2, cells := [{ value := some { value := 5, view := 6, interface := Interface.value, dispatch := none } }, { value := some { value := 2, view := 3, interface := Interface.value, dispatch := none } }, { value := some { value := 0, view := 0, interface := Interface.value, dispatch := none } }, { value := none }, { value := some { value := 1, view := 2, interface := Interface.computation, dispatch := none } }, { value := some { value := 4, view := 5, interface := Interface.value, dispatch := none } }, { value := some { value := 7, view := 8, interface := Interface.value, dispatch := none } }, { value := some { value := 7, view := 8, interface := Interface.value, dispatch := none } }, { value := some { value := 11, view := 12, interface := Interface.value, dispatch := none } }, { value := some { value := 12, view := 14, interface := Interface.computation, dispatch := none } }], environments := [{ parent := none, binderKind := none, binderId := none, binderCell := none, binderOwner := none, dispatchBase := none, dispatchWord := none, substitution := none }, { parent := some 0, binderKind := some (String.ofList [Char.ofNat 112, Char.ofNat 97, Char.ofNat 114, Char.ofNat 97, Char.ofNat 109, Char.ofNat 101, Char.ofNat 116, Char.ofNat 101, Char.ofNat 114]), binderId := some 0, binderCell := some 4, binderOwner := some (SourceRootIdentity.definition (String.ofList [Char.ofNat 104, Char.ofNat 97, Char.ofNat 110, Char.ofNat 100, Char.ofNat 108, Char.ofNat 101]) (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]) (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]) 0), dispatchBase := none, dispatchWord := none, substitution := none }, { parent := some 0, binderKind := some (String.ofList [Char.ofNat 112, Char.ofNat 97, Char.ofNat 114, Char.ofNat 97, Char.ofNat 109, Char.ofNat 101, Char.ofNat 116, Char.ofNat 101, Char.ofNat 114]), binderId := some 0, binderCell := some 5, binderOwner := some (SourceRootIdentity.definition (String.ofList [Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121]) (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]) (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]) 0), dispatchBase := none, dispatchWord := none, substitution := none }, { parent := some 0, binderKind := some (String.ofList [Char.ofNat 112, Char.ofNat 97, Char.ofNat 114, Char.ofNat 97, Char.ofNat 109, Char.ofNat 101, Char.ofNat 116, Char.ofNat 101, Char.ofNat 114]), binderId := some 0, binderCell := some 6, binderOwner := some (SourceRootIdentity.definition (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101]) (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]) (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]) 0), dispatchBase := none, dispatchWord := none, substitution := none }, { parent := some 1, binderKind := some (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 116, Char.ofNat 99, Char.ofNat 104]), binderId := some 0, binderCell := some 7, binderOwner := some (SourceRootIdentity.definition (String.ofList [Char.ofNat 104, Char.ofNat 97, Char.ofNat 110, Char.ofNat 100, Char.ofNat 108, Char.ofNat 101]) (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]) (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]) 0), dispatchBase := none, dispatchWord := none, substitution := none }, { parent := some 4, binderKind := some (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 116, Char.ofNat 99, Char.ofNat 104]), binderId := some 1, binderCell := some 8, binderOwner := some (SourceRootIdentity.definition (String.ofList [Char.ofNat 104, Char.ofNat 97, Char.ofNat 110, Char.ofNat 100, Char.ofNat 108, Char.ofNat 101]) (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]) (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]) 0), dispatchBase := none, dispatchWord := none, substitution := none }, { parent := some 0, binderKind := some (String.ofList [Char.ofNat 112, Char.ofNat 97, Char.ofNat 114, Char.ofNat 97, Char.ofNat 109, Char.ofNat 101, Char.ofNat 116, Char.ofNat 101, Char.ofNat 114]), binderId := some 0, binderCell := some 9, binderOwner := some (SourceRootIdentity.definition (String.ofList [Char.ofNat 104, Char.ofNat 97, Char.ofNat 110, Char.ofNat 100, Char.ofNat 108, Char.ofNat 101]) (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]) (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]) 0), dispatchBase := none, dispatchWord := none, substitution := none }], values := [{ source := { bindingName := (String.ofList [Char.ofNat 104, Char.ofNat 97, Char.ofNat 110, Char.ofNat 100, Char.ofNat 108, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 19, startByte := 119, endByte := 197 }, kind := ValueKind.closure }, { source := { bindingName := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 105, Char.ofNat 110]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 30, startByte := 215, endByte := 226 }, kind := ValueKind.computation }, { source := { bindingName := (String.ofList [Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 11, startByte := 89, endByte := 118 }, kind := ValueKind.closure }, { source := { bindingName := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 105, Char.ofNat 110]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 33, startByte := 223, endByte := 224 }, kind := ValueKind.computation }, { source := { bindingName := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 105, Char.ofNat 110]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 35, startByte := 223, endByte := 224 }, kind := ValueKind.integer (String.ofList [Char.ofNat 55]) }, { source := { bindingName := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 2, startByte := 33, endByte := 88 }, kind := ValueKind.closure }, { source := { bindingName := (String.ofList [Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 13, startByte := 111, endByte := 112 }, kind := ValueKind.computation }, { source := { bindingName := (String.ofList [Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 15, startByte := 111, endByte := 112 }, kind := ValueKind.integer (String.ofList [Char.ofNat 49]) }, { source := { bindingName := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 5, startByte := 52, endByte := 58 }, kind := ValueKind.operation ({ name := (String.ofList [Char.ofNat 116, Char.ofNat 105, Char.ofNat 99, Char.ofNat 107]), familyRealm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), familyPath := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), familyDeclaration := { startByte := 0, endByte := 32, kind := (String.ofList [Char.ofNat 65, Char.ofNat 99, Char.ofNat 116, Char.ofNat 68, Char.ofNat 101, Char.ofNat 99, Char.ofNat 108, Char.ofNat 97, Char.ofNat 114, Char.ofNat 97, Char.ofNat 116, Char.ofNat 105, Char.ofNat 111, Char.ofNat 110]), text := (String.ofList [Char.ofNat 97, Char.ofNat 99, Char.ofNat 116, Char.ofNat 32, Char.ofNat 105, Char.ofNat 111, Char.ofNat 58, Char.ofNat 10, Char.ofNat 32, Char.ofNat 32, Char.ofNat 32, Char.ofNat 32, Char.ofNat 111, Char.ofNat 117, Char.ofNat 114, Char.ofNat 32, Char.ofNat 116, Char.ofNat 105, Char.ofNat 99, Char.ofNat 107, Char.ofNat 58, Char.ofNat 32, Char.ofNat 105, Char.ofNat 110, Char.ofNat 116, Char.ofNat 32, Char.ofNat 45, Char.ofNat 62, Char.ofNat 32, Char.ofNat 105, Char.ofNat 110, Char.ofNat 116]) }, declaration := { startByte := 12, endByte := 32, kind := (String.ofList [Char.ofNat 66, Char.ofNat 105, Char.ofNat 110, Char.ofNat 100, Char.ofNat 105, Char.ofNat 110, Char.ofNat 103, Char.ofNat 83, Char.ofNat 116, Char.ofNat 97, Char.ofNat 116, Char.ofNat 101, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116]), text := (String.ofList [Char.ofNat 111, Char.ofNat 117, Char.ofNat 114, Char.ofNat 32, Char.ofNat 116, Char.ofNat 105, Char.ofNat 99, Char.ofNat 107, Char.ofNat 58, Char.ofNat 32, Char.ofNat 105, Char.ofNat 110, Char.ofNat 116, Char.ofNat 32, Char.ofNat 45, Char.ofNat 62, Char.ofNat 32, Char.ofNat 105, Char.ofNat 110, Char.ofNat 116]) }, namePosition := { startByte := 16, endByte := 20, kind := (String.ofList [Char.ofNat 73, Char.ofNat 100, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116, Char.ofNat 105, Char.ofNat 102, Char.ofNat 105, Char.ofNat 101, Char.ofNat 114, Char.ofNat 80, Char.ofNat 97, Char.ofNat 116, Char.ofNat 116, Char.ofNat 101, Char.ofNat 114, Char.ofNat 110]), text := (String.ofList [Char.ofNat 116, Char.ofNat 105, Char.ofNat 99, Char.ofNat 107]) }, signaturePosition := { startByte := 22, endByte := 32, kind := (String.ofList [Char.ofNat 84, Char.ofNat 121, Char.ofNat 112, Char.ofNat 101, Char.ofNat 69, Char.ofNat 120, Char.ofNat 112, Char.ofNat 114, Char.ofNat 101, Char.ofNat 115, Char.ofNat 115, Char.ofNat 105, Char.ofNat 111, Char.ofNat 110]), text := (String.ofList [Char.ofNat 105, Char.ofNat 110, Char.ofNat 116, Char.ofNat 32, Char.ofNat 45, Char.ofNat 62, Char.ofNat 32, Char.ofNat 105, Char.ofNat 110, Char.ofNat 116]) }, startByte := 12, endByte := 32, visibility := (String.ofList [Char.ofNat 79, Char.ofNat 117, Char.ofNat 114]), signature := AnnotationType.mk (SourceType.function (AnnotationType.mk (SourceType.int) (none)) (AnnotationType.mk (SourceType.int) (none))) (none) }) }, { source := { bindingName := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 4, startByte := 59, endByte := 63 }, kind := ValueKind.computation }, { source := { bindingName := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 4, startByte := 59, endByte := 63 }, kind := ValueKind.computation }, { source := { bindingName := (String.ofList [Char.ofNat 104, Char.ofNat 97, Char.ofNat 110, Char.ofNat 100, Char.ofNat 108, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 20, startByte := 148, endByte := 197 }, kind := ValueKind.closure }, { source := { bindingName := (String.ofList [Char.ofNat 104, Char.ofNat 97, Char.ofNat 110, Char.ofNat 100, Char.ofNat 108, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 22, startByte := 187, endByte := 195 }, kind := ValueKind.computation }, { source := { bindingName := (String.ofList [Char.ofNat 104, Char.ofNat 97, Char.ofNat 110, Char.ofNat 100, Char.ofNat 108, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 25, startByte := 191, endByte := 193 }, kind := ValueKind.computation }, { source := { bindingName := (String.ofList [Char.ofNat 104, Char.ofNat 97, Char.ofNat 110, Char.ofNat 100, Char.ofNat 108, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 27, startByte := 191, endByte := 193 }, kind := ValueKind.integer (String.ofList [Char.ofNat 49, Char.ofNat 48]) }, { source := { bindingName := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 7, startByte := 65, endByte := 86 }, kind := ValueKind.closure }], receivingViews := [{ index := 0, value := 0, image := none, unknown := true, kind := ReceivingViewKind.ordinary }, { index := 1, value := 1, image := none, unknown := true, kind := ReceivingViewKind.ordinary }, { index := 2, value := 1, image := some 0, unknown := true, kind := ReceivingViewKind.rootComp }, { index := 3, value := 2, image := none, unknown := true, kind := ReceivingViewKind.ordinary }, { index := 4, value := 3, image := none, unknown := true, kind := ReceivingViewKind.ordinary }, { index := 5, value := 4, image := none, unknown := false, kind := ReceivingViewKind.ordinary }, { index := 6, value := 5, image := none, unknown := true, kind := ReceivingViewKind.ordinary }, { index := 7, value := 6, image := none, unknown := true, kind := ReceivingViewKind.ordinary }, { index := 8, value := 7, image := none, unknown := false, kind := ReceivingViewKind.ordinary }, { index := 9, value := 8, image := none, unknown := true, kind := ReceivingViewKind.ordinary }, { index := 10, value := 9, image := none, unknown := true, kind := ReceivingViewKind.ordinary }, { index := 11, value := 10, image := none, unknown := true, kind := ReceivingViewKind.ordinary }, { index := 12, value := 11, image := none, unknown := true, kind := ReceivingViewKind.ordinary }, { index := 13, value := 12, image := none, unknown := true, kind := ReceivingViewKind.ordinary }, { index := 14, value := 12, image := some 1, unknown := true, kind := ReceivingViewKind.rootComp }, { index := 15, value := 13, image := none, unknown := true, kind := ReceivingViewKind.ordinary }, { index := 16, value := 14, image := none, unknown := false, kind := ReceivingViewKind.ordinary }, { index := 17, value := 15, image := none, unknown := true, kind := ReceivingViewKind.ordinary }], receivingImageChains := [{ view := 0, links := [] }, { view := 1, links := [] }, { view := 2, links := [{ image := 0, boundary := 0, receiver := 0 }] }, { view := 3, links := [] }, { view := 4, links := [] }, { view := 5, links := [] }, { view := 6, links := [] }, { view := 7, links := [] }, { view := 8, links := [] }, { view := 9, links := [] }, { view := 10, links := [] }, { view := 11, links := [] }, { view := 12, links := [] }, { view := 13, links := [] }, { view := 14, links := [{ image := 1, boundary := 1, receiver := 4 }] }, { view := 15, links := [] }, { view := 16, links := [] }, { view := 17, links := [] }], sourceNameInitialization := some { value := 4, view := 5, interface := Interface.value, dispatch := none }, sourceNameParameter := some 0, receivingScanTruncated := false }
end Current


namespace Make

structure Position where
  startByte : Nat
  endByte : Nat
  kind : String
  text : String

inductive ScopeTag where
  | definition | moduleExpression | sourceMember
  | expression (id : Nat) | parameter (id : Nat) | localInitializer (id : Nat)
  | catchArm (id : Nat) (arm : Position)

structure RootBinding where
  name : String
  realm : String
  path : String
  sameNameOrdinal : Nat

inductive Resolution where
  | moduleDef (name : String) (realm : String) (path : String) (ordinal : Nat)
  | parameter (id : Nat) | local (id : Nat) | catchBinder (id : Nat) | caseBinder (id : Nat)
  | unresolved | ambiguous

structure EffectId where
  realm : String
  path : String
  declaration : Position

structure EffectRow where
  position : Position
  concrete : List EffectId
  variables : List String

mutual
inductive SourceType where
  | unit | int | bool | str | variable (name : String) | hole (position : Position)
  | tuple (items : List AnnotationType) | function (argument result : AnnotationType)

inductive AnnotationType where
  | mk (value : SourceType) (effects : Option EffectRow)

end
structure Annotation where
  owner : String
  position : Position
  type : AnnotationType

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

structure Formal where
  id : Nat
  spelling : String
  startByte : Nat
  endByte : Nat
  sourcePosition : Position
  scope : ScopeTag
  annotation : Option Annotation

inductive BlockStatement where
  | expression (code : Nat) | binding (ordinal localId initializer : Nat)

inductive SourceStatement where
  | expression (source : Nat) | binding (ordinal localId initializer : Nat)

structure SourceStatementBlock where
  statements : List SourceStatement
  finalExpression : Nat

structure InstructionStatementBlock where
  statements : List BlockStatement
  finalExpression : Nat

inductive SourceForm where
  | unit | integer (value : String) | boolean (value : Bool) | string (value : String)
  | decodedString (value : String) | name (spelling : String) (resolution : Resolution)
  | apply (syntaxKind : String) (callee argument : Nat) | group (inner : Nat)
  | ascription (annotation : Annotation) (inner : Nat) | lambda (formal : Formal) (body : Nat)
  | operation (identity : OperationIdentity) | block (bindings : List (Nat × Nat)) (finalExpression : Nat)
  | statementBlock (block : SourceStatementBlock)

inductive Instruction where
  | unit | integer (value : String) | boolean (value : Bool) | string (value : String)
  | decodedString (value : String) | name (resolution : Resolution) (consumption : String)
  | apply (callee argument : Nat) | forward (inner : Nat) | lambda (formalId body : Nat)
  | operation (identity : OperationIdentity) | block (bindings : List (Nat × Nat)) (finalExpression : Nat)
  | statementBlock (block : InstructionStatementBlock)

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

end Make

namespace Binding
structure BindingUsePublication where
  makeRoot : Make.RootBinding
  makeDefinitionRoot : Current.SourceRootIdentity
  declaration : Current.Position
  bindingAnnotation : Option Current.Annotation
  hirVisibility : String
  sourceIndexPublic : Bool
  initializer : Nat
  useSite : Current.RuntimeSite
  useOwner : Current.ExecutionOwner
  useStep : Nat
  useEnvironment : Nat
  useScope : Current.ScopeTag
  resolution : Current.Resolution
  consumes : String
  globalCell : Nat
  cellValue : Nat
  cellView : Nat
  cellInterface : Current.Interface
  providerSite : Current.RuntimeSite
  providerFormal : Nat
  providerBody : Nat
  providerEnvironment : Nat
  providerEnvironmentParent : Option Nat
  providerInterfaceIsValue : Bool
  useEnvironmentParent : Option Nat
  useEnvironmentBinderKind : Option String
  useEnvironmentBinderId : Option Nat
  useEnvironmentBinderCell : Option Nat
  useEnvironmentBinderOwner : Option Current.SourceRootIdentity
  dispatchBase : Option Nat
  dispatchWord : Option Nat
  substitution : Option Nat
  runId : Nat

structure ModuleBindingRow where
  name : String
  realm : String
  path : String
  sameNameOrdinal : Nat
  definitionRoot : Current.SourceRootIdentity
  declaration : Current.Position
  bindingAnnotation : Option Current.Annotation
  hirVisibility : String
  sourceIndexPublic : Bool
  runtimeCell : Nat

def moduleBindingsInSourceOrder : List ModuleBindingRow := [{ name := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, definitionRoot := Current.SourceRootIdentity.definition (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101]) (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]) (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]) 0, declaration := { startByte := 33, endByte := 88, kind := (String.ofList [Char.ofNat 66, Char.ofNat 105, Char.ofNat 110, Char.ofNat 100, Char.ofNat 105, Char.ofNat 110, Char.ofNat 103, Char.ofNat 83, Char.ofNat 116, Char.ofNat 97, Char.ofNat 116, Char.ofNat 101, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116]), text := (String.ofList [Char.ofNat 109, Char.ofNat 121, Char.ofNat 32, Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101, Char.ofNat 32, Char.ofNat 115, Char.ofNat 101, Char.ofNat 101, Char.ofNat 100, Char.ofNat 32, Char.ofNat 61, Char.ofNat 32, Char.ofNat 123, Char.ofNat 32, Char.ofNat 105, Char.ofNat 111, Char.ofNat 58, Char.ofNat 58, Char.ofNat 116, Char.ofNat 105, Char.ofNat 99, Char.ofNat 107, Char.ofNat 32, Char.ofNat 115, Char.ofNat 101, Char.ofNat 101, Char.ofNat 100, Char.ofNat 59, Char.ofNat 32, Char.ofNat 92, Char.ofNat 97, Char.ofNat 114, Char.ofNat 103, Char.ofNat 117, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116, Char.ofNat 32, Char.ofNat 45, Char.ofNat 62, Char.ofNat 32, Char.ofNat 97, Char.ofNat 114, Char.ofNat 103, Char.ofNat 117, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116, Char.ofNat 32, Char.ofNat 125]) }, bindingAnnotation := none, hirVisibility := (String.ofList [Char.ofNat 80, Char.ofNat 114, Char.ofNat 105, Char.ofNat 118, Char.ofNat 97, Char.ofNat 116, Char.ofNat 101]), sourceIndexPublic := false, runtimeCell := 0 }, { name := (String.ofList [Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, definitionRoot := Current.SourceRootIdentity.definition (String.ofList [Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121]) (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]) (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]) 0, declaration := { startByte := 89, endByte := 118, kind := (String.ofList [Char.ofNat 66, Char.ofNat 105, Char.ofNat 110, Char.ofNat 100, Char.ofNat 105, Char.ofNat 110, Char.ofNat 103, Char.ofNat 83, Char.ofNat 116, Char.ofNat 97, Char.ofNat 116, Char.ofNat 101, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116]), text := (String.ofList [Char.ofNat 109, Char.ofNat 121, Char.ofNat 32, Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121, Char.ofNat 32, Char.ofNat 118, Char.ofNat 97, Char.ofNat 108, Char.ofNat 117, Char.ofNat 101, Char.ofNat 32, Char.ofNat 61, Char.ofNat 32, Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101, Char.ofNat 32, Char.ofNat 49, Char.ofNat 32, Char.ofNat 118, Char.ofNat 97, Char.ofNat 108, Char.ofNat 117, Char.ofNat 101]) }, bindingAnnotation := none, hirVisibility := (String.ofList [Char.ofNat 80, Char.ofNat 114, Char.ofNat 105, Char.ofNat 118, Char.ofNat 97, Char.ofNat 116, Char.ofNat 101]), sourceIndexPublic := false, runtimeCell := 1 }, { name := (String.ofList [Char.ofNat 104, Char.ofNat 97, Char.ofNat 110, Char.ofNat 100, Char.ofNat 108, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, definitionRoot := Current.SourceRootIdentity.definition (String.ofList [Char.ofNat 104, Char.ofNat 97, Char.ofNat 110, Char.ofNat 100, Char.ofNat 108, Char.ofNat 101]) (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]) (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]) 0, declaration := { startByte := 119, endByte := 197, kind := (String.ofList [Char.ofNat 66, Char.ofNat 105, Char.ofNat 110, Char.ofNat 100, Char.ofNat 105, Char.ofNat 110, Char.ofNat 103, Char.ofNat 83, Char.ofNat 116, Char.ofNat 97, Char.ofNat 116, Char.ofNat 101, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116]), text := (String.ofList [Char.ofNat 109, Char.ofNat 121, Char.ofNat 32, Char.ofNat 104, Char.ofNat 97, Char.ofNat 110, Char.ofNat 100, Char.ofNat 108, Char.ofNat 101, Char.ofNat 32, Char.ofNat 40, Char.ofNat 116, Char.ofNat 104, Char.ofNat 117, Char.ofNat 110, Char.ofNat 107, Char.ofNat 58, Char.ofNat 91, Char.ofNat 105, Char.ofNat 111, Char.ofNat 93, Char.ofNat 32, Char.ofNat 105, Char.ofNat 110, Char.ofNat 116, Char.ofNat 41, Char.ofNat 32, Char.ofNat 61, Char.ofNat 32, Char.ofNat 99, Char.ofNat 97, Char.ofNat 116, Char.ofNat 99, Char.ofNat 104, Char.ofNat 32, Char.ofNat 116, Char.ofNat 104, Char.ofNat 117, Char.ofNat 110, Char.ofNat 107, Char.ofNat 32, Char.ofNat 123, Char.ofNat 32, Char.ofNat 105, Char.ofNat 111, Char.ofNat 58, Char.ofNat 58, Char.ofNat 116, Char.ofNat 105, Char.ofNat 99, Char.ofNat 107, Char.ofNat 40, Char.ofNat 112, Char.ofNat 41, Char.ofNat 44, Char.ofNat 32, Char.ofNat 107, Char.ofNat 32, Char.ofNat 45, Char.ofNat 62, Char.ofNat 32, Char.ofNat 104, Char.ofNat 97, Char.ofNat 110, Char.ofNat 100, Char.ofNat 108, Char.ofNat 101, Char.ofNat 32, Char.ofNat 123, Char.ofNat 32, Char.ofNat 107, Char.ofNat 32, Char.ofNat 49, Char.ofNat 48, Char.ofNat 32, Char.ofNat 125, Char.ofNat 32, Char.ofNat 125]) }, bindingAnnotation := none, hirVisibility := (String.ofList [Char.ofNat 80, Char.ofNat 114, Char.ofNat 105, Char.ofNat 118, Char.ofNat 97, Char.ofNat 116, Char.ofNat 101]), sourceIndexPublic := false, runtimeCell := 2 }, { name := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 105, Char.ofNat 110]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, definitionRoot := Current.SourceRootIdentity.definition (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 105, Char.ofNat 110]) (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]) (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]) 0, declaration := { startByte := 198, endByte := 226, kind := (String.ofList [Char.ofNat 66, Char.ofNat 105, Char.ofNat 110, Char.ofNat 100, Char.ofNat 105, Char.ofNat 110, Char.ofNat 103, Char.ofNat 83, Char.ofNat 116, Char.ofNat 97, Char.ofNat 116, Char.ofNat 101, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116]), text := (String.ofList [Char.ofNat 109, Char.ofNat 121, Char.ofNat 32, Char.ofNat 109, Char.ofNat 97, Char.ofNat 105, Char.ofNat 110, Char.ofNat 32, Char.ofNat 61, Char.ofNat 32, Char.ofNat 104, Char.ofNat 97, Char.ofNat 110, Char.ofNat 100, Char.ofNat 108, Char.ofNat 101, Char.ofNat 32, Char.ofNat 123, Char.ofNat 32, Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121, Char.ofNat 32, Char.ofNat 55, Char.ofNat 32, Char.ofNat 125]) }, bindingAnnotation := none, hirVisibility := (String.ofList [Char.ofNat 80, Char.ofNat 114, Char.ofNat 105, Char.ofNat 118, Char.ofNat 97, Char.ofNat 116, Char.ofNat 101]), sourceIndexPublic := false, runtimeCell := 3 }]
def makeBindingUse : BindingUsePublication := { makeRoot := Make.rootBinding, makeDefinitionRoot := Current.SourceRootIdentity.definition (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101]) (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]) (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]) 0, declaration := { startByte := 33, endByte := 88, kind := (String.ofList [Char.ofNat 66, Char.ofNat 105, Char.ofNat 110, Char.ofNat 100, Char.ofNat 105, Char.ofNat 110, Char.ofNat 103, Char.ofNat 83, Char.ofNat 116, Char.ofNat 97, Char.ofNat 116, Char.ofNat 101, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116]), text := (String.ofList [Char.ofNat 109, Char.ofNat 121, Char.ofNat 32, Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101, Char.ofNat 32, Char.ofNat 115, Char.ofNat 101, Char.ofNat 101, Char.ofNat 100, Char.ofNat 32, Char.ofNat 61, Char.ofNat 32, Char.ofNat 123, Char.ofNat 32, Char.ofNat 105, Char.ofNat 111, Char.ofNat 58, Char.ofNat 58, Char.ofNat 116, Char.ofNat 105, Char.ofNat 99, Char.ofNat 107, Char.ofNat 32, Char.ofNat 115, Char.ofNat 101, Char.ofNat 101, Char.ofNat 100, Char.ofNat 59, Char.ofNat 32, Char.ofNat 92, Char.ofNat 97, Char.ofNat 114, Char.ofNat 103, Char.ofNat 117, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116, Char.ofNat 32, Char.ofNat 45, Char.ofNat 62, Char.ofNat 32, Char.ofNat 97, Char.ofNat 114, Char.ofNat 103, Char.ofNat 117, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 116, Char.ofNat 32, Char.ofNat 125]) }, bindingAnnotation := none, hirVisibility := (String.ofList [Char.ofNat 80, Char.ofNat 114, Char.ofNat 105, Char.ofNat 118, Char.ofNat 97, Char.ofNat 116, Char.ofNat 101]), sourceIndexPublic := false, initializer := 0, useSite := { bindingName := (String.ofList [Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 14, startByte := 106, endByte := 110 }, useOwner := Current.ExecutionOwner.invocation 1, useStep := 18, useEnvironment := 2, useScope := Current.ScopeTag.parameter 0, resolution := Current.Resolution.moduleDef (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101]) (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]) (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]) 0, consumes := (String.ofList [Char.ofNat 79, Char.ofNat 98, Char.ofNat 115, Char.ofNat 101, Char.ofNat 114, Char.ofNat 118, Char.ofNat 101]), globalCell := 0, cellValue := 5, cellView := 6, cellInterface := Current.Interface.value, providerSite := { bindingName := (String.ofList [Char.ofNat 109, Char.ofNat 97, Char.ofNat 107, Char.ofNat 101]), realm := (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]), path := (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]), sameNameOrdinal := 0, occurrence := 2, startByte := 33, endByte := 88 }, providerFormal := 0, providerBody := 1, providerEnvironment := 0, providerEnvironmentParent := none, providerInterfaceIsValue := true, useEnvironmentParent := some 0, useEnvironmentBinderKind := some (String.ofList [Char.ofNat 112, Char.ofNat 97, Char.ofNat 114, Char.ofNat 97, Char.ofNat 109, Char.ofNat 101, Char.ofNat 116, Char.ofNat 101, Char.ofNat 114]), useEnvironmentBinderId := some 0, useEnvironmentBinderCell := some 5, useEnvironmentBinderOwner := some (Current.SourceRootIdentity.definition (String.ofList [Char.ofNat 114, Char.ofNat 101, Char.ofNat 108, Char.ofNat 97, Char.ofNat 121]) (String.ofList [Char.ofNat 114, Char.ofNat 51, Char.ofNat 49, Char.ofNat 50, Char.ofNat 45, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 101, Char.ofNat 112, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100]) (String.ofList [Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 108, Char.ofNat 101, Char.ofNat 101, Char.ofNat 45, Char.ofNat 104, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 121, Char.ofNat 46, Char.ofNat 121, Char.ofNat 117]) 0), dispatchBase := none, dispatchWord := none, substitution := none, runId := 135158189492808 }
end Binding

end YulangClosure.OriginalModuleContextBindingR315.Native
-- END authenticated native payload

namespace YulangClosure.OriginalModuleContextBindingR315

open OriginalSource OriginalScopedClosure OriginalSourceInterpretation
open OriginalSourceEnvironment OriginalSourceChecking
open OriginalScopedSourceEventMapR314 OriginalSourceContractResolutionR311

/-- A published Name retains its ORIGINAL instance binder and all three
original atoms at the SAME extension, for an arbitrary original kernel.
This is an exact source-rule equation, not a proof of those obligations. -/
theorem published_name_iff {Value : Type} (kernel : Kernel Value)
    (environment : Environment Value) (context : Context)
    (site : Site) (name : Name) (binding : Binding)
    (resolved : lookupBinding context name = some binding)
    (published : binding.kind = .published) :
    SourceJudgment kernel environment context (.name ⟨site, none⟩ name) ↔
      ∃ candidate, kernel.admitted environment ⟨site, .publishedInstance, 0⟩ candidate ∧
        let after := environment.extend ⟨site, .publishedInstance, 0⟩ candidate
        kernel.atom after {(atom .exactWholeInstance site context) with
          names := [name], binding := some binding} ∧
        kernel.atom after {(atom .resolvedSameBinding site context) with
          names := [name], binding := some binding} ∧
        kernel.atom after {(atom .computedFetchOnce site context) with
          names := [name], binding := some binding} := by
  simp only [SourceJudgment, sourceRules, resolved, Option.map_some, published]
  constructor
  · intro proof
    cases proof with
    | existsE candidate admitted proof =>
      cases proof with
      | rule instanceProof children =>
        cases children with
        | cons nameProof rest =>
          cases nameProof with
          | rule nameProof noChildren =>
            have first := instanceProof _ (List.mem_cons_self ..)
            have second := nameProof _ (List.mem_cons_self ..)
            have third := nameProof _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
            cases first with
            | atom first =>
              cases second with
              | atom second =>
                cases third with
                | atom third => exact ⟨candidate, admitted, first, second, third⟩
  · rintro ⟨candidate, admitted, first, second, third⟩
    apply Judgment.existsE candidate admitted
    apply Judgment.rule
    · intro premise member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      subst premise
      exact .atom first
    · apply Judgments.cons
      · apply Judgment.rule
        · intro premise member
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl
          · exact .atom second
          · exact .atom third
        · exact .nil
      · exact .nil

/-- The original Context projection depends only on the authenticated binding
header. The initializer remains arbitrary; no invented replacement body is used. -/
theorem binding_header_context (site : Site) (name : Name)
    (annotation : Option OriginalSource.Annotation) (initializer : Source .expression) :
    (Source.binding site name annotation initializer .bindingsNil).bindingRecords =
      [{name := name, owner := site, kind := .published}] := rfl

/-- The R314 selected occurrence is now connected to the imported, original
R297 inventory in this module; both original operands and all scopes remain. -/
theorem selected_inventory_row (origin : Declaration) (context : Context) :
    ((SourceGraphRegistrationR297.sourceInventory origin context
      OriginalScopedSourceEventMapR314.Fixture.root)[12]?).map
      SourceGraphRegistrationR297.Row.program =
      some (allocate (OriginalScopedSourceEventMapR314.Fixture.position origin)
        (sourceRules (OriginalScopedSourceEventMapR314.Fixture.localContext context)
          OriginalScopedSourceEventMapR314.Fixture.selected)) := by
  run_tac Lean.Meta.withTransparency .all <| Lean.Elab.Tactic.evalTactic (← `(tactic| rfl))

/-- Apply the existing R311 source-resolution consumer to every request in
the SAME R314 root. This does not supply its semantic formation leaves. -/
theorem requests_located (origin : Declaration) (context : Context) :
    ∀ request ∈ ComputedCallTypedFormationR310.requests origin context
      OriginalScopedSourceEventMapR314.Fixture.root,
      ∃ (index : Nat) (row : SourceGraphRegistrationR297.Row),
        (SourceGraphRegistrationR297.sourceInventory origin context
          OriginalScopedSourceEventMapR314.Fixture.root)[index]? = some row ∧
        ComputedCallTypedFormationR310.callRecord row = some request.original ∧
        ComputedCallTypedFormationR310.prepare request.original = request :=
  fun request member => request_source_row origin context
    OriginalScopedSourceEventMapR314.Fixture.root request member

/-- The exact outer call, retaining its own ViewLogic scope below the seven
R314 enclosing scopes. Its callee remains an App, not a Name substitute. -/
def selectedCall (origin : Declaration) (context : Context) :
    ComputedCallTypedFormationR310.CallRecord :=
  let original := OriginalSourceCalleeWitnessR313.originalCall
    (OriginalScopedSourceEventMapR314.Fixture.position origin)
    (OriginalScopedSourceEventMapR314.Fixture.localContext context) ⟨1, none⟩
    OriginalScopedSourceEventMapR314.Fixture.callee
    OriginalScopedSourceEventMapR314.Fixture.argument
  ⟨original.position, original.site, original.context, original.premises,
    original.callee, original.argument, 2, 3⟩

theorem selected_request_computed (origin : Declaration) (context : Context) :
    ((SourceGraphRegistrationR297.sourceInventory origin context
      OriginalScopedSourceEventMapR314.Fixture.root)[13]?).bind
      ComputedCallTypedFormationR310.callRecord = some (selectedCall origin context) := by
  run_tac Lean.Meta.withTransparency .all <| Lean.Elab.Tactic.evalTactic (← `(tactic| rfl))

/-- Exact inversion/reconstruction of the computed callee. No child, local
premise or publication instance is dropped. Both extensions remain shared. -/
theorem published_callee_iff {Value : Type} (kernel : Kernel Value)
    (environment : Environment Value) (context : Context) (binding : Binding)
    (resolved : lookupBinding context 8 = some binding)
    (published : binding.kind = .published) :
    SourceJudgment kernel environment context OriginalScopedSourceEventMapR314.Fixture.callee ↔
      ∃ candidate, kernel.admitted environment ⟨2, .viewLogic, 0⟩ candidate ∧
        let after := environment.extend ⟨2, .viewLogic, 0⟩ candidate
        (∀ premise ∈ SourceAppAdmissionR159.appPremises context ⟨2, none⟩
          (.name ⟨4, none⟩ 8) (.literal ⟨5, none⟩ (.int 1)), Local kernel after premise) ∧
        SourceJudgment kernel after context (.literal ⟨5, none⟩ (.int 1)) ∧
        ∃ instanceCandidate,
          kernel.admitted after ⟨4, .publishedInstance, 0⟩ instanceCandidate ∧
          let instanceAfter := after.extend ⟨4, .publishedInstance, 0⟩ instanceCandidate
          kernel.atom instanceAfter {(atom .exactWholeInstance 4 context) with
            names := [8], binding := some binding} ∧
          kernel.atom instanceAfter {(atom .resolvedSameBinding 4 context) with
            names := [8], binding := some binding} ∧
          kernel.atom instanceAfter {(atom .computedFetchOnce 4 context) with
            names := [8], binding := some binding} := by
  change SourceJudgment kernel environment context
    (.app ⟨2, none⟩ (.name ⟨4, none⟩ 8) (.literal ⟨5, none⟩ (.int 1))) ↔ _
  rw [SourceAppAdmissionR159.app_source_iff]
  constructor
  · rintro ⟨_, candidate, admitted, body⟩
    obtain ⟨locals, nameProof, argumentProof⟩ :=
      (SourceAppAdmissionR159.app_continuation_iff kernel _ _ _ _ _).mp body
    exact ⟨candidate, admitted, locals, argumentProof,
      (published_name_iff kernel _ context 4 8 binding resolved published).mp nameProof⟩
  · rintro ⟨candidate, admitted, locals, argumentProof, instanceProof⟩
    refine ⟨?_, candidate, admitted, ?_⟩
    · intro premise member
      cases member
    · apply (SourceAppAdmissionR159.app_continuation_iff kernel _ _ _ _ _).mpr
      exact ⟨locals,
        (published_name_iff kernel _ context 4 8 binding resolved published).mpr instanceProof,
        argumentProof⟩

set_option maxRecDepth 4096
set_option maxHeartbeats 600000

abbrev ModuleRow := Native.Binding.ModuleBindingRow
abbrev BindingUse := Native.Binding.BindingUsePublication

def rowResolution (row : ModuleRow) : R314Artifact.Resolution :=
  .moduleDef row.name row.realm row.path row.sameNameOrdinal

def sameRoot (root : Native.Current.SourceRootIdentity) (name realm path : String)
    (ordinal : Nat) : Bool :=
  match root with
  | .definition n r p o => n == name && r == realm && p == path && o == ordinal
  | _ => false

def rowMatches (row : ModuleRow) (name realm path : String) (ordinal : Nat) : Bool :=
  row.name == name && row.realm == realm && row.path == path && row.sameNameOrdinal == ordinal &&
  sameRoot row.definitionRoot name realm path ordinal

/-- Full DefId identity is interned through the frozen R314 source references.
Unreferenced module names use disjoint, source-table coordinates. -/
def nameFor (row : ModuleRow) : Name :=
  let index := R314Artifact.nodes.findIdx (fun node => match node.form with
    | .name _ resolution => sameResolution resolution (rowResolution row)
    | _ => false)
  2 * (if index < R314Artifact.nodes.length then index else R314Artifact.nodes.length + row.runtimeCell)

def headerBinding (row : ModuleRow) : OriginalSource.Binding :=
  {name := nameFor row, owner := row.declaration.startByte, kind := .published}

def consumerIndex : Nat := Native.Binding.moduleBindingsInSourceOrder.findIdx (fun row =>
  rowMatches row Native.Current.rootBinding.name Native.Current.rootBinding.realm
    Native.Current.rootBinding.path Native.Current.rootBinding.sameNameOrdinal)

/-- The complete ordered predecessor binding prefix of this source declaration.
Operation families remain in the independent primitive declaration table. -/
def externalContext : Context :=
  (Native.Binding.moduleBindingsInSourceOrder.take consumerIndex).map headerBinding

def makeRow : ModuleRow := Native.Binding.moduleBindingsInSourceOrder[0]'(by decide)
def makeBinding : OriginalSource.Binding := headerBinding makeRow

theorem make_row_resolved : Native.Binding.moduleBindingsInSourceOrder.find? (fun row =>
    rowMatches row Native.Binding.makeBindingUse.makeRoot.name
      Native.Binding.makeBindingUse.makeRoot.realm Native.Binding.makeBindingUse.makeRoot.path
      Native.Binding.makeBindingUse.makeRoot.sameNameOrdinal) = some makeRow := by rfl

theorem context_computed : consumerIndex = 1 ∧ externalContext = [makeBinding] ∧
    makeBinding = {name := 8, owner := 33, kind := .published} := by exact ⟨rfl, rfl, rfl⟩

theorem actual_make_lookup : lookupBinding
    (OriginalScopedSourceEventMapR314.Fixture.localContext externalContext) 8 = some makeBinding := by
  rw [context_computed.2.1, context_computed.2.2]
  rfl

def makeAnnotation : Option OriginalSource.Annotation :=
  Native.Binding.makeBindingUse.bindingAnnotation.map (fun annotation => annotation.position.startByte)

def makeFormal (formal : Native.Make.Formal) : OriginalSource.Formal :=
  ⟨formal.startByte, 2 * formal.id + 1,
    formal.annotation.map (fun annotation => annotation.position.startByte),
    match formal.annotation with
    | none => false
    | some annotation => match annotation.type with | .mk _ effects => effects.isSome⟩

mutual
/-- Finite constructor adapter for the actual make initializer. Unsupported
local-binding blocks fail closed; the represented statement block keeps its
ordered discarded expression, operation identity and final lambda. -/
def decodeMake : Nat → Nat → Option (Source .expression)
  | 0, _ => none
  | fuel + 1, index => do
    let node ← Native.Make.nodes.find? (fun node => node.ordinal == index)
    let mark : Mark := ⟨node.ordinal, none⟩
    match node.form with
    | .unit => pure (.literal mark .unit)
    | .integer text => pure (.literal mark (.int (← decimalInt text)))
    | .boolean value => pure (.literal mark (.bool value))
    | .string value | .decodedString value => pure (.literal mark (.string value))
    | .name _ (.parameter id) => pure (.name mark (2 * id + 1))
    | .apply _ callee argument => pure (.app mark (← decodeMake fuel callee) (← decodeMake fuel argument))
    | .group inner => decodeMake fuel inner
    | .ascription annotation inner => withAnnotation (← decodeMake fuel inner) annotation.position.startByte
    | .lambda formal body => pure (.lambda mark (makeFormal formal)
        (.varPattern formal.startByte (2 * formal.id + 1)) (← decodeMake fuel body))
    | .operation identity => pure (.primitive mark identity.declaration.startByte)
    | .statementBlock block => pure (.block mark (← decodeMakeStatements fuel block.statements)
        (← decodeMake fuel block.finalExpression))
    | _ => none

def decodeMakeStatements : Nat → List Native.Make.SourceStatement → Option (Source .statements)
  | 0, _ => none
  | _ + 1, [] => some .statementsNil
  | fuel + 1, .expression expression :: rest => do
      pure (.statementsCons (.expressionS expression (← decodeMake fuel expression))
        (← decodeMakeStatements fuel rest))
  | _ + 1, .binding .. :: _ => none
end

/-- Compact normal form, validated against the independently exported tree. -/
def makeInitializer : Source .expression :=
  .lambda ⟨0, none⟩ ⟨41, 1, none, false⟩ (.varPattern 41 1)
    (.block ⟨1, none⟩
      (.statementsCons (.expressionS 3
        (.app ⟨3, none⟩ (.primitive ⟨4, none⟩ 12) (.name ⟨5, none⟩ 1))) .statementsNil)
      (.lambda ⟨2, none⟩ ⟨66, 3, none, false⟩ (.varPattern 66 3) (.name ⟨6, none⟩ 3)))

theorem make_initializer_decoded : decodeMake 16 Native.Make.rootInitializer = some makeInitializer := by rfl

def makeSource : Source .bindings :=
  .binding makeBinding.owner makeBinding.name makeAnnotation makeInitializer .bindingsNil

theorem source_context_computed : makeSource.bindingRecords = externalContext := by
  rw [context_computed.2.1]
  rfl

/-- Original publication is internal SG publication, independent of native
public export visibility. The initializer's actual final root is retained. -/
theorem publication_computed (origin : Declaration) :
    ((source origin [] makeSource).publications.map (fun publication =>
      (publication.name, publication.clause.site, publication.endpoint))) =
      [(8, 33, (⟨0, .finalRoot⟩ : Endpoint))] := by
  run_tac Lean.Meta.withTransparency .all <| Lean.Elab.Tactic.evalTactic (← `(tactic| rfl))

/-- Read the same installed original publication, conditional on its genuine
fixed-map equations. Those equations are not synthesized from native IDs. -/
theorem publication_readback {s : Sorts} {View : Type}
    (readout : RuntimeReadout s View) (environment : Environment (Payload s View))
    (root : Root s View) (identity : PublicationId (Payload s View))
    (record : PublicationRecord (Payload s View))
    (rootFound : environment.root = .root root)
    (named : environment.publicationName makeBinding.name = some identity)
    (stored : environment.publications identity = some record) :
    published environment makeBinding.name = some (publicationData root record) ∧
    (publicationData root record).entry =
      (record.entryFrames.foldl (decodeFrame readout) root.decoded).actual ∧
    (publicationData root record).completed =
      (record.fixedFrames.foldl (decodeFrame readout) root.decoded).actual ∧
    (publicationData root record).captures = record.captures := by
  refine ⟨?_, publication_data_matches_fold readout root record⟩
  simp only [published, rootFound, named, stored, Option.bind_eq_bind,
    Option.bind_some, Option.pure_def]

/-- Apply the actual computed Context to the original source/code consumer. -/
def sourceApply (origin : Declaration) (otherCode : Nat → Option OriginalSourceCalleeWitnessR313.Code) :=
  OriginalScopedSourceEventMapR314.Fixture.sourceApply origin externalContext otherCode

theorem binding_enters_consumer (origin : Declaration)
    (otherCode : Nat → Option OriginalSourceCalleeWitnessR313.Code) :
    (sourceApply origin otherCode).rootContext = externalContext ∧
    lookupBinding (sourceApply origin otherCode).context 8 = some makeBinding ∧
    ((SourceGraphRegistrationR297.sourceInventory origin externalContext
      OriginalScopedSourceEventMapR314.Fixture.root)[13]?).bind
      ComputedCallTypedFormationR310.callRecord = some (selectedCall origin externalContext) := by
  exact ⟨rfl, actual_make_lookup, selected_request_computed origin externalContext⟩

theorem actual_callee_iff {Value : Type} (kernel : Kernel Value) (environment : Environment Value) :
    SourceJudgment kernel environment (OriginalScopedSourceEventMapR314.Fixture.localContext externalContext) OriginalScopedSourceEventMapR314.Fixture.callee ↔
      ∃ candidate, kernel.admitted environment ⟨2, .viewLogic, 0⟩ candidate ∧
        let after := environment.extend ⟨2, .viewLogic, 0⟩ candidate
        (∀ premise ∈ SourceAppAdmissionR159.appPremises (OriginalScopedSourceEventMapR314.Fixture.localContext externalContext) ⟨2, none⟩
          (.name ⟨4, none⟩ 8) (.literal ⟨5, none⟩ (.int 1)), Local kernel after premise) ∧
        SourceJudgment kernel after (OriginalScopedSourceEventMapR314.Fixture.localContext externalContext) (.literal ⟨5, none⟩ (.int 1)) ∧
        ∃ instanceCandidate,
          kernel.admitted after ⟨4, .publishedInstance, 0⟩ instanceCandidate ∧
          let instanceAfter := after.extend ⟨4, .publishedInstance, 0⟩ instanceCandidate
          kernel.atom instanceAfter {(atom .exactWholeInstance 4 (OriginalScopedSourceEventMapR314.Fixture.localContext externalContext)) with
            names := [8], binding := some makeBinding} ∧
          kernel.atom instanceAfter {(atom .resolvedSameBinding 4 (OriginalScopedSourceEventMapR314.Fixture.localContext externalContext)) with
            names := [8], binding := some makeBinding} ∧
          kernel.atom instanceAfter {(atom .computedFetchOnce 4 (OriginalScopedSourceEventMapR314.Fixture.localContext externalContext)) with
            names := [8], binding := some makeBinding} :=
  published_callee_iff kernel environment
    (OriginalScopedSourceEventMapR314.Fixture.localContext externalContext) makeBinding actual_make_lookup rfl

def sameSite (left right : Native.Current.RuntimeSite) : Bool :=
  left.bindingName == right.bindingName && left.realm == right.realm && left.path == right.path &&
  left.sameNameOrdinal == right.sameNameOrdinal && left.occurrence == right.occurrence &&
  left.startByte == right.startByte && left.endByte == right.endByte

def sameCurrentResolution : Native.Current.Resolution → Native.Current.Resolution → Bool
  | .moduleDef n r p o, .moduleDef n' r' p' o' => n == n' && r == r' && p == p' && o == o'
  | .parameter a, .parameter b | .local a, .local b | .catchBinder a, .catchBinder b
  | .caseBinder a, .caseBinder b => a == b
  | .unresolved, .unresolved | .ambiguous, .ambiguous => true
  | _, _ => false

def isValue : Native.Current.Interface → Bool | .value => true | _ => false

def useScope (scope : Native.Current.ScopeTag) : Option Nat :=
  match scope with | .parameter id => some id | _ => none

def providerAgrees (candidate : BindingUse) : Bool :=
  match Native.Make.nodes.find? (fun node => node.occurrence == candidate.providerSite.occurrence) with
  | none => false
  | some node => match node.form, node.instruction with
    | .lambda formal body, .lambda nativeFormal nativeBody =>
      match Native.Make.nodes.find? (fun child => child.ordinal == body) with
      | none => false
      | some child => formal.id == candidate.providerFormal && nativeFormal == formal.id &&
        candidate.providerBody == child.codeLabel && nativeBody == child.codeLabel &&
        formal.annotation.isNone && candidate.providerInterfaceIsValue &&
        node.startByte == candidate.providerSite.startByte && node.endByte == candidate.providerSite.endByte &&
        candidate.providerSite.bindingName == candidate.makeRoot.name &&
        candidate.providerSite.realm == candidate.makeRoot.realm &&
        candidate.providerSite.path == candidate.makeRoot.path &&
        candidate.providerSite.sameNameOrdinal == candidate.makeRoot.sameNameOrdinal
    | _, _ => false

def lookupAgrees (candidate : BindingUse) : Bool :=
  match Native.Current.nodes.find? (fun node => node.occurrence == candidate.useSite.occurrence) with
  | none => false
  | some node => match node.form, node.instruction with
    | .name _ resolution, .name nativeResolution consumption =>
      sameCurrentResolution resolution candidate.resolution &&
      sameCurrentResolution resolution nativeResolution && consumption == candidate.consumes &&
      candidate.consumes == "Observe" &&
      node.startByte == candidate.useSite.startByte && node.endByte == candidate.useSite.endByte &&
      useScope node.scope == useScope candidate.useScope && (useScope candidate.useScope).isSome &&
      candidate.useSite.bindingName == Native.Current.rootBinding.name &&
      candidate.useSite.realm == Native.Current.rootBinding.realm &&
      candidate.useSite.path == Native.Current.rootBinding.path &&
      candidate.useSite.sameNameOrdinal == Native.Current.rootBinding.sameNameOrdinal
    | _, _ => false

def snapshotAgrees (candidate : BindingUse) : Bool :=
  match Native.Current.returnSnapshot.cells[candidate.globalCell]?,
      Native.Current.returnSnapshot.environments[candidate.useEnvironment]?,
      Native.Current.returnSnapshot.environments[candidate.providerEnvironment]? with
  | some cell, some environment, some providerEnvironment =>
    match cell.value with
    | none => false
    | some received => match Native.Current.returnSnapshot.values[received.value]? with
      | none => false
      | some value => received.value == candidate.cellValue && received.view == candidate.cellView &&
        isValue received.interface && isValue candidate.cellInterface &&
        (match value.kind with | .closure => true | _ => false) &&
        sameSite value.source candidate.providerSite &&
        environment.parent == candidate.useEnvironmentParent &&
        environment.binderKind == candidate.useEnvironmentBinderKind &&
        environment.binderId == candidate.useEnvironmentBinderId &&
        environment.binderCell == candidate.useEnvironmentBinderCell &&
        environment.binderKind == some "parameter" && environment.binderId == useScope candidate.useScope &&
        (match environment.binderOwner, candidate.useEnvironmentBinderOwner with
          | some owner, some candidateOwner =>
              sameRoot owner Native.Current.rootBinding.name Native.Current.rootBinding.realm
                Native.Current.rootBinding.path Native.Current.rootBinding.sameNameOrdinal &&
              sameRoot candidateOwner Native.Current.rootBinding.name Native.Current.rootBinding.realm
                Native.Current.rootBinding.path Native.Current.rootBinding.sameNameOrdinal
          | _, _ => false) &&
        environment.dispatchBase == candidate.dispatchBase && environment.dispatchWord == candidate.dispatchWord &&
        environment.substitution == candidate.substitution &&
        providerEnvironment.parent == candidate.providerEnvironmentParent
  | _, _, _ => false

/-- Finite consistency joins, not authentication of arbitrary Rust objects or
an original event interpretation. The exporter owns live identity checks. -/
def accepts (candidate : BindingUse) : Bool :=
  candidate.runId == Native.Current.runId && candidate.runId == Native.Current.returnSnapshot.runId &&
  Native.Current.sourceText == Native.Make.sourceText && Native.Current.sourceText == R314Artifact.sourceText &&
  Native.Binding.moduleBindingsInSourceOrder.all (fun row =>
    row.realm == Native.Current.rootBinding.realm && row.path == Native.Current.rootBinding.path) &&
  (Native.Binding.moduleBindingsInSourceOrder.map (fun row => row.name)).eraseDups.length ==
    Native.Binding.moduleBindingsInSourceOrder.length &&
  match Native.Binding.moduleBindingsInSourceOrder.find? (fun row =>
      rowMatches row candidate.makeRoot.name candidate.makeRoot.realm candidate.makeRoot.path
        candidate.makeRoot.sameNameOrdinal) with
  | none => false
  | some row =>
    sameRoot candidate.makeDefinitionRoot row.name row.realm row.path row.sameNameOrdinal &&
    candidate.declaration.startByte == row.declaration.startByte &&
    candidate.declaration.endByte == row.declaration.endByte &&
    candidate.declaration.kind == row.declaration.kind && candidate.declaration.text == row.declaration.text &&
    candidate.bindingAnnotation.isNone && row.bindingAnnotation.isNone &&
    candidate.sourceIndexPublic == row.sourceIndexPublic && candidate.hirVisibility == row.hirVisibility &&
    candidate.globalCell == row.runtimeCell && row.declaration.endByte < candidate.useSite.startByte &&
    (Native.Binding.moduleBindingsInSourceOrder.findIdx (fun other =>
      rowMatches other row.name row.realm row.path row.sameNameOrdinal)) < consumerIndex &&
    (match candidate.resolution with
      | .moduleDef name realm path ordinal => rowMatches row name realm path ordinal
      | _ => false) &&
    candidate.makeRoot.name == Native.Make.rootBinding.name &&
    candidate.makeRoot.realm == Native.Make.rootBinding.realm &&
    candidate.makeRoot.path == Native.Make.rootBinding.path &&
    candidate.makeRoot.sameNameOrdinal == Native.Make.rootBinding.sameNameOrdinal &&
    candidate.initializer == Native.Make.rootInitializer &&
    providerAgrees candidate && lookupAgrees candidate && snapshotAgrees candidate

theorem actual_binding_accepted : accepts Native.Binding.makeBindingUse = true := by decide +kernel

theorem foreign_defid_rejected : accepts {Native.Binding.makeBindingUse with
    resolution := .moduleDef "foreign" Native.Make.rootBinding.realm Native.Make.rootBinding.path 0} = false := by decide +kernel

theorem foreign_realm_rejected : accepts {Native.Binding.makeBindingUse with
    makeRoot := {Native.Binding.makeBindingUse.makeRoot with realm := "foreign"}} = false := by decide +kernel

theorem wrong_scope_rejected : accepts {Native.Binding.makeBindingUse with useScope := .definition} = false := by decide +kernel

theorem wrong_role_rejected : accepts {Native.Binding.makeBindingUse with providerInterfaceIsValue := false} = false := by decide +kernel

theorem foreign_snapshot_rejected : accepts {Native.Binding.makeBindingUse with runId := 0} = false := by decide +kernel

theorem private_is_preserved : Native.Binding.makeBindingUse.sourceIndexPublic = false ∧
    Native.Binding.makeBindingUse.hirVisibility = "Private" ∧ makeBinding.kind = .published := by exact ⟨rfl, rfl, rfl⟩

/-- Apply the computed Context at the unchanged R311/R159 formation edge.
The original logical admission and every remaining App/child obligation stay
explicit at one extension. This theorem does not prove any such premise. -/
theorem original_parent_formation_iff {s : Sorts} {View : Type}
    (inputs : Inputs s) (readout : RuntimeReadout s View)
    (admissions : LocalAdmissions s View) (original : Kernel (Payload s View))
    (environment : Environment (Payload s View)) :
    let context := OriginalScopedSourceEventMapR314.Fixture.localContext externalContext
    let mark : Mark := ⟨1, none⟩
    let callee := OriginalScopedSourceEventMapR314.Fixture.callee
    let argument := OriginalScopedSourceEventMapR314.Fixture.argument
    let kernel := admissionKernel inputs readout admissions original
    SourceJudgment kernel environment context (.app mark callee argument) ↔
      (∀ premise ∈ SourceAppAdmissionR159.annotationPremises context mark,
        Local kernel environment premise) ∧
      ∃ occurrence data state,
        decode readout environment = some state ∧
        admissions.logical state ⟨mark.site, .viewLogic, 0⟩ .viewLogic data ∧
        let candidate := scopeCandidate environment occurrence (.logical .viewLogic data)
        let after := environment.extend ⟨mark.site, .viewLogic, 0⟩ candidate
        original.atom after
          (atom .descriptorFormation mark.site context [callee.site, argument.site]) ∧
        (∀ premise ∈ remainingPremises context mark callee argument, Local kernel after premise) ∧
        SourceJudgment kernel after context callee ∧ SourceJudgment kernel after context argument :=
  app_parent_formation_iff inputs readout admissions original environment
    (OriginalScopedSourceEventMapR314.Fixture.localContext externalContext) ⟨1, none⟩
    OriginalScopedSourceEventMapR314.Fixture.callee OriginalScopedSourceEventMapR314.Fixture.argument


/-- Decode this run's relay rows through the same R314 finite representation.
The fresh run token is retained; it is not equated to the older run token. -/
def currentName (resolution : Native.Current.Resolution) : NameKind × Nat :=
  match resolution with
  | .parameter id => (.parameter, id)
  | .moduleDef .. => (.definition, Native.Current.nodes.findIdx (fun node => match node.form with
      | .name _ prior => sameCurrentResolution prior resolution | _ => false))
  | _ => (.unsupported, 0)

def currentNode (node : Native.Current.SourceNode) : Node :=
  let name := match node.form with
    | .name _ resolution => currentName resolution
    | .lambda formal _ => (NameKind.parameter, formal.id)
    | _ => (.unsupported, 0)
  let instruction : InstructionFields := match node.instruction with
    | .apply callee argument => ⟨"Apply", [callee,argument], .unsupported, 0, ""⟩
    | .forward inner => ⟨"Forward", [inner], .unsupported, 0, ""⟩
    | .lambda formal body => ⟨"Lambda", [body,formal], .parameter, formal, ""⟩
    | .integer value => ⟨"Integer", [], .unsupported, 0, value⟩
    | .name resolution consumption =>
      let n := currentName resolution
      let tag := match n.1 with
        | .parameter => if consumption == "Observe" then "ParameterObserve" else "Unsupported"
        | .definition => if consumption == "Observe" then "DefinitionObserve" else "Unsupported"
        | _ => "Unsupported"
      ⟨tag, [n.2], n.1, n.2, ""⟩
    | _ => ⟨"Unsupported", [], .unsupported, 0, ""⟩
  {ordinal := node.ordinal, occurrence := node.occurrence, startByte := node.startByte, endByte := node.endByte,
   scope := match node.scope with
     | .definition => "Definition" | .parameter id => "Parameter(" ++ toString id ++ ")" | _ => "Unsupported",
   form := match node.form with
     | .name .. => .name | .integer .. => .integer | .apply .. => .apply
     | .group .. => .group | .ascription .. => .ascription | .lambda .. => .lambda | _ => .unsupported,
   children := node.childOrdinals, label := node.codeLabel,
   instruction := instruction.tag, operands := instruction.operands, nameKind := name.1, nameId := name.2,
   literal := match node.form with | .integer value => value | _ => "",
   instructionNameKind := instruction.nameKind, instructionNameId := instruction.nameId,
   instructionLiteral := instruction.literal}

def currentData : Export :=
  let formal := Native.Current.rootFormals[0]'(by decide)
  ⟨toString Native.Current.runId, Native.Current.rootBinding.name, Native.Current.rootInitializer,
    formal.id, formal.startByte, formal.endByte, Native.Current.nodes.map currentNode⟩

theorem current_data_normalized : currentData =
    {OriginalScopedSourceEventMapR314.Fixture.canonical with run := toString Native.Current.runId} := by rfl

theorem current_relay_rows : currentData.nodes = OriginalScopedSourceEventMapR314.Fixture.data.nodes := by rfl

theorem current_root_decoded : decode currentData 7 currentData.root =
    some OriginalScopedSourceEventMapR314.Fixture.root := by rfl

/-- Run metadata is absent from recursive source decoding. Proving this by
induction avoids expanding a symbolic code lookup into every source branch. -/
theorem decode_run_irrelevant (data : Export) (run : String) (fuel index : Nat) :
    decode {data with run := run} fuel index = decode data fuel index := by
  induction fuel generalizing index with
  | zero => rfl
  | succ fuel ih => simp only [OriginalScopedSourceEventMapR314.decode, nodeAt, ih]

theorem code_run_irrelevant (origin : Declaration) (data : Export) (run : String) (node : Node) :
    codeFor origin {data with run := run} node = codeFor origin data node := by
  simp only [codeFor, decode_run_irrelevant]
  rfl

theorem arena_run_irrelevant (origin : Declaration) (data : Export) (run : String)
    (otherCode : Nat → Option OriginalSourceCalleeWitnessR313.Code) :
    arena origin {data with run := run} otherCode = arena origin data otherCode := by
  simp only [arena, code_run_irrelevant]

theorem current_arena_agrees (origin : Declaration)
    (otherCode : Nat → Option OriginalSourceCalleeWitnessR313.Code) :
    arena origin currentData otherCode =
      arena origin OriginalScopedSourceEventMapR314.Fixture.data otherCode := by
  rw [current_data_normalized, OriginalScopedSourceEventMapR314.Fixture.data_normalized,
    arena_run_irrelevant]

/-- Both native operand labels and the current run's decoded source are used
by the existing R313/R312 consumer. Actual Raw/program correspondence remains
an explicit native-history premise. -/
theorem current_source_enters {C Dict Rest Schema : Type} (origin : Declaration)
    (otherCode : Nat → Option OriginalSourceCalleeWitnessR313.Code)
    (raw : OriginalCalleeDelayProvenance.Raw C Dict Rest Schema)
    (program : raw.program = (arena origin currentData otherCode).program) (caller : Nat)
    (tail : List OriginalCalleeArgumentHistoryR312.Frame) :
    ∃ original : OriginalCalleeArgumentHistoryR312.ApplySource raw,
      (OriginalCalleeArgumentHistoryR312.enter original caller tail).control = .evaluate 9 caller ∧
      lookupBinding original.call.context 8 = some makeBinding ∧
      OriginalCalleeArgumentHistoryR312.Occurs
        (source origin externalContext OriginalScopedSourceEventMapR314.Fixture.root)
        (original.save caller).call.program := by
  rw [current_arena_agrees] at program
  let a := sourceApply origin otherCode
  let original := a.toApplySource _ raw program
  exact ⟨original, rfl, actual_make_lookup, original.present⟩

end YulangClosure.OriginalModuleContextBindingR315
