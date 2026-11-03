import Lean.Elab.Tactic.Basic
import YulangClosure.OriginalSourceCalleeWitnessR313

/-!
R314 finite source/code correspondence, not original whole-language soundness.
Authority: adopted SG §§3.1, 3.3, 4, 5.2 and EI §§3.1–3.4; the original R159
admission, independent arms, source/event interpretation and shared witness stay open.
Native R4 SHA256: b320d208d5fa2a2b84b29e74652e5529f0e78f35453e626733770b768a74df25.
The following exact source-data declaration subset is deterministically extracted;
only unused generated Repr instances and the original import are omitted.
-/
-- BEGIN R314 native source declaration subset
namespace R314Artifact

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

structure Formal where
  id : Nat
  spelling : String
  startByte : Nat
  endByte : Nat
  sourcePosition : Position
  scope : ScopeTag
  annotation : Option Annotation

inductive SourceForm where
  | unit | integer (value : String) | boolean (value : Bool) | string (value : String)
  | decodedString (value : String) | name (spelling : String) (resolution : Resolution)
  | apply (syntaxKind : String) (callee argument : Nat) | group (inner : Nat)
  | ascription (annotation : Annotation) (inner : Nat) | lambda (formal : Formal) (body : Nat)

inductive Instruction where
  | unit | integer (value : String) | boolean (value : Bool) | string (value : String)
  | decodedString (value : String) | name (resolution : Resolution) (consumption : String)
  | apply (callee argument : Nat) | forward (inner : Nat) | lambda (formalId body : Nat)

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
def runId : Nat := 131137133318568
end R314Artifact

-- END R314 native source declaration subset

namespace YulangClosure.OriginalScopedSourceEventMapR314
open OriginalSource OriginalScopedClosure OriginalSourceInterpretation
open OriginalCalleeArgumentHistoryR312 OriginalSourceCalleeWitnessR313

inductive Form where
  | name | integer | apply | group | ascription | lambda | unsupported

/-- Owner-exported flat data. Coordinates are local to one immutable artifact;
no ordinal is asserted equal to a pre-existing original semantic identity. -/
inductive NameKind where
  | parameter | definition | unsupported

structure Node where
  ordinal : Nat
  occurrence : Nat
  startByte : Nat
  endByte : Nat
  scope : String
  form : Form
  children : List Nat
  label : Nat
  instruction : String
  operands : List Nat
  nameKind : NameKind
  nameId : Nat
  literal : String
  instructionNameKind : NameKind := .unsupported
  instructionNameId : Nat := 0
  instructionLiteral : String := ""

structure Export where
  run : String
  definition : String
  root : Nat
  formal : Nat
  formalStart : Nat
  formalEnd : Nat
  nodes : List Node

def nodeAt (data : Export) (ordinal : Nat) : Option Node :=
  data.nodes.find? (fun node => node.ordinal == ordinal)

def bindingName : NameKind → Nat → Option Name
  | .parameter, id => some (2 * id + 1)
  | .definition, id => some (2 * id)
  | .unsupported, _ => none

def decimalDigits : List Char → Nat → Option Nat
  | [], value => some value
  | digit :: rest, value =>
      if '0'.toNat ≤ digit.toNat && digit.toNat ≤ '9'.toNat then
        decimalDigits rest (10 * value + (digit.toNat - '0'.toNat))
      else none

def decimalInt (text : String) : Option Int :=
  match text.toList with
  | [] => none
  | '-' :: [] => none
  | '-' :: digits => (decimalDigits digits 0).map (fun value => -(Int.ofNat value))
  | digits => (decimalDigits digits 0).map Int.ofNat

def withAnnotation (raw : Source .expression) (target : Annotation) : Option (Source .expression) :=
  match raw with
  | .literal mark value => some (.literal {mark with annotation := some target} value)
  | .name mark name => some (.name {mark with annotation := some target} name)
  | .app mark callee argument => some (.app {mark with annotation := some target} callee argument)
  | .lambda mark formal pattern body => some (.lambda {mark with annotation := some target} formal pattern body)
  | _ => none

/-- Constructor-directed raw reification. Fuel and unsupported cases fail
closed. This finite adapter neither defines nor proves source typing. -/
def decode (data : Export) : Nat → Nat → Option (Source .expression)
  | 0, _ => none
  | fuel + 1, index => do
      let node ← nodeAt data index
      match node.form, node.children with
      | .name, [] =>
          let name ← bindingName node.nameKind node.nameId
          pure (.name ⟨node.ordinal, none⟩ name)
      | .integer, [] =>
          let value ← decimalInt node.literal
          pure (.literal ⟨node.ordinal, none⟩ (.int value))
      | .apply, [callee, argument] =>
          pure (.app ⟨node.ordinal, none⟩ (← decode data fuel callee) (← decode data fuel argument))
      | .group, [inner] => decode data fuel inner
      | .ascription, [inner] => withAnnotation (← decode data fuel inner) node.ordinal
      | .lambda, [body] =>
          let raw ← decode data fuel body
          let name ← bindingName .parameter node.nameId
          pure (.lambda ⟨node.ordinal, none⟩
            ⟨data.formalStart, name, none, false⟩ (.varPattern data.formalStart name) raw)
      | _, _ => none

/-- Operand labels are obtained from the source children's rows, rather than
copied from the Apply instruction or guessed from code arena order. -/
def sourceChildLabels (data : Export) (node : Node) : Option (List Nat) :=
  node.children.mapM (fun child => (nodeAt data child).map Node.label)

def lexical (data : Export) (node : Node) : Bool :=
  match node.form with
  | .lambda => node.ordinal == data.root && node.scope == "Definition" &&
      node.children.all (fun child => match nodeAt data child with
        | some row => row.scope == "Parameter(" ++ toString data.formal ++ ")"
        | none => false)
  | .name => match node.nameKind with
      | .parameter => node.nameId == data.formal && node.scope == "Parameter(" ++ toString node.nameId ++ ")"
      | .definition => node.scope != "Unsupported"
      | _ => false
  | .unsupported => false
  | _ => node.scope != "Unsupported" && node.children.all (fun child =>
      match nodeAt data child with
      | some row => row.scope == node.scope
      | none => false)

def compatible (data : Export) (node : Node) : Bool :=
  lexical data node && match node.form with
  | .apply => node.instruction == "Apply" && node.children.length == 2 &&
      sourceChildLabels data node == some node.operands
  | .name => node.children.isEmpty &&
      match node.nameKind, node.instructionNameKind with
      | .parameter, .parameter => node.instruction == "ParameterObserve" &&
          node.nameId == node.instructionNameId && node.operands == [node.instructionNameId]
      | .definition, .definition => node.instruction == "DefinitionObserve" &&
          node.nameId == node.instructionNameId && node.operands == [node.instructionNameId]
      | _, _ => false
  | .integer => node.instruction == "Integer" && node.children.isEmpty &&
      node.instructionLiteral == node.literal && (decimalInt node.literal).isSome
  | .group | .ascription => node.instruction == "Forward" && node.children.length == 1 &&
      sourceChildLabels data node == some node.operands
  | .lambda => node.instruction == "Lambda" && node.children.length == 1 &&
      (sourceChildLabels data node).map (fun labels => labels ++ [data.formal]) == some node.operands &&
      node.nameId == data.formal
  | _ => false

def visits (data : Export) : Nat → Nat → Option (List Nat)
  | 0, _ => none
  | fuel + 1, index => do
      let node ← nodeAt data index
      let descendants ← node.children.mapM (visits data fuel)
      pure (index :: descendants.flatten)

def complete (data : Export) : Bool :=
  match visits data (data.nodes.length + 1) data.root with
  | none => false
  | some visited => visited.eraseDups.length == visited.length &&
      visited.length == data.nodes.length &&
      data.nodes.all (fun node => visited.contains node.ordinal)

/-- All references and code labels are unique and every exported row must
match its owning source constructor. Native pointer authentication is a
separate in-process exporter obligation, not a theorem about these strings. -/
def valid (data : Export) : Bool :=
  !data.run.isEmpty && !data.definition.isEmpty &&
  data.nodes.all (compatible data) && complete data &&
  (data.nodes.map Node.occurrence).eraseDups.length == data.nodes.length &&
  (data.nodes.map Node.ordinal).eraseDups.length == data.nodes.length &&
  (data.nodes.map Node.label).eraseDups.length == data.nodes.length &&
  (decode data (data.nodes.length + 1) data.root).isSome

/-- The allocator used by R297 retains full premises and scope. This selector reads the actual App's pre-view-logic occurrence position. -/
def appAnchor (site : Site) (program : Program) : Option (Position × Context) :=
  match program with
  | .existsE occurrence (.rule _ .app actual context _ _) =>
      if actual == site then some (occurrence.position, context) else none
  | _ => none

/-- Reading an allocated path never removes the intervening scope constructors. -/
def follow : List Nat → Program → Option Program
  | [], program => some program
  | index :: rest, program => do
      let child ← (children program)[index]?
      follow rest child

theorem follow_occurs (path : List Nat) (outer selected : Program)
    (found : follow path outer = some selected) : Occurs outer selected := by
  induction path generalizing outer with
  | nil =>
      simp only [follow, Option.some.injEq] at found
      subst selected
      exact .root outer
  | cons index rest ih =>
      simp only [follow] at found
      cases child : (children outer)[index]? with
      | none => simp only [child, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at found
      | some next =>
          simp only [child, Option.bind_eq_bind, Option.bind_some] at found
          exact .descend (List.mem_of_getElem? child) (ih next found)

set_option maxRecDepth 2048
set_option maxHeartbeats 400000
def instructionFor (node : Node) : Option Instruction :=
  if node.instruction == "Apply" then
    match node.operands with
    | [callee, argument] => some (.apply callee argument)
    | _ => none
  else if node.instruction == "ParameterObserve" then
    some (.name (2 * node.instructionNameId + 1) ⟨.parameter, .observe⟩)
  else some .retained

def codeFor (origin : Declaration) (data : Export) (node : Node) : Option Code := do
  if !compatible data node then none else do
    let raw ← decode data (data.nodes.length + 1) node.ordinal
    let instruction ← instructionFor node
    pure ⟨origin, node.ordinal, raw, instruction⟩

def arena (origin : Declaration) (data : Export) (otherCode : Nat → Option Code) : Arena :=
  ⟨fun label => match data.nodes.find? (fun node => node.label == label) with
    | some node => codeFor origin data node
    | none => otherCode label⟩

/-- Complete native resolution equality; module identity retains name, realm,
path and same-name ordinal. The finite name number is an intern, not a DefId. -/
def sameResolution : R314Artifact.Resolution → R314Artifact.Resolution → Bool
  | .parameter left, .parameter right => left == right
  | .moduleDef ln lr lp lo, .moduleDef rn rr rp ro =>
      ln == rn && lr == rr && lp == rp && lo == ro
  | _, _ => false

def nativeName (nodes : List R314Artifact.SourceNode)
    (resolution : R314Artifact.Resolution) : NameKind × Nat :=
  match resolution with
  | .parameter id => (.parameter, id)
  | .moduleDef .. =>
      (.definition, nodes.findIdx (fun node => match node.form with
        | .name _ prior => sameResolution prior resolution
        | _ => false))
  | _ => (.unsupported, 0)

def sourceFormTag : R314Artifact.SourceForm → Form
  | .name .. => .name
  | .integer .. => .integer
  | .apply .. => .apply
  | .group .. => .group
  | .ascription .. => .ascription
  | .lambda .. => .lambda
  | _ => .unsupported

def nativeChildren : R314Artifact.SourceForm → List Nat
  | .apply _ callee argument => [callee, argument]
  | .group inner | .ascription _ inner | .lambda _ inner => [inner]
  | _ => []

def nativeScope : R314Artifact.ScopeTag → String
  | .definition => "Definition"
  | .parameter id => "Parameter(" ++ toString id ++ ")"
  | _ => "Unsupported"

structure InstructionFields where
  tag : String
  operands : List Nat
  nameKind : NameKind
  nameId : Nat
  literal : String

def nativeInstruction (nodes : List R314Artifact.SourceNode) :
    R314Artifact.Instruction → InstructionFields
  | .apply callee argument => ⟨"Apply", [callee,argument], .unsupported, 0, ""⟩
  | .forward inner => ⟨"Forward", [inner], .unsupported, 0, ""⟩
  | .lambda formal body => ⟨"Lambda", [body,formal], .parameter, formal, ""⟩
  | .integer value => ⟨"Integer", [], .unsupported, 0, value⟩
  | .name resolution consumption =>
      let name := nativeName nodes resolution
      let tag := match name.1 with
        | .parameter => if consumption == "Observe" then "ParameterObserve" else "Unsupported"
        | .definition => if consumption == "Observe" then "DefinitionObserve" else "Unsupported"
        | _ => "Unsupported"
      ⟨tag, [name.2], name.1, name.2, ""⟩
  | _ => ⟨"Unsupported", [], .unsupported, 0, ""⟩

/-- A pure adapter over independently exported typed source and instruction
fields. A source-child list disagreement is rejected before decoding. -/
def formalAgreement (formal : R314Artifact.Formal) : Bool :=
  match R314Artifact.rootFormals with
  | [original] => formal.id == original.id && formal.spelling == original.spelling &&
      formal.startByte == original.startByte && formal.endByte == original.endByte &&
      formal.sourcePosition.startByte == original.sourcePosition.startByte && formal.sourcePosition.endByte == original.sourcePosition.endByte &&
      formal.sourcePosition.kind == original.sourcePosition.kind && formal.sourcePosition.text == original.sourcePosition.text &&
      formal.annotation.isNone && original.annotation.isNone &&
      (match formal.scope, original.scope with | .definition, .definition => true | _, _ => false)
  | _ => false

def nativeNode (nodes : List R314Artifact.SourceNode) (node : R314Artifact.SourceNode) : Node :=
  let name := match node.form with
    | .name _ resolution => nativeName nodes resolution
    | .lambda formal _ => (NameKind.parameter, formal.id)
    | _ => (.unsupported, 0)
  let literal := match node.form with | .integer value => value | _ => ""
  let instruction := nativeInstruction nodes node.instruction
  { ordinal := node.ordinal, occurrence := node.occurrence,
    startByte := node.startByte, endByte := node.endByte,
    scope := nativeScope node.scope,
    form := if node.childOrdinals == nativeChildren node.form &&
      (match node.form with | .lambda formal _ => formalAgreement formal | _ => true)
      then sourceFormTag node.form else .unsupported,
    children := node.childOrdinals, label := node.codeLabel,
    instruction := instruction.tag, operands := instruction.operands,
    nameKind := name.1, nameId := name.2, literal := literal,
    instructionNameKind := instruction.nameKind, instructionNameId := instruction.nameId,
    instructionLiteral := instruction.literal }

namespace Fixture

def data : Export :=
  let formal := R314Artifact.rootFormals[0]'(by decide)
  ⟨toString R314Artifact.runId, R314Artifact.rootBinding.name,
    R314Artifact.rootInitializer, formal.id, formal.startByte, formal.endByte,
    R314Artifact.nodes.map (nativeNode R314Artifact.nodes)⟩

/-- A compact normal form of the typed adapter, justified by equality below;
its fields are not an independently supplied source/code map. -/
def canonical : Export :=
  ⟨toString R314Artifact.runId, "relay", 0, 0, 98, 103,
   [⟨0, 11, 89, 118, "Definition", .lambda, [1], 7, "Lambda", [8,0], .parameter, 0, "", .parameter, 0, ""⟩,
    ⟨1, 12, 113, 118, "Parameter(0)", .apply, [2,3], 8, "Apply", [9,10], .unsupported, 0, "", .unsupported, 0, ""⟩,
    ⟨2, 13, 111, 112, "Parameter(0)", .apply, [4,5], 9, "Apply", [11,12], .unsupported, 0, "", .unsupported, 0, ""⟩,
    ⟨3, 16, 113, 118, "Parameter(0)", .name, [], 10, "ParameterObserve", [0], .parameter, 0, "", .parameter, 0, ""⟩,
    ⟨4, 14, 106, 110, "Parameter(0)", .name, [], 11, "DefinitionObserve", [4], .definition, 4, "", .definition, 4, ""⟩,
    ⟨5, 15, 111, 112, "Parameter(0)", .integer, [], 12, "Integer", [], .unsupported, 0, "1", .unsupported, 0, "1"⟩]⟩

theorem data_normalized : data = canonical := by rfl

def argument : Source .expression := .name ⟨3, none⟩ 1
def callee : Source .expression := .app ⟨2, none⟩ (.name ⟨4, none⟩ 8) (.literal ⟨5, none⟩ (.int 1))
def selected : Source .expression := .app ⟨1, none⟩ callee argument
def root : Source .expression := .lambda ⟨0, none⟩ ⟨98, 1, none, false⟩ (.varPattern 98 1) selected

theorem root_decodes : decode data 7 data.root = some root := by rw [data_normalized]; rfl
theorem selected_decodes : decode data 7 1 = some selected := by rw [data_normalized]; rfl
theorem callee_decodes : decode data 7 2 = some callee := by rw [data_normalized]; rfl
theorem argument_decodes : decode data 7 3 = some argument := by rw [data_normalized]; rfl

/-- This candidate is checked against R297's computed allocation below. -/
def position (origin : Declaration) : Position :=
  ⟨origin, [0,0,0,0,0,0,0,0,0,1,0,0],
    [.existsE ⟨98, .description, 0⟩,
     .existsE ⟨0, .viewLogic, 0⟩,
     .forallE ⟨0, .invocation, 0⟩,
     .existsE ⟨98, .receipt, 0⟩,
     .executionE ⟨98, .returnRebind, 0⟩,
     .sharedE ⟨98, .shared, 0⟩,
     .existsE ⟨1, .eventProof, 0⟩], []⟩

def localContext (context : Context) : Context :=
  {name := 1, owner := 98, kind := .formal, annotation := none,
    entry := some .value, singleUse := true} :: context

def selectedPath : List Nat := [0,0,0,0,0,0,0,0,1,0,0]

theorem anchor_computed (origin : Declaration) (context : Context) :
    (follow selectedPath (source origin context root)).bind (appAnchor 1) =
      some (position origin, localContext context) := by
  run_tac Lean.Meta.withTransparency .all <| Lean.Elab.Tactic.evalTactic (← `(tactic| rfl))

theorem selected_occurs (origin : Declaration) (context : Context) :
    Occurs (source origin context root)
      (allocate (position origin) (sourceRules (localContext context) selected)) := by
  apply follow_occurs selectedPath
  run_tac Lean.Meta.withTransparency .all <| Lean.Elab.Tactic.evalTactic (← `(tactic| rfl))

/-- This is R313's actual SourceApply, produced from the decoded complete root
and independently validated code rows. No arbitrary callee or occurrence proof
is supplied by the caller. The external module Context keeps its original owner. -/
def sourceApply (origin : Declaration) (context : Context) (otherCode : Nat → Option Code) : SourceApply (arena origin data otherCode) where
  origin := origin
  rootContext := context
  root := root
  position := position origin
  context := localContext context
  mark := ⟨1, none⟩
  callee := callee
  argument := argument
  present := selected_occurs origin context
  applyLabel := 8
  calleeLabel := 9
  argumentLabel := 10
  applyCode := ⟨origin, 1, selected, .apply 9 10⟩
  calleeCode := ⟨origin, 2, callee, .apply 11 12⟩
  argumentCode := ⟨origin, 3, argument, .name 1 ⟨.parameter, .observe⟩⟩
  applyFound := by rw [data_normalized]; rfl
  applyOwner := rfl
  applySource := rfl
  applySite := rfl
  instruction := rfl
  calleeFound := by rw [data_normalized]; rfl
  argumentFound := by rw [data_normalized]; rfl
  calleeOwner := rfl
  argumentOwner := rfl
  calleeSource := rfl
  argumentSource := rfl

theorem decoded_source_enters (origin : Declaration) (context : Context)
    (otherCode : Nat → Option Code)
    (raw : OriginalCalleeDelayProvenance.Raw C Dict Rest Schema)
    (program : raw.program = (arena origin data otherCode).program) (caller : Nat)
    (tail : List OriginalCalleeArgumentHistoryR312.Frame) :
    let a := sourceApply origin context otherCode
    let original := a.toApplySource (arena origin data otherCode) raw program
    (enter original caller tail).control = .evaluate 9 caller ∧
    (enter original caller tail).frames = .callee (original.save caller) :: tail ∧
    Occurs (source origin context root) (original.save caller).call.program := by
  exact ⟨rfl, rfl, (sourceApply origin context otherCode).toApplySource (arena origin data otherCode) raw program |>.present⟩

theorem decoded_observe_delay (origin : Declaration) (context : Context)
    (otherCode : Nat → Option Code)
    (raw : OriginalCalleeDelayProvenance.Raw C Dict Rest Schema)
    (program : raw.program = (arena origin data otherCode).program) (caller : Nat) :
    OriginalCalleeDelayProvenance.directFormalRoot raw 10 caller = none ∧
    OriginalCalleeDelayProvenance.delayMetadata raw
      (OriginalCalleeDelayProvenance.directFormalRoot raw 10 caller) = some ⟨none, true, .ordinary⟩ := by
  exact observe_has_no_inherited_root (arena origin data otherCode) (sourceApply origin context otherCode)
    raw program 1 rfl caller

def changeNode (data : Export) (index : Nat) (change : Node → Node) : Export :=
  {data with nodes := data.nodes.map (fun node => if node.ordinal == index then change node else node)}

def acceptsRun (expected : String) (candidate : Export) : Bool :=
  expected == candidate.run && valid candidate

theorem data_valid : valid data = true := by
  simp only [data_normalized]
  decide +kernel

theorem callee_name_substitution_rejected :
    valid (changeNode data 2 (fun node => {node with form := .name, children := [], nameKind := .parameter})) = false := by
  simp only [data_normalized]
  decide +kernel

theorem swapped_labels_rejected :
    valid (changeNode data 1 (fun node => {node with operands := [10,9]})) = false := by
  simp only [data_normalized]
  decide +kernel

theorem wrong_scope_rejected :
    valid (changeNode data 3 (fun node => {node with scope := "Definition"})) = false := by
  simp only [data_normalized]
  decide +kernel

theorem wrong_binding_rejected :
    valid (changeNode data 3 (fun node => {node with nameId := 1})) = false := by
  simp only [data_normalized]
  decide +kernel

theorem conflated_occurrence_rejected :
    valid (changeNode data 3 (fun node => {node with occurrence := 12})) = false := by
  simp only [data_normalized]
  decide +kernel

theorem different_run_rejected :
    acceptsRun data.run {data with run := "foreign-run"} = false := by
  simp only [data_normalized]
  decide +kernel

theorem complete_telescope (origin : Declaration) : (position origin).telescope.length = 7 := rfl

end Fixture
end YulangClosure.OriginalScopedSourceEventMapR314
