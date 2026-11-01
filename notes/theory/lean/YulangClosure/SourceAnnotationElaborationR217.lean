import YulangClosure.OriginalSourceSyntax

/-!
R217 candidate: immutable, source-owned annotation declarations.

This models the complete current Rust `SourceAnnotationType` constructor
shape, including effect rows on tuple elements. It does not assert that every
such parser result belongs to the original supported judgment. `valueView`
is a candidate projection. Only its root-wrapper erasure matches the cited
Oracle value-bound equation; the current carrier's Function row locations do
not yet have a proved correspondence to Oracle's explicit arrow ports.
-/
namespace YulangClosure.SourceAnnotationElaborationR217

abbrev AnnotationId := Nat
abbrev Owner := Nat
abbrev Scope := Nat
abbrev SourcePosition := Nat
abbrev EffectId := Nat
abbrev Symbol := Nat

inductive Entry where
  | value
  | computation
  deriving DecidableEq, Repr

structure EffectRow where
  position : SourcePosition
  concrete : List EffectId
  variables : List Symbol
  deriving DecidableEq, Repr

inductive AnnotationType where
  | unit (effects : Option EffectRow)
  | int (effects : Option EffectRow)
  | bool (effects : Option EffectRow)
  | str (effects : Option EffectRow)
  | variable (effects : Option EffectRow) (name : Symbol)
  | hole (effects : Option EffectRow) (position : SourcePosition)
  | tuple (effects : Option EffectRow) (elements : List AnnotationType)
  | function (effects : Option EffectRow) (argument result : AnnotationType)

structure Declaration where
  id : AnnotationId
  owner : Owner
  typeScope : Scope
  type : AnnotationType

structure FormalUse where
  annotation : AnnotationId
  owner : Owner
  typeScope : Scope
  entry : Entry
  deriving DecidableEq, Repr

abbrev Signature := List Declaration

def lookup (signature : Signature) (id : AnnotationId) : Option Declaration :=
  signature.find? (fun declaration => declaration.id == id)

def wellFormedSignature (signature : Signature) : Prop :=
  signature.Pairwise (fun left right => left.id ≠ right.id)

def resolve (signature : Signature) (use : FormalUse) : Option Declaration := do
  let declaration ← lookup signature use.annotation
  if (declaration.owner == use.owner) && (declaration.typeScope == use.typeScope)
  then some declaration else none

theorem lookup_stable (signature : Signature) (use : FormalUse)
    (declaration : Declaration) (found : lookup signature use.annotation = some declaration) :
    resolve signature use =
      (if declaration.owner == use.owner && declaration.typeScope == use.typeScope
       then some declaration else none) := by
  simp [resolve, found]

theorem resolved_source_identity (signature : Signature) (use : FormalUse)
    (declaration : Declaration) (found : resolve signature use = some declaration) :
    declaration.owner = use.owner ∧ declaration.typeScope = use.typeScope := by
  unfold resolve at found
  cases hlookup : lookup signature use.annotation with
  | none => simp [hlookup] at found
  | some candidate =>
      simp [hlookup] at found
      rcases found with ⟨⟨howner, hscope⟩, rfl⟩
      exact ⟨howner, hscope⟩

/-! The root effect row is retained verbatim by resolution. Nested rows remain
part of the same recursive annotation tree; their polarity and source meaning
are intentionally left open. -/
def rootEffects : AnnotationType → Option EffectRow
  | .unit effects | .int effects | .bool effects | .str effects |
    .variable effects _ | .hole effects _ | .tuple effects _ |
    .function effects _ _ => effects

def setRootEffects (ty : AnnotationType) (effects : Option EffectRow) : AnnotationType :=
  match ty with
  | .unit _ => .unit effects
  | .int _ => .int effects
  | .bool _ => .bool effects
  | .str _ => .str effects
  | .variable _ name => .variable effects name
  | .hole _ position => .hole effects position
  | .tuple _ elements => .tuple effects elements
  | .function _ argument result => .function effects argument result

inductive ValueView where
  | unit | int | bool | str
  | variable (name : Symbol)
  | hole (position : SourcePosition)
  | tuple (elements : List ValueView)
  | function (argument : ValueView) (argumentEffects resultEffects : Option EffectRow)
      (result : ValueView)

def valueView : AnnotationType → ValueView
  | .unit _ => .unit
  | .int _ => .int
  | .bool _ => .bool
  | .str _ => .str
  | .variable _ name => .variable name
  | .hole _ position => .hole position
  | .tuple _ elements => .tuple (elements.map valueView)
  | .function _ argument result =>
      .function (valueView argument) (rootEffects argument) (rootEffects result) (valueView result)

theorem value_view_ignores_root_effects (ty : AnnotationType)
    (first second : Option EffectRow) :
    valueView (setRootEffects ty first) = valueView (setRootEffects ty second) := by
  cases ty <;> simp [setRootEffects, valueView, rootEffects]

theorem candidate_function_view_records_child_root_rows
    (outerEffects : Option EffectRow) (argument result : AnnotationType) :
    valueView (.function outerEffects argument result) =
      .function (valueView argument) (rootEffects argument) (rootEffects result) (valueView result) := by
  simp [valueView]

end YulangClosure.SourceAnnotationElaborationR217

#print axioms YulangClosure.SourceAnnotationElaborationR217.lookup_stable
#print axioms YulangClosure.SourceAnnotationElaborationR217.resolved_source_identity
#print axioms YulangClosure.SourceAnnotationElaborationR217.value_view_ignores_root_effects
#print axioms YulangClosure.SourceAnnotationElaborationR217.candidate_function_view_records_child_root_rows
