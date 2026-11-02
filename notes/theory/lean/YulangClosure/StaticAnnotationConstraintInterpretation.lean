import YulangClosure.SimpleSubConstraintSyntax
import YulangClosure.PaperTypeSubstitution

/-!
R208's concrete data interpretation for resolved annotation hygiene.

One annotation declaration is source data, not an opaque predicate. Generation
retains its resolved tree and coordinates; a solution may satisfy the ordinary
Simple-sub store but cannot replace that tree or its owner. Permission,
allowance, symbolic dependencies, actual arrivals and handler residuals are
represented separately. This module defines a source/constraint fragment; it
does not claim the Rust parser has been connected to this data yet.
-/
namespace YulangClosure.StaticAnnotationConstraintInterpretation

open PaperTypes

inductive Polarity where
  | positive | negative
  deriving DecidableEq, Repr

def Polarity.flip : Polarity → Polarity
  | .positive => .negative
  | .negative => .positive

inductive Variance where
  | covariant | contravariant | invariant
  deriving DecidableEq, Repr

def Variance.images (variance : Variance) (polarity : Polarity) : List Polarity :=
  match variance with
  | .covariant => [polarity]
  | .contravariant => [polarity.flip]
  | .invariant => [polarity, polarity.flip]

def Ty.hasVariable : Ty → Bool
  | .var _ => true
  | .base _ | .top | .bottom | .tupleNil | .recordNil | .variantNil => false
  | .union a b | .intersection a b | .tupleCons a b => a.hasVariable || b.hasVariable
  | .recordCons _ _ field tail | .variantCons _ field tail =>
      field.hasVariable || tail.hasVariable
  | .nominal _ arguments => arguments.hasVariable
  | .mu body | .thunk body | .poly body => body.hasVariable
  | .callable argument result | .kont argument result =>
      argument.hasVariable || result.hasVariable

def Ty.variables : Ty → List Nat
  | .var index => [index]
  | .base _ | .top | .bottom | .tupleNil | .recordNil | .variantNil => []
  | .union a b | .intersection a b | .tupleCons a b => a.variables ++ b.variables
  | .recordCons _ _ field tail | .variantCons _ field tail => field.variables ++ tail.variables
  | .nominal _ arguments => arguments.variables
  | .mu body | .thunk body | .poly body => body.variables
  | .callable argument result | .kont argument result => argument.variables ++ result.variables

structure EffectInstance where
  operation : Nat
  typeArguments : List Ty
  deriving DecidableEq, Repr

def EffectInstance.isConcrete (effect : EffectInstance) : Bool :=
  effect.typeArguments.all (fun ty => !ty.hasVariable)

def EffectInstance.symbolicVariables (effect : EffectInstance) : List Nat :=
  effect.typeArguments.flatMap Ty.variables

structure EffectRow where
  position : Nat
  concrete : List EffectInstance
  symbolic : List Nat
  deriving DecidableEq, Repr

/-! The resolved tree is generic over source type constructors. Function
argument/result children are represented by the designated contravariant and
covariant edges; all other constructor edges carry their declaration-derived
variance explicitly. Labels preserve the original ordered path. -/
structure Child where
  label : Nat
  variance : Variance
  tree : Annotation

structure Children where
  items : List Child
  deriving Repr

inductive Annotation where
  | node (constructor : Nat) (effect : Option EffectRow) (children : Children)
  deriving Repr

structure ResolvedAnnotation where
  identity : Nat
  tree : Annotation
  deriving Repr

abbrev AnnotationEnvironment := Nat → Option ResolvedAnnotation

structure FormalUse (Owner Scope Event Witness : Type) where
  annotation : Nat
  owner : Owner
  scope : Scope
  event : Event
  witness : Witness
  entryIsComputation : Bool

/-! Every row at a node is visited at its full path. Variance is composed at
each child edge; invariant edges retain both directions. The root row is an
ordinary site, which is kept distinct from all nested Function rows. -/
inductive EffectSite : Annotation → Polarity → List Nat → EffectRow → Prop where
  | root {constructor children polarity row} :
      EffectSite (.node constructor (some row) children) polarity [] row
  | child {constructor effect children child polarity childPolarity path row}
      (member : child ∈ children.items)
      (image : childPolarity ∈ child.variance.images polarity)
      (nested : EffectSite child.tree childPolarity path row) :
      EffectSite (.node constructor effect children) polarity (child.label :: path) row

structure ScopedEffectSite (Owner Scope : Type) where
  annotation : Nat
  owner : Owner
  scope : Scope
  path : List Nat
  rowPosition : Nat
  effect : EffectInstance
  deriving Repr

structure SymbolicDependency (Owner Scope : Type) where
  annotation : Nat
  owner : Owner
  scope : Scope
  path : List Nat
  rowPosition : Nat
  variable : Nat
  deriving Repr

inductive ClassifiedSite (Owner Scope : Type) where
  | permission (site : ScopedEffectSite Owner Scope)
  | allowance (site : ScopedEffectSite Owner Scope)
  | symbolic (dependency : SymbolicDependency Owner Scope)

def classifyRow {Owner Scope : Type} (use : FormalUse Owner Scope Event Witness)
    (path : List Nat) (polarity : Polarity) (row : EffectRow) : List (ClassifiedSite Owner Scope) := Id.run do
  let mut out := row.symbolic.map fun variable =>
    ClassifiedSite.symbolic ⟨use.annotation, use.owner, use.scope, path, row.position, variable⟩
  for effect in row.concrete do
    if effect.isConcrete then
      let site : ScopedEffectSite Owner Scope :=
        ⟨use.annotation, use.owner, use.scope, path, row.position, effect⟩
      out := out ++ [match polarity with
        | .negative => .permission site
        | .positive => .allowance site]
    else
      for variable in effect.symbolicVariables do
        out := out ++ [.symbolic ⟨use.annotation, use.owner, use.scope,
          path, row.position, variable⟩]
  return out

/-! The extraction relation is the semantic profile of the resolved source
tree. Generated clauses retain this tree as data; they do not carry a source
judgment or a permission predicate as an assumed field. -/
inductive ProfileEntry {Owner Scope : Type} (use : FormalUse Owner Scope Event Witness) :
    Annotation → List Nat → ClassifiedSite Owner Scope → Prop where
  | permission {tree path row} (site : EffectSite tree .negative path row)
      (effect : EffectInstance) (member : effect ∈ row.concrete) (closed : effect.isConcrete = true) :
      ProfileEntry use tree path (.permission ⟨use.annotation, use.owner, use.scope, path, row.position, effect⟩)
  | allowance {tree path row} (site : EffectSite tree .positive path row)
      (effect : EffectInstance) (member : effect ∈ row.concrete) (closed : effect.isConcrete = true) :
      ProfileEntry use tree path (.allowance ⟨use.annotation, use.owner, use.scope, path, row.position, effect⟩)
  | rowVariable {tree path row} (site : EffectSite tree .positive path row)
      (variable : Nat) (member : variable ∈ row.symbolic) :
      ProfileEntry use tree path (.symbolic ⟨use.annotation, use.owner, use.scope, path, row.position, variable⟩)
  | negativeRowVariable {tree path row} (site : EffectSite tree .negative path row)
      (variable : Nat) (member : variable ∈ row.symbolic) :
      ProfileEntry use tree path (.symbolic ⟨use.annotation, use.owner, use.scope, path, row.position, variable⟩)

structure GeneratedAnnotationClause (Owner Scope Event Witness : Type) where
  use : FormalUse Owner Scope Event Witness
  resolved : ResolvedAnnotation

def generate {Owner Scope Event Witness : Type} (environment : AnnotationEnvironment)
    (use : FormalUse Owner Scope Event Witness) : Option (GeneratedAnnotationClause Owner Scope Event Witness) := do
  let resolved ← environment use.annotation
  if resolved.identity = use.annotation then some ⟨use, resolved⟩ else none

/-! Original source meaning for `sourceFormalRole`: one resolved declaration
at the same ID and coordinates, with the polarity-derived profile. Outer entry
is retained as source data; this clause never chooses it from the body. -/
def SourceFormalRole {Owner Scope Event Witness : Type}
    (environment : AnnotationEnvironment) (use : FormalUse Owner Scope Event Witness) : Prop :=
  ∃ resolved, environment use.annotation = some resolved ∧
    resolved.identity = use.annotation ∧
    ∀ tree path polarity row,
      resolved.tree = tree → EffectSite tree polarity path row →
        ∀ effect, effect ∈ row.concrete →
          effect.isConcrete = true →
          (polarity = .negative ∧
             ProfileEntry use tree path (.permission
               ⟨use.annotation, use.owner, use.scope, path, row.position, effect⟩)) ∨
          (polarity = .positive ∧
             ProfileEntry use tree path (.allowance
               ⟨use.annotation, use.owner, use.scope, path, row.position, effect⟩))

structure Assignment (Owner Scope Event Witness : Type) where
  valuation : SimpleSub.Valuation
  annotationEnvironment : AnnotationEnvironment
  owner : Owner
  scope : Scope
  event : Event
  witness : Witness

def Solves {Owner Scope Event Witness : Type}
    (clause : GeneratedAnnotationClause Owner Scope Event Witness)
    (assignment : Assignment Owner Scope Event Witness)
    (store : SimpleSub.Store) : Prop :=
  SimpleSub.Store.Satisfied assignment.valuation store ∧
  assignment.annotationEnvironment clause.use.annotation = some clause.resolved ∧
  clause.resolved.identity = clause.use.annotation ∧
  assignment.owner = clause.use.owner ∧ assignment.scope = clause.use.scope ∧
  assignment.event = clause.use.event ∧ assignment.witness = clause.use.witness

theorem generated_formal_role_reflection {Owner Scope Event Witness : Type}
    (environment : AnnotationEnvironment) (use : FormalUse Owner Scope Event Witness)
    (clause : GeneratedAnnotationClause Owner Scope Event Witness)
    (assignment : Assignment Owner Scope Event Witness) (store : SimpleSub.Store)
    (generated : generate environment use = some clause)
    (solved : Solves clause assignment store) :
    SourceFormalRole assignment.annotationEnvironment use ∧
    assignment.owner = use.owner ∧ assignment.scope = use.scope ∧
    assignment.event = use.event ∧ assignment.witness = use.witness := by
  simp only [generate] at generated
  split at generated
  · injection generated with equal
    subst clause
    rcases solved with ⟨_, resolved, identity, owner, scope, event, witness⟩
    refine ⟨?_, owner, scope, event, witness⟩
    refine ⟨clause.resolved, resolved, identity, ?_⟩
    intro tree path polarity row treeEq site effect member closed
    subst tree
    rcases polarity with _ | _
    · exact Or.inr ⟨rfl, .allowance site effect member closed⟩
    · exact Or.inl ⟨rfl, .permission site effect member closed⟩
  · simp at generated

/-! A permission licenses a subtraction only when an actual selected handler
and an actual arrival share the complete source coordinate and EffectInstance.
The residual is always a filter of actual inflow. -/
structure Arrival where
  occurrence : Nat
  owner : Nat
  scope : Nat
  effect : EffectInstance
  deriving DecidableEq, Repr

structure Handler where
  occurrence : Nat
  owner : Nat
  scope : Nat
  annotation : Nat
  path : List Nat
  effect : EffectInstance
  actual : Bool
  deriving DecidableEq, Repr

def licensed (permissions : List (ScopedEffectSite Nat Nat)) (handler : Handler)
    (arrival : Arrival) : Bool :=
  handler.actual && handler.occurrence == arrival.occurrence &&
  handler.owner == arrival.owner && handler.scope == arrival.scope &&
  handler.effect == arrival.effect &&
  permissions.any (fun permission =>
    permission.annotation == handler.annotation &&
    permission.owner == handler.owner && permission.scope == handler.scope &&
    permission.path == handler.path && permission.effect == handler.effect)

def residual (permissions : List (ScopedEffectSite Nat Nat)) (handlers : List Handler)
    (inflow : List Arrival) : List Arrival :=
  inflow.filter fun arrival => !(handlers.any fun handler => licensed permissions handler arrival)

theorem residual_subset_inflow (permissions : List (ScopedEffectSite Nat Nat))
    (handlers : List Handler) (inflow : List Arrival) (arrival : Arrival)
    (retained : arrival ∈ residual permissions handlers inflow) : arrival ∈ inflow := by
  exact (List.mem_filter.mp retained).1

theorem empty_inflow_stays_empty (permissions : List (ScopedEffectSite Nat Nat))
    (handlers : List Handler) : residual permissions handlers [] = [] := rfl

theorem unmatched_arrival_retained (permissions : List (ScopedEffectSite Nat Nat))
    (handlers : List Handler) (inflow : List Arrival) (arrival : Arrival)
    (arrived : arrival ∈ inflow)
    (unmatched : ∀ handler, handler ∈ handlers → licensed permissions handler arrival = false) :
    arrival ∈ residual permissions handlers inflow := by
  apply List.mem_filter.mpr
  refine ⟨arrived, ?_⟩
  simp only [Bool.not_eq_true']
  cases selected : handlers.any (fun handler => licensed permissions handler arrival) with
  | false => rfl
  | true =>
      have witness := List.any_eq_true.mp selected
      rcases witness with ⟨handler, member, valid⟩
      have contradiction := unmatched handler member
      simp [contradiction] at valid

theorem permission_does_not_create_arrival (permissions : List (ScopedEffectSite Nat Nat))
    (handlers : List Handler) (arrival : Arrival)
    (retained : arrival ∈ residual permissions handlers []) : False := by
  simpa [residual] using retained

end YulangClosure.StaticAnnotationConstraintInterpretation
