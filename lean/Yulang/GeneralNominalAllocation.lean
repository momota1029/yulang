import Yulang.GeneralNominalState
import Yulang.GeneralDictionaryEmissionPlans

/-! Deterministic invocation-local allocation. Origins retain invocation,
declaration, purpose, clause/binder and position. An injective numeric encoding
and a persistent source seed make identities independent of registry order and
stable under reservation. Existing ownership permits revisits; any collision
with an unrelated listed or ordinary free source stays deferred. Distinct
identities are never required to have distinct semantic values. -/
namespace Yulang.GeneralNominalAllocation

open GeneralDeclarationPatterns GeneralDeclarations
open GeneralSourceDictionaries (Occurrence)
open GeneralSourceState (Interval)
open Core.PresenceGeneration (TyTerm)
open PresenceNormalForm (Atom All)

abbrev Origin := GeneralNominalIdentities.Origin
abbrev Bindings := List (Nat × Interval)

def origin (invocation declaration purpose owner position : Nat) : Origin :=
  (invocation, declaration, purpose, owner, position)

def declarationKeys (root : Nat) (declaration : Declaration) : List Origin :=
  (declaration.inputNames.flatMap fun name =>
    [origin root declaration.id 0 name 0, origin root declaration.id 1 name 0]) ++
  (declaration.outputNames.map fun name => origin root declaration.id 2 name 0) ++
  (declaration.requirements.flatMap fun clause =>
    origin root declaration.id 6 clause.id 0 ::
    ((List.range clause.arguments.length).flatMap fun index =>
      [origin root declaration.id 3 clause.id index, origin root declaration.id 4 clause.id index]) ++
    (clause.outputs.map fun equation => origin root declaration.id 5 equation.id 0))

def keys (registry : Registry) (root : Nat) : List Origin :=
  registry.declarations.flatMap (declarationKeys root)

def source (state : GeneralNominalState.State) (_registry : Registry) (_root : Nat)
    (key : Origin) : Nat := GeneralNominalIdentities.source state.seed key

def reserved (state : GeneralNominalState.State) (registry : Registry) (root : Nat) : List Nat :=
  (keys registry root).map (source state registry root)

/-- Existing ownership permits a revisit. Every other collision blocks the
candidate before any generated equation can constrain an unrelated identity. -/
def Fresh (state : GeneralNominalState.State) (registry : Registry) (root : Nat) : Prop :=
  ∀ key ∈ keys registry root, source state registry root key ∈ GeneralNominalState.sources state →
    key ∈ state.allocated

theorem member_le_max (values : List Nat) (value : Nat) (member : value ∈ values) :
    value ≤ values.foldr max 0 := by
  induction values with
  | nil => cases member
  | cons head tail ih =>
      rcases List.mem_cons.mp member with rfl | member
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih member) (Nat.le_max_right _ _)

theorem source_initial_fresh (state : GeneralNominalState.State) (registry : Registry) (root : Nat)
    (key : Origin) (old : Nat) (below : old ≤ state.seed) : source state registry root key ≠ old := by
  have above := GeneralNominalIdentities.source_above_seed state.seed key
  unfold source
  omega

theorem source_fresh (state : GeneralNominalState.State) (registry : Registry) (root : Nat)
    (fresh : Fresh state registry root) (key : Origin) (member : key ∈ keys registry root)
    (new : key ∉ state.allocated) : source state registry root key ∉ GeneralNominalState.sources state :=
  fun collision => new (fresh key member collision)

theorem source_identity (state : GeneralNominalState.State) (registry : Registry) (root : Nat)
    (first last : Origin) : source state registry root first = source state registry root last ↔ first = last :=
  GeneralNominalIdentities.source_identity state.seed first last

theorem source_preserved (state : GeneralNominalState.State) (registry : Registry) (root : Nat)
    (reserved : List Nat) (atoms : List (Atom Nat)) (key : Origin) :
    source (GeneralNominalState.extend state reserved atoms) registry root key = source state registry root key := rfl

theorem distinct_invocations (state : GeneralNominalState.State) (registry : Registry)
    (first last key purpose owner position : Nat) (different : first ≠ last) :
    source state registry first (origin first key purpose owner position) ≠
      source state registry last (origin last key purpose owner position) := by
  intro equal
  have same := (GeneralNominalIdentities.source_identity state.seed _ _).mp equal
  exact different (congrArg Prod.fst same)

theorem later_fresh (state : GeneralNominalState.State) (registry : Registry) (first next : Nat)
    (old new : Origin) (different : old ≠ new) :
    source (GeneralNominalState.extend state (reserved state registry first) []) registry next new ≠
      source state registry first old := by
  intro equal
  exact different ((GeneralNominalIdentities.source_identity state.seed new old).mp equal).symm

theorem source_registry_independent (state : GeneralNominalState.State) (first last : Registry)
    (invocation : Nat) (key : Origin) : source state first invocation key = source state last invocation key := rfl

def occurrences (bindings : Bindings) (name : Nat) : List Interval :=
  (bindings.filter fun binding => binding.1 == name).map Prod.snd

def capture (state : GeneralNominalState.State) (registry : Registry) (root key : Nat)
    (bindings : Bindings) : GeneralDeclarationDemands.Capture where
  inputs := fun name => match occurrences bindings name with
    | [bounds] => bounds
    | _ => (source state registry root (origin root key 0 name 0),
            source state registry root (origin root key 1 name 0))
  outputs := fun name => source state registry root (origin root key 2 name 0)

def allocation (state : GeneralNominalState.State) (registry : Registry) (root key : Nat)
    (clause : Clause) : GeneralDeclarationDemands.Allocation roles clause where
  arguments := fun index =>
    (source state registry root (origin root key 3 clause.id index.val),
      source state registry root (origin root key 4 clause.id index.val))
  outputs := fun equation => source state registry root (origin root key 5 equation 0)

def frame (state : GeneralNominalState.State) (registry : Registry) (root : Nat)
    (bindings : Bindings) : GeneralDictionaryEmissionPlans.Frame roles where
  capture := fun key => capture state registry root key bindings
  allocation := fun key => allocation state registry root key
  identity := fun invocation key clause => source state registry root (origin invocation key 6 clause 0)

def children (state : GeneralNominalState.State) (registry : Registry) (root : Occurrence roles)
    (declaration : Declaration) (checked : DeclarationChecked constructors roles declaration)
    (bindings : Bindings) : List (Occurrence roles) :=
  GeneralDictionaryEmissionPlans.children (frame state registry root.identity bindings) root declaration checked

/-- The full self/cross matrix is generated before any child is considered. -/
def cross (bindings : Bindings) : List (Atom Nat) :=
  bindings.flatMap fun first => bindings.flatMap fun last =>
    if first.1 = last.1 then [.tyLe (.var first.2.1) (.var last.2.2)] else []

def Compatible (bindings : Bindings) (model : GeneralNominalCommonBridge.Assignment) : Prop :=
  ∀ first ∈ bindings, ∀ last ∈ bindings, first.1 = last.1 →
    CommonNominalFullCarrier.Subtype (model first.2.1).1 (model last.2.2).1

theorem cross_exact (bindings : Bindings) (model : GeneralNominalCommonBridge.Assignment) :
    All CommonNominalFullCarrier.model model (cross bindings) ↔ Compatible bindings model := by
  constructor
  · intro valid first one last two same
    apply valid (.tyLe (.var first.2.1) (.var last.2.2))
    exact List.mem_flatMap.mpr ⟨first, one, List.mem_flatMap.mpr ⟨last, two, by simp [same]⟩⟩
  · intro valid atom member
    obtain ⟨first, one, rest⟩ := List.mem_flatMap.mp member
    obtain ⟨last, two, generated⟩ := List.mem_flatMap.mp rest
    by_cases same : first.1 = last.1
    · simp only [same, ↓reduceIte, List.mem_singleton] at generated
      subst atom
      exact valid first one last two same
    · simp [same] at generated

def lower (bounds : List Interval) : TyTerm Nat :=
  match bounds with
  | [] => .bottom
  | [pair] => .var pair.1
  | pair :: rest => .union (.var pair.1) (lower rest)

def upper (bounds : List Interval) : TyTerm Nat :=
  match bounds with
  | [] => .top
  | [pair] => .var pair.2
  | pair :: rest => .inter (.var pair.2) (upper rest)

def equations (slot : Nat) (term : TyTerm Nat) : List (Atom Nat) :=
  [.tyLe (.var slot) term, .tyLe term (.var slot)]

def merges (state : GeneralNominalState.State) (registry : Registry) (root : Nat)
    (declaration : Declaration) (bindings : Bindings) : List (Atom Nat) :=
  declaration.inputNames.flatMap fun name =>
    match occurrences bindings name with
    | [_] => []
    | bounds => equations ((capture state registry root declaration.id bindings).inputs name).1 (lower bounds) ++
        equations ((capture state registry root declaration.id bindings).inputs name).2 (upper bounds)

def propagate (state : GeneralNominalState.State) (registry : Registry) (root : Nat)
    (declaration : Declaration) (bindings : Bindings) : GeneralNominalState.State :=
  { GeneralNominalState.extend state (reserved state registry root)
      (cross bindings ++ merges state registry root declaration bindings) with
    allocated := state.allocated ++ keys registry root }

theorem propagate_models (state : GeneralNominalState.State) (registry : Registry) (root : Nat)
    (declaration : Declaration) (bindings : Bindings) (model : GeneralNominalCommonBridge.Assignment) :
    GeneralNominalState.Models (propagate state registry root declaration bindings) model ↔
      GeneralNominalState.Models state model ∧ Compatible bindings model ∧
        All CommonNominalFullCarrier.model model (merges state registry root declaration bindings) := by
  change GeneralNominalState.Models (GeneralNominalState.extend state (reserved state registry root)
    (cross bindings ++ merges state registry root declaration bindings)) model ↔ _
  simp only [GeneralNominalState.extend_models, PresenceNormalForm.all_append, cross_exact]

theorem propagated_source_preserved (state : GeneralNominalState.State) (registry : Registry) (root : Nat)
    (declaration : Declaration) (bindings : Bindings) (key : Origin) :
    source (propagate state registry root declaration bindings) registry root key = source state registry root key := rfl

end Yulang.GeneralNominalAllocation
