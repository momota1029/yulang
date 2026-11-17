import Yulang.GeneralNominalAggregateVersion231
import Yulang.GeneralNominalCaptureMerges

/-! I44 successor allocation layer. Reservations, freshness, capture and merge
equations use one common observation version. No boundary-law claim is made. -/
namespace Yulang.GeneralNominalVersionedAllocation231
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalAllocation (Bindings occurrences origin cross lower upper equations Compatible)
open GeneralNominalAggregateVersion231 (key slot)
open PresenceNormalForm (Atom All)

def declarationKeys (root : Nat) (declaration : Declaration) (bindings : Bindings) :
    List GeneralNominalIdentities.Origin :=
  (declaration.inputNames.flatMap fun name =>
    [key root declaration.id 0 name bindings,key root declaration.id 1 name bindings]) ++
  (declaration.outputNames.map fun name => origin root declaration.id 2 name 0) ++
  (declaration.requirements.flatMap fun clause =>
    origin root declaration.id 6 clause.id 0 ::
    ((List.range clause.arguments.length).flatMap fun index =>
      [origin root declaration.id 3 clause.id index,origin root declaration.id 4 clause.id index]) ++
    (clause.outputs.map fun equation => origin root declaration.id 5 equation.id 0))

def keys (registry : Registry) (root : Nat) (bindings : Bindings) :=
  registry.declarations.flatMap fun declaration => declarationKeys root declaration bindings

def reserved (state : GeneralNominalState.State) (registry : Registry) (root : Nat) (bindings : Bindings) :=
  (keys registry root bindings).map (GeneralNominalIdentities.source state.seed)

def Fresh (state : GeneralNominalState.State) (registry : Registry) (root : Nat) (bindings : Bindings) : Prop :=
  ∀ key ∈ keys registry root bindings,
    GeneralNominalIdentities.source state.seed key ∈ GeneralNominalState.sources state →
      key ∈ state.allocated

def capture (state : GeneralNominalState.State) (registry : Registry) (root declaration : Nat)
    (bindings : Bindings) : GeneralDeclarationDemands.Capture where
  inputs := fun name => match occurrences bindings name with
    | [bounds] => bounds
    | _ => (slot state.seed root declaration 0 name bindings,
            slot state.seed root declaration 1 name bindings)
  outputs := fun name => GeneralNominalAllocation.source state registry root
    (origin root declaration 2 name 0)

def merges (state : GeneralNominalState.State) (registry : Registry) (root : Nat)
    (declaration : Declaration) (bindings : Bindings) : List (Atom Nat) :=
  declaration.inputNames.flatMap fun name =>
    match occurrences bindings name with
    | [_] => []
    | bounds => equations ((capture state registry root declaration.id bindings).inputs name).1 (lower bounds) ++
        equations ((capture state registry root declaration.id bindings).inputs name).2 (upper bounds)

def propagate (state : GeneralNominalState.State) (registry : Registry) (root : Nat)
    (declaration : Declaration) (bindings : Bindings) : GeneralNominalState.State :=
  { GeneralNominalState.extend state (reserved state registry root bindings)
      (cross bindings ++ merges state registry root declaration bindings) with
    allocated := state.allocated ++ keys registry root bindings }

theorem propagate_models (state : GeneralNominalState.State) (registry : Registry) (root : Nat)
    (declaration : Declaration) (bindings : Bindings) (model : GeneralNominalCommonBridge.Assignment) :
    GeneralNominalState.Models (propagate state registry root declaration bindings) model ↔
      GeneralNominalState.Models state model ∧ Compatible bindings model ∧
        All CommonNominalFullCarrier.model model (merges state registry root declaration bindings) := by
  change GeneralNominalState.Models (GeneralNominalState.extend state (reserved state registry root bindings) (cross bindings ++ merges state registry root declaration bindings)) model ↔ _
  simp only [GeneralNominalState.extend_models,PresenceNormalForm.all_append,GeneralNominalAllocation.cross_exact]

theorem seed_preserved : (propagate state registry root declaration bindings).seed = state.seed := rfl

theorem source_preserved (old) :
    (propagate state registry root declaration bindings).base.source old = state.base.source old := rfl

theorem capture_outputs (name) :
    (capture state registry root declaration bindings).outputs name =
      (GeneralNominalAllocation.capture state registry root declaration bindings).outputs name := rfl

theorem singleton_input (observed : occurrences bindings name = [bounds]) :
    (capture state registry root declaration bindings).inputs name = bounds := by
  simp [capture,observed]

theorem reserved_key (member : k ∈ keys registry root bindings) :
    GeneralNominalIdentities.source state.seed k ∈ reserved state registry root bindings :=
  List.mem_map.mpr ⟨k,member,rfl⟩

theorem fresh_key (fresh : Fresh state registry root bindings)
    (member : k ∈ keys registry root bindings) (new : k ∉ state.allocated) :
    GeneralNominalIdentities.source state.seed k ∉ GeneralNominalState.sources state :=
  fun collision => new (fresh k member collision)

theorem input_keys (visible : declaration ∈ registry.declarations)
    (named : name ∈ declaration.inputNames) :
    key root declaration.id 0 name bindings ∈ keys registry root bindings ∧
    key root declaration.id 1 name bindings ∈ keys registry root bindings := by
  constructor <;> apply List.mem_flatMap.mpr
  · refine ⟨declaration,visible,?_⟩
    apply List.mem_append_left
    apply List.mem_append_left
    exact List.mem_flatMap.mpr ⟨name,named,List.mem_cons_self⟩
  · refine ⟨declaration,visible,?_⟩
    apply List.mem_append_left
    apply List.mem_append_left
    exact List.mem_flatMap.mpr ⟨name,named,List.mem_cons_of_mem _ (List.mem_singleton_self _)⟩

theorem aggregate_reserved (visible : declaration ∈ registry.declarations)
    (named : name ∈ declaration.inputNames) :
    slot state.seed root declaration.id 0 name bindings ∈ reserved state registry root bindings ∧
    slot state.seed root declaration.id 1 name bindings ∈ reserved state registry root bindings :=
  ⟨reserved_key (input_keys visible named).1,reserved_key (input_keys visible named).2⟩

theorem old_allocated (member : k ∈ state.allocated) :
    k ∈ (propagate state registry root declaration bindings).allocated :=
  List.mem_append_left _ member

theorem new_allocated (member : k ∈ keys registry root bindings) :
    k ∈ (propagate state registry root declaration bindings).allocated :=
  List.mem_append_right _ member

end Yulang.GeneralNominalVersionedAllocation231
