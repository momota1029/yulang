import Yulang.GeneralNominalRecursiveBoundary
import Yulang.GeneralDictionaryReadback

/-!
# Model-indexed source evidence for the recursive nominal boundary

The local judgment below names a visible, checked source declaration and its
actual emitted obligations. Registry and context constructor interpretations are
required to agree through Metadata. Its semantic premises are checked in the supplied
model: the private interval equations, recursive projections, and materialized
source equations. It does not refer to Survivor, Unique, Classify, or execution.

This is an inspection-mediated source certificate. It uses the existing partial
pattern inspection/materialization and retains their completion guards; it does
not claim a separate completeness theorem for unrestricted ground patterns.

Crucially, a Survivor has a branch model, not every model of the original state.
The node theorem therefore exposes its one-model BranchModels premise. The
module supplies the Evidence field without claiming B4TargetV3.EvidenceNode.
-/
namespace Yulang.GeneralDictionaryRecursiveEvidence

open GeneralDeclarations
open GeneralSourceDictionaries (Occurrence LocalInstance ErasedEvidence Readback)
open GeneralDictionaryReadback (Payload PayloadEvidence)
open GeneralNominalRecursiveCandidates (Context arguments report generated BranchModels RequestReady Survivor)
open GeneralNominalRecursiveInspection (Finished bindings)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (All₂)

/-- A finite source instance in one specified model. Completion guards certify
which source inspection and materialization the semantic facts refer to. The
children are the complete canonical emission, with multiplicity preserved. -/
def Instance (registry : Registry) (context : Context) (model : Assignment) : LocalInstance roles :=
  fun root key children =>
    ∃ declaration ∈ registry.declarations,
      ∃ checked : DeclarationChecked registry.constructors roles declaration,
        declaration.id = key ∧ declaration.role = root.demand.role ∧
        ∃ bounds, arguments context root = some bounds ∧
          Finished (report context declaration bounds) ∧
          RequestReady registry context root declaration checked bounds ∧
          children = GeneralNominalAllocation.children context.state registry root declaration checked
            (bindings context.state (report context declaration bounds)) ∧
          GeneralNominalRecursiveCandidates.Metadata registry context ∧
          BranchModels registry context root declaration checked bounds model

/-- Semantic evidence retains an entire source-indexed witness behind the raw
runtime payload. No candidate-selection or execution derivation occurs here. -/
def Evidence (registry : Registry) (context : Context) (model : Assignment)
    (root : Occurrence roles) (payload : Payload) : Prop :=
  ErasedEvidence (Instance registry context model) root payload

/-- Fill only the dictionary field; transition/closure fields remain the caller's
unchanged package. This adapter does not implement Step, Stable, or Generated. -/
def boundary (roles : Roles.RoleDecls)
    (remaining : GeneralNominalLocalBoundary.Remaining (GeneralNominalCandidates.vocabulary roles)) :
    B4Target.SourceBoundary (GeneralNominalCandidates.vocabulary roles) :=
  GeneralNominalLocalBoundary.complete (GeneralNominalLocalBoundary.recursiveFields roles)
    { remaining with Evidence := Evidence }

theorem evidence_iff_payload (registry : Registry) (context : Context) (model : Assignment)
    (root : Occurrence roles) (payload : Payload) :
    Evidence registry context model root payload ↔
      PayloadEvidence (Instance registry context model) root payload :=
  (GeneralDictionaryReadback.payload_iff_erased _ _ _).symm

/-- The original model is retained, rather than silently substituted with the
existential consistency witness of a candidate. -/
theorem instance_models (registry : Registry) (context : Context) (model : Assignment)
    (root : Occurrence roles) (key : Nat) (children : List (Occurrence roles))
    (instanceRule : Instance registry context model root key children) :
    GeneralNominalState.Models context.state model := by
  obtain ⟨declaration, _, checked, _, _, bounds, _, _, _, _, _, branch⟩ := instanceRule
  exact (GeneralNominalRecursiveCandidates.branch_interval_sound registry context root
    declaration checked bounds model branch).1

/-- A survivor supplies a source instance in some branch model. This existential
statement does not permit evidence in an arbitrary original-state model. -/
theorem survivor_instance_exists (registry : Registry) (context : Context)
    (root : Occurrence roles) (key : Nat) (children : List (Occurrence roles))
    (survivor : Survivor registry context root key children) :
    ∃ model, Instance registry context model root key children := by
  obtain ⟨_, declaration, visible, checked, identity, role, bounds, located, prepared, emitted⟩ := survivor
  obtain ⟨metadata, _, _, other, found, finished, ready, model, branch⟩ := prepared
  have same := Option.some.inj (located.symm.trans found)
  subst other
  exact ⟨model, declaration, visible, checked, identity, role, bounds, located,
    finished, ready, emitted, metadata, branch⟩

/-- Replace only the existential branch witness with an explicitly provided model.
Registry key uniqueness identifies the same declaration; argument lookup identifies
the same bounds. Nothing here promotes existential consistency to universality. -/
theorem survivor_instance_of_branch (registry : Registry) (checked : Checked registry)
    (context : Context) (model : Assignment) (root : Occurrence roles)
    (key : Nat) (children : List (Occurrence roles))
    (survivor : Survivor registry context root key children)
    (declaration : Declaration) (visible : declaration ∈ registry.declarations)
    (valid : DeclarationChecked registry.constructors roles declaration)
    (identity : declaration.id = key)
    (bounds : List (GeneralNominalInspection.Bounds context.state))
    (located : arguments context root = some bounds)
    (branch : BranchModels registry context root declaration valid bounds model) :
    Instance registry context model root key children := by
  obtain ⟨_, selected, present, selectedChecked, selectedKey, role, other, found, prepared, emitted⟩ := survivor
  have same := GeneralDictionaryEmissionPlans.declaration_key_unique registry checked
    selected declaration present visible (selectedKey.trans identity.symm)
  subst selected
  have same := Option.some.inj (located.symm.trans found)
  subst other
  obtain ⟨metadata, _, _, inner, innerFound, finished, ready, _⟩ := prepared
  have same := Option.some.inj (located.symm.trans innerFound)
  subst inner
  exact ⟨declaration, visible, valid, identity, role, bounds, located,
    finished, ready, emitted, metadata, branch⟩

/-- Every node combines its one-model source instance with evidence for all of
its emitted children. This is the representation-level adapter, not the missing
all-original-models applicability theorem. -/
theorem evidence_node (registry : Registry) (context : Context) (model : Assignment)
    (root : Occurrence roles) (key : Nat) (children : List (Occurrence roles))
    (dictionaries : List Payload) (instanceRule : Instance registry context model root key children)
    (given : All₂ (Evidence registry context model) children dictionaries) :
    Evidence registry context model root (.node key dictionaries) :=
  GeneralDictionaryReadback.erased_evidence_node _ _ _ _ _ instanceRule given

/-- The usable local bridge from the recursive Survivor is conditional on the
specified model satisfying this node's actual branch equations. -/
theorem evidence_node_of_branch (registry : Registry) (checked : Checked registry)
    (context : Context) (model : Assignment) (root : Occurrence roles)
    (key : Nat) (children : List (Occurrence roles)) (dictionaries : List Payload)
    (survivor : Survivor registry context root key children)
    (declaration : Declaration) (visible : declaration ∈ registry.declarations)
    (valid : DeclarationChecked registry.constructors roles declaration)
    (identity : declaration.id = key)
    (bounds : List (GeneralNominalInspection.Bounds context.state))
    (located : arguments context root = some bounds)
    (branch : BranchModels registry context root declaration valid bounds model)
    (given : All₂ (Evidence registry context model) children dictionaries) :
    Evidence registry context model root (.node key dictionaries) :=
  evidence_node registry context model root key children dictionaries
    (survivor_instance_of_branch registry checked context model root key children survivor
      declaration visible valid identity bounds located branch) given

/-- Source evidence exposes a local instance for the actual payload key. It is
useful for refuting semantic evidence with a concrete source equation. -/
theorem evidence_node_elim (registry : Registry) (context : Context) (model : Assignment)
    (root : Occurrence roles) (key : Nat) (dictionaries : List Payload)
    (evidence : Evidence registry context model root (.node key dictionaries)) :
    ∃ children, Instance registry context model root key children ∧
      All₂ (Evidence registry context model) children dictionaries := by
  have payload := (evidence_iff_payload registry context model root _).mp evidence
  cases payload with
  | node instanceRule children =>
    have convert : ∀ {cs : List (Occurrence roles)} {ds : List Payload}, All₂ (PayloadEvidence (Instance registry context model)) cs ds →
        All₂ (Evidence registry context model) cs ds := by
      intro cs ds given
      induction given with
      | nil => exact .nil
      | cons first rest ih =>
          exact .cons ((evidence_iff_payload registry context model _ _).mpr first) ih
    exact ⟨_, instanceRule, convert children⟩

/-- In particular a terminal raw dictionary needs a genuine terminal source
instance, not just a selected key or an arbitrary empty child proof. -/
theorem evidence_leaf_iff (registry : Registry) (context : Context) (model : Assignment)
    (root : Occurrence roles) (key : Nat) :
    Evidence registry context model root (.node key []) ↔
      Instance registry context model root key [] := by
  constructor
  · intro evidence
    obtain ⟨children, instanceRule, given⟩ := evidence_node_elim registry context model root key [] evidence
    cases given
    exact instanceRule
  · intro instanceRule
    exact evidence_node registry context model root key [] [] instanceRule .nil

/-- Exactly the model-indexed, branch-conditional node rule in the V3 package.
The extra BranchModels argument is deliberate, so this is not EvidenceNode. -/
theorem boundary_node_of_branch (roles : Roles.RoleDecls)
    (remaining : GeneralNominalLocalBoundary.Remaining (GeneralNominalCandidates.vocabulary roles))
    (registry : Registry) (checked : (boundary roles remaining).Checked registry)
    (context : Context) (model : Assignment) (root : Occurrence roles)
    (key : Nat) (children : List (Occurrence roles)) (dictionaries : List Payload)
    (unique : B4Target.Unique (boundary roles remaining) registry context root key children)
    (declaration : Declaration) (visible : declaration ∈ registry.declarations)
    (valid : DeclarationChecked registry.constructors roles declaration)
    (identity : declaration.id = key)
    (bounds : List (GeneralNominalInspection.Bounds context.state))
    (located : arguments context root = some bounds)
    (branch : BranchModels registry context root declaration valid bounds model)
    (given : All₂ (fun child dictionary =>
      (boundary roles remaining).Evidence registry context model child dictionary) children dictionaries) :
    (boundary roles remaining).Evidence registry context model root (.node key dictionaries) :=
  evidence_node_of_branch registry checked.2 context model root key children dictionaries
    unique.1 declaration visible valid identity bounds located branch given

end Yulang.GeneralDictionaryRecursiveEvidence
