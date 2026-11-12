import Yulang.GeneralDictionaryKeyedRevision
import Yulang.GeneralDictionaryJournalTree

/-! Complete finite dictionaries for the key-local actual revision trace.
Syntactic journal coverage and accessibility remain explicit: stable selection
alone does not imply coverage, as cycle139's counterexample demonstrates. -/
namespace Yulang.GeneralDictionaryKeyedJournalTree
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralDictionaryJournalTree
open GeneralDictionaryCurrentJournal (Current)
open GeneralNominalReobservationSteps (Revision Certified)
variable {roles : Roles.RoleDecls}

/-- A fixed syntactic dictionary works uniformly in every model of a Current
journal. The dictionary is not selected separately for each model. -/
theorem indexed_of_current (registry : Registry) (state : State roles)
    (current : Current registry state) (tree : Dictionary roles)
    (recorded : Evidence (Recorded state) tree)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model) :
    Evidence (GeneralDictionaryRecursiveEvidence.Instance registry state.context model) tree := by
  apply evidence_mono (Recorded state) _ (fun site key children recorded => ?_) recorded
  obtain ⟨packet,present,rfl,rfl,rfl⟩ := recorded
  exact current packet present model valid

theorem uniform_of_current (registry : Registry) (state : State roles) (root : Occurrence roles)
    (current : Current registry state) (covered : Covered state root)
    (accessible : Acc (Child state) root) :
    ∃ tree : Dictionary roles, tree.root = root ∧ Evidence (Recorded state) tree ∧
      ∀ model, Models state model →
        GeneralDictionaryRecursiveEvidence.Evidence registry state.context model root (erase tree) := by
  obtain ⟨tree,same,recorded⟩ := recorded_tree state root covered accessible
  exact ⟨tree,same,recorded,fun model valid =>
    ⟨tree,⟨same,rfl⟩,indexed_of_current registry state current tree recorded model valid⟩⟩

theorem uniform_after_trace (registry : Registry) (root : Occurrence roles)
    (context : GeneralNominalCandidates.Context) (after : State roles)
    (path : B4Target.Steps (GeneralDictionaryKeyedRevision.Step registry root)
      (initial context root) after)
    (covered : Covered after root) (accessible : Acc (Child after) root) :
    ∃ tree : Dictionary roles, tree.root = root ∧ Evidence (Recorded after) tree ∧
      ∀ model, Models after model →
        GeneralDictionaryRecursiveEvidence.Evidence registry after.context model root (erase tree) :=
  uniform_of_current registry after root
    (GeneralDictionaryKeyedRevision.initial_trace_current registry root context after path) covered accessible

@[simp] theorem revision_recorded (before : State roles) (revision : Revision before) :
    Recorded revision.result = Recorded before := rfl

@[simp] theorem revision_child (before : State roles) (revision : Revision before) :
    Child revision.result = Child before := rfl

theorem revision_reach (before : State roles) (revision : Revision before)
    (root site : Occurrence roles) : Reach revision.result root site ↔ Reach before root site := by
  constructor
  · intro reached
    induction reached with
    | root => exact .root
    | child _ edge ih => exact .child ih edge
  · intro reached
    induction reached with
    | root => exact .root
    | child _ edge ih => exact .child ih edge

@[simp] theorem revision_covered (before : State roles) (revision : Revision before) (root : Occurrence roles) :
    Covered revision.result root ↔ Covered before root := by
  constructor
  · intro covered site reached
    exact covered site ((revision_reach before revision root site).mpr reached)
  · intro covered site reached
    exact covered site ((revision_reach before revision root site).mp reached)

/-- One source-indexed tree, not just an equivalent payload, is sound before and
 after certified point replacement. No branch-model choice changes. -/
theorem same_dictionary_revision (registry : Registry) (before : State roles)
    (root : Occurrence roles) (revision : Revision before)
    (certificate : Certified revision)
    (footprint : GeneralDictionaryKeyedRevision.RecordedFootprint registry before revision)
    (current : Current registry before) (covered : Covered before root)
    (accessible : Acc (Child before) root) :
    ∃ tree : Dictionary roles, tree.root = root ∧ Evidence (Recorded before) tree ∧
      ∀ model, Models before model →
        GeneralDictionaryRecursiveEvidence.Evidence registry before.context model root (erase tree) ∧
        GeneralDictionaryRecursiveEvidence.Evidence registry revision.result.context model root (erase tree) := by
  obtain ⟨tree,same,recorded⟩ := recorded_tree before root covered accessible
  have next := GeneralDictionaryKeyedRevision.revision_footprint_current registry before revision certificate footprint current
  refine ⟨tree,same,recorded,?_⟩
  intro model valid
  exact ⟨⟨tree,⟨same,rfl⟩,indexed_of_current registry before current tree recorded model valid⟩,
    ⟨tree,⟨same,rfl⟩,indexed_of_current registry revision.result next tree recorded model
      ((certificate.exact model).mpr valid)⟩⟩
end Yulang.GeneralDictionaryKeyedJournalTree
