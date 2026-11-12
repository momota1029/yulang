import Yulang.GeneralDictionaryInspectionTransport

/-! Reobservation only needs to preserve reports at nodes of the actual source
witness. Exact node multiplicity, keys, child order and payload are retained. -/
namespace Yulang.GeneralDictionaryTreeTransport
open GeneralSourceDictionaries GeneralDictionaryInspectionTransport
open GeneralDeclarations (Registry)
open GeneralNominalRecursiveCandidates (Context)
open GeneralNominalCommonBridge (Assignment)

def PreservesTree (registry : Registry) (context : Context) (next : Observation context.state)
    (tree : Dictionary roles) : Prop :=
  ∀ occurrence key, (occurrence,key) ∈ observations tree → PreservesAt registry context next occurrence

theorem child_observation (children : List (Dictionary roles)) (tree : Dictionary roles)
    (member : tree ∈ children) (entry : Occurrence roles × Nat)
    (present : entry ∈ observations tree) : entry ∈ childObservations children := by
  rw [childObservations_flatten]
  exact List.mem_flatten.mpr ⟨observations tree,List.mem_map.mpr ⟨tree,member,rfl⟩,present⟩

theorem preserves_root (registry : Registry) (context : Context) (next : Observation context.state)
    (root : Occurrence roles) (key : Nat) (children : List (Dictionary roles))
    (same : PreservesTree registry context next (.node root key children)) :
    PreservesAt registry context next root := same root key List.mem_cons_self

theorem preserves_child (registry : Registry) (context : Context) (next : Observation context.state)
    (root : Occurrence roles) (key : Nat) (children : List (Dictionary roles))
    (same : PreservesTree registry context next (.node root key children))
    (child : Dictionary roles) (member : child ∈ children) : PreservesTree registry context next child := by
  intro occurrence selected present
  exact same occurrence selected (List.mem_cons_of_mem _ (child_observation children child member _ present))

theorem indexed_of_reports (registry : Registry) (context : Context) (next : Observation context.state)
    (model : Assignment) (valid : GeneralNominalState.Models (reobserve context next).state model)
    (tree : Dictionary roles)
    (old : Evidence (GeneralDictionaryRecursiveEvidence.Instance registry context model) tree)
    (same : PreservesTree registry context next tree) :
    Evidence (GeneralDictionaryRecursiveEvidence.Instance registry (reobserve context next) model) tree := by
  induction old with
  | @node occurrence key children localRule given ih =>
    refine .node (instance_of_reports registry context next model occurrence key _
      (preserves_root registry context next occurrence key children same) valid localRule) ?_
    intro child member
    exact ih child member (preserves_child registry context next occurrence key children same child member)

/-- The source witness and payload stay literally the same. Reports at demands
absent from this witness are unconstrained. -/
theorem erased_of_witness_reports (registry : Registry) (context : Context) (next : Observation context.state)
    (model : Assignment) (valid : GeneralNominalState.Models (reobserve context next).state model)
    (root : Occurrence roles) (payload : GeneralDictionaryReadback.Payload) (tree : Dictionary roles)
    (readback : Readback root payload tree)
    (old : Evidence (GeneralDictionaryRecursiveEvidence.Instance registry context model) tree)
    (same : PreservesTree registry context next tree) :
    GeneralDictionaryRecursiveEvidence.Evidence registry (reobserve context next) model root payload :=
  ⟨tree,readback,indexed_of_reports registry context next model valid tree old same⟩

/-- Reordering does not strengthen the finite inspection footprint. -/
theorem preserves_equivalent (registry : Registry) (context : Context) (next : Observation context.state)
    (first last : Dictionary roles) (equal : DictionaryEquivalent first last) :
    PreservesTree registry context next first ↔ PreservesTree registry context next last := by
  constructor
  · intro same occurrence key present
    exact same occurrence key ((equivalent_observations equal).mem_iff.mpr present)
  · intro same occurrence key present
    exact same occurrence key ((equivalent_observations equal).mem_iff.mp present)

end Yulang.GeneralDictionaryTreeTransport
