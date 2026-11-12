import Yulang.GeneralDictionarySelectedLocality
import Yulang.GeneralDictionaryTreeTransport

/-! Exact source witness transport under finite selected-key footprints. Neither
unselected declarations nor occurrences absent from the witness are constrained.
The payload, child order, multiplicity, declaration keys and model stay fixed. -/
namespace Yulang.GeneralDictionarySelectedTree
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalRecursiveCandidates (Context)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryInspectionTransport
open GeneralDictionarySelectedLocality

def FootprintTree (registry : Registry) (context : Context) (next : Observation context.state)
    (tree : Dictionary roles) : Prop :=
  ∀ occurrence key, (occurrence,key) ∈ observations tree → FootprintFor registry context next occurrence key

theorem footprint_child (registry : Registry) (context : Context) (next : Observation context.state)
    (root : Occurrence roles) (key : Nat) (children : List (Dictionary roles))
    (same : FootprintTree registry context next (.node root key children))
    (child : Dictionary roles) (member : child ∈ children) : FootprintTree registry context next child := by
  intro occurrence selected present
  exact same occurrence selected (List.mem_cons_of_mem _
    (GeneralDictionaryTreeTransport.child_observation children child member _ present))

theorem indexed_of_footprint (registry : Registry) (context : Context) (next : Observation context.state)
    (view : next.view = context.state.view) (model : Assignment)
    (valid : GeneralNominalState.Models (reobserve context next).state model)
    (tree : Dictionary roles)
    (old : Evidence (GeneralDictionaryRecursiveEvidence.Instance registry context model) tree)
    (same : FootprintTree registry context next tree) :
    Evidence (GeneralDictionaryRecursiveEvidence.Instance registry (reobserve context next) model) tree := by
  induction old with
  | @node occurrence key children localRule given ih =>
    refine .node (instance_of_footprint registry context next view model occurrence key _
      (same occurrence key List.mem_cons_self) valid localRule) ?_
    intro child member
    exact ih child member (footprint_child registry context next occurrence key children same child member)

theorem erased_of_footprint (registry : Registry) (context : Context) (next : Observation context.state)
    (view : next.view = context.state.view) (model : Assignment)
    (valid : GeneralNominalState.Models (reobserve context next).state model)
    (root : Occurrence roles) (payload : GeneralDictionaryReadback.Payload) (tree : Dictionary roles)
    (readback : Readback root payload tree)
    (old : Evidence (GeneralDictionaryRecursiveEvidence.Instance registry context model) tree)
    (same : FootprintTree registry context next tree) :
    GeneralDictionaryRecursiveEvidence.Evidence registry (reobserve context next) model root payload :=
  ⟨tree,readback,indexed_of_footprint registry context next view model valid tree old same⟩

theorem indexed_of_occupied (registry : Registry) (context : Context) (next : Observation context.state)
    (view : next.view = context.state.view)
    (refinement : GeneralNominalRefinements.Refines context.state (reobserve context next).state)
    (model : Assignment) (valid : GeneralNominalState.Models (reobserve context next).state model)
    (tree : Dictionary roles)
    (old : Evidence (GeneralDictionaryRecursiveEvidence.Instance registry context model) tree)
    (occupied : ∀ occurrence key, (occurrence,key) ∈ observations tree → OccupiedFor registry context occurrence key) :
    Evidence (GeneralDictionaryRecursiveEvidence.Instance registry (reobserve context next) model) tree :=
  indexed_of_footprint registry context next view model valid tree old
    (fun occurrence key member => footprint_of_occupied registry context next occurrence key refinement
      (occupied occurrence key member))

theorem footprint_equivalent (registry : Registry) (context : Context) (next : Observation context.state)
    (first last : Dictionary roles) (equal : DictionaryEquivalent first last) :
    FootprintTree registry context next first ↔ FootprintTree registry context next last := by
  constructor
  · intro same occurrence key present
    exact same occurrence key ((equivalent_observations equal).mem_iff.mpr present)
  · intro same occurrence key present
    exact same occurrence key ((equivalent_observations equal).mem_iff.mp present)

end Yulang.GeneralDictionarySelectedTree
