import Yulang.GeneralDeclarativeI65I74StructuralWhereBodyReplay428
import Yulang.GeneralDeclarativeI65I75ProjectedRule426

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.StructuralWhere431
open GeneralDeclarativeI65 StructuralWhere427 StructuralWhere428
open CommonRoleOutermostResolver (Tree Dictionary Summarizes)
open GeneralDeclarativeInspect321 (PatternK2)

def AllRaw (s : GeneralDeclarativeI65.State) (q : Request) (root : Nat) : Prop :=
  ∀ d ∈ visible s q, ∃ source code, d.head = [source] ∧ translateWhere427 s source = some code ∧
    ¬ PatternK2 s.current.ordinary root code

/-- Independent admissible source packet. The positive and opposite
ordinary candidates, both complete visible lists, original literal row
and captures are from the same State. No report, model, proof of
classification, child proof, or wire success is an admission premise. -/
structure ActualPair (s : I72.State) (q : Request) where
  pair : ReadPositivePair427 s.core q
  parentRaw : AllRaw s.core q pair.parentRival.found.root
  childRaw : AllRaw s.core pair.original.child pair.childRival.found.root

def ActualPair.parent {s q} (a : ActualPair s q) : Event s q :=
  originalNoOutputEvent427 s.b6 a.pair.frame (a.pair.rootDecl.symm ▸ a.pair.root.head)
    a.pair.rootNoOutput

def ActualPair.child {s q} (a : ActualPair s q) : Event s a.pair.original.child :=
  originalNoOutputEvent427 s.b6 a.pair.childFrame (a.pair.childDecl.symm ▸ a.pair.child.head)
    a.pair.childNoOutput

inductive OriginalLocal (s : I72.State) : (q : Request) → Event s q → Type where
  | parent {q} (p : ActualPair s q) : OriginalLocal s q p.parent
  | child {q} (p : ActualPair s q) : OriginalLocal s p.pair.original.child p.child

def structuralLocal : SourcePrimitives where
  elected s q e needs := needs = [] ∧ Nonempty (OriginalLocal s q e)
  other _ _ _ _ := False

theorem actual_pair_each_opposite_candidate_cannot_displace431
    {s q} (a : ActualPair s q) (m : I72.Model) (fit : I72.Fits s m) :
    (∀ d ∈ visible s.core q, Nonempty (SourceHead s.core q d) → d = a.pair.root.decl) ∧
    (∀ d ∈ visible s.core a.pair.original.child, Nonempty (SourceHead s.core a.pair.original.child d) →
      d = a.pair.child.decl) :=
  ⟨(positive_box_cannot_be_displaced_by_its_checked_rival427
      a.pair.parentRival a.pair.parentCandidates ⟨a.pair.root.head⟩ m fit).2,
    (positive_box_cannot_be_displaced_by_its_checked_rival427
      a.pair.childRival a.pair.originalChildCandidates ⟨a.pair.child.head⟩ m fit).2⟩

theorem scoped_local_law431 : SelectedLaw428 structuralLocal := by
  intro _ _ _ _ chose m fit
  obtain ⟨actual⟩ := chose.2
  cases actual with
  | parent p =>
    exact no_output_ordinary_event_same_model_semantics428 _ _ p.pair.rootNoOutput m fit
  | child p =>
    exact no_output_ordinary_event_same_model_semantics428 _ _ p.pair.childNoOutput m fit

def R15 : SourcePrimitives .withEndpoint where
  elected := (ruleUnion428 RepeatedCenters421.R13 structuralLocal).elected
  other := (ruleUnion428 RepeatedCenters421.R13 structuralLocal).other

theorem named_law431 : SelectedLaw428 R15.named426 :=
  union_local_law428 current_R13_local_law_for_mixed_named_traces428 scoped_local_law431

theorem dictionary_sound_R15 : DictionarySound R15 := by
  intro s q d source m fit
  rcases classification_has_exact_lane_rule426 source with named|endpoint
  · obtain ⟨_,_,⟨trace⟩,summary⟩ := named
    exact actual_named_trace_same_model_dictionary428 named_law431 trace m fit d summary
  · obtain ⟨e,⟨kept⟩,same⟩ := endpoint
    cases same
    exact original_projected_leaf_with_retention_has_dictionary_evidence426 e kept m fit

/-- The former named lane is transported, never reclassified: the
same original Event option, ordered tree, producer needs and all
encoded writes survive. The endpoint lane stays a separate inclusion. -/
theorem previous_named_trace_retains_writes_and_support431 {s q tree event}
    (old : SourceTrace RepeatedCenters421.R13 s q tree event) :
    ∃ now : SourceTrace R15.named426 s q tree event,
      namedTraceWrites428 now = namedTraceWrites428 old ∧
      namedTraceNeeds428 now = namedTraceNeeds428 old := by
  let replay := mapNamedTrace428 (left_named_rule_map428 RepeatedCenters421.R13 structuralLocal) old
  exact ⟨replay.val,replay.property⟩

theorem legacy_R14_classification_included431 {s q v} (old : Classifies EndpointProjection426.R14 s q v) :
    Classifies R15 s q v := by
  rcases classification_has_exact_lane_rule426 old with named|ep
  · obtain ⟨tree,event,⟨trace⟩,summary⟩ := named
    let replay := mapNamedTrace428 (left_named_rule_map428 RepeatedCenters421.R13 structuralLocal) trace
    exact legacy_classification_included426 ⟨tree,event,⟨replay.val⟩,summary⟩
  · exact endpoint_classification_included426 ep

end Yulang.GeneralDeclarativeI65.I72.StructuralWhere431
