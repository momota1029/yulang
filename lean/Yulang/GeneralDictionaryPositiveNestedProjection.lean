import Yulang.GeneralDictionaryNestedCarrierExample
import Yulang.GeneralNominalBranchProjection
import Yulang.GeneralDictionaryNestedBranchTransport

/-! Positive nonpoint nested inspection with a repeated capture. Unlike the
prior Models+Finished regression, both nominal arms have the same arbitrary
leaf value and the full projection judgment is proved. This module alone does
not assert an operational refresh or candidate materialization. -/
set_option linter.unusedSimpArgs false
namespace Yulang.GeneralDictionaryPositiveNestedProjection
open GeneralNominalRecursiveInspection GeneralNominalProvenanceSource
open GeneralDictionaryNestedRefinementExamples (query bounds nested_finished)
open CommonNominalFullCarrier
abbrev leftParent : GeneralNominalProjections.Ref := .argument (.source 0) 0 0
abbrev rightParent : GeneralNominalProjections.Ref := .argument (.source 3) 0 0
abbrev leftLeaf : GeneralNominalProjections.Ref := .argument leftParent 0 0
abbrev rightLeaf : GeneralNominalProjections.Ref := .argument rightParent 0 0
abbrev result := inspect state query bounds none

theorem parents_observed (a u : Ty) :
 Observes (model a a u) (embed leftParent) (nominal 0 [.inl a]) ∧
 Observes (model a a u) (embed rightParent) (nominal 0 [.inl a]) := by
 constructor
 · exact .nominal (.source 0) ⟨subtype_refl _,subtype_refl _⟩ rfl
 · exact .nominal (.source 3) ⟨subtype_refl _,subtype_refl _⟩ rfl

theorem leaves_observed (a u : Ty) :
 Observes (model a a u) (embed leftLeaf) a ∧
 Observes (model a a u) (embed rightLeaf) a := by
 constructor
 · exact .nominal (parents_observed a u).1 ⟨subtype_refl _,subtype_refl _⟩ rfl
 · exact .nominal (parents_observed a u).2 ⟨subtype_refl _,subtype_refl _⟩ rfl

theorem captures : result.captures =
 [⟨7,(2,2),some (embed leftLeaf)⟩,⟨7,(5,5),some (embed rightLeaf)⟩] := by
 simp [result,query,bounds,inspect,inspectMany,Report.visit,Report.append,typeArguments,
  state,entries,listDescriptor,boxDescriptor,embed,leftParent,rightParent,leftLeaf,rightLeaf]
 repeat first
  | rw [inspectMany.eq_def]
  | rw [inspect.eq_def]
  | simp [Report.visit,Report.append,typeArguments,state,entries,listDescriptor,boxDescriptor,embed,leftParent,rightParent,leftLeaf,rightLeaf]
 all_goals decide +kernel

theorem anchors : result.anchors =
 [(embed leftParent,(1,1)),(embed leftLeaf,(2,2)),
  (embed rightParent,(4,4)),(embed rightLeaf,(5,5))] := by
 simp [result,query,bounds,inspect,inspectMany,Report.visit,Report.append,typeArguments,
  state,entries,listDescriptor,boxDescriptor,embed,leftParent,rightParent,leftLeaf,rightLeaf]
 repeat first
  | rw [inspectMany.eq_def]
  | rw [inspect.eq_def]
  | simp [Report.visit,Report.append,typeArguments,state,entries,listDescriptor,boxDescriptor,embed,leftParent,rightParent,leftLeaf,rightLeaf]
 all_goals decide +kernel

theorem tests : result.tests =
 [(embed leftParent,.nominal 0 1),(embed rightParent,.nominal 0 1)] := by
 simp [result,query,bounds,inspect,inspectMany,Report.visit,Report.append,typeArguments,
  state,entries,listDescriptor,boxDescriptor,embed,leftParent,rightParent,leftLeaf,rightLeaf]
 repeat first
  | rw [inspectMany.eq_def]
  | rw [inspect.eq_def]
  | simp [Report.visit,Report.append,typeArguments,state,entries,listDescriptor,boxDescriptor,embed,leftParent,rightParent,leftLeaf,rightLeaf]
 all_goals decide +kernel

private theorem anchor_ok (m : GeneralNominalCommonBridge.Assignment)
 (ref : GeneralNominalProjections.Ref) (slot : Fin state.base.slots) (value : Ty)
 (observed : Observes m (embed ref) value)
 (equal : Equivalent (m (state.base.source slot)).1 value) :
 (∃ actual, Observes m (embed ref) actual) ∧
 ∀ actual, Observes m (embed ref) actual → Fits state m (slot,slot) actual := by
 refine ⟨⟨value,observed⟩,?_⟩
 intro actual seen
 have same := nominal_observation_unique m ref value actual observed seen
 exact ⟨subtype_trans equal.1 same.1,subtype_trans same.2 equal.2⟩

private theorem eq_trans {a b c : Ty} (one : Equivalent a b) (two : Equivalent b c) : Equivalent a c :=
 ⟨subtype_trans one.1 two.1,subtype_trans two.2 one.2⟩

private theorem leaf_fit (a u : Ty) (ref : GeneralNominalProjections.Ref)
 (seen : Observes (model a a u) (embed ref) a) (actual : Ty)
 (observed : Observes (model a a u) (embed ref) actual)
 (slot : Fin state.base.slots) (equal : (model a a u (state.base.source slot)).1 = a) :
 Fits state (model a a u) (slot,slot) actual := by
 have same := nominal_observation_unique _ ref a actual seen observed
 change Subtype _ actual ∧ Subtype actual _
 rw [equal]
 exact same

theorem projection (a u : Ty) : ProjectionModels state result (model a a u) := by
 refine ⟨?_,?_,?_,?_⟩
 · intro anchor member
   rw [anchors] at member
   simp only [List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl | rfl | rfl | rfl
   · exact anchor_ok _ leftParent 1 _ (parents_observed a u).1 ⟨subtype_refl _,subtype_refl _⟩
   · exact anchor_ok _ leftLeaf 2 _ (leaves_observed a u).1 ⟨subtype_refl _,subtype_refl _⟩
   · exact anchor_ok _ rightParent 4 _ (parents_observed a u).2 ⟨subtype_refl _,subtype_refl _⟩
   · exact anchor_ok _ rightLeaf 5 _ (leaves_observed a u).2 ⟨subtype_refl _,subtype_refl _⟩
 · intro test member actual seen
   rw [tests] at member
   simp only [List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl | rfl
   · exact ⟨[.inl a],rfl,nominal_observation_unique _ leftParent actual _ seen (parents_observed a u).1⟩
   · exact ⟨[.inl a],rfl,nominal_observation_unique _ rightParent actual _ seen (parents_observed a u).2⟩
 · intro first hf last hl same ref origin actual seen
   rw [captures] at hf hl
   simp only [List.mem_cons,List.not_mem_nil,or_false] at hf hl
   rcases hf with rfl | rfl <;> rcases hl with rfl | rfl
   all_goals cases Option.some.inj origin
   · exact leaf_fit a u leftLeaf (leaves_observed a u).1 actual seen 2 rfl
   · exact leaf_fit a u leftLeaf (leaves_observed a u).1 actual seen 5 rfl
   · exact leaf_fit a u rightLeaf (leaves_observed a u).2 actual seen 2 rfl
   · exact leaf_fit a u rightLeaf (leaves_observed a u).2 actual seen 5 rfl
 · intro first hf last hl same one two hOne hTwo x y seenX seenY
   rw [captures] at hf hl
   simp only [List.mem_cons,List.not_mem_nil,or_false] at hf hl
   rcases hf with rfl | rfl <;> rcases hl with rfl | rfl
   all_goals cases Option.some.inj hOne; cases Option.some.inj hTwo
   all_goals
     first
     | exact eq_trans (nominal_observation_unique _ leftLeaf x a seenX (leaves_observed a u).1)
         (nominal_observation_unique _ leftLeaf a y (leaves_observed a u).1 seenY)
     | exact eq_trans (nominal_observation_unique _ leftLeaf x a seenX (leaves_observed a u).1)
         (nominal_observation_unique _ rightLeaf a y (leaves_observed a u).2 seenY)
     | exact eq_trans (nominal_observation_unique _ rightLeaf x a seenX (leaves_observed a u).2)
         (nominal_observation_unique _ leftLeaf a y (leaves_observed a u).1 seenY)
     | exact eq_trans (nominal_observation_unique _ rightLeaf x a seenX (leaves_observed a u).2)
         (nominal_observation_unique _ rightLeaf a y (leaves_observed a u).2 seenY)

theorem positive (a u : Ty) :
 GeneralNominalState.Models state (model a a u) ∧ Finished result ∧
 ProjectionModels state result (model a a u) ∧ bounds.1 ≠ bounds.2 :=
 ⟨source_models _ _ _,nested_finished,projection _ _,by decide +kernel⟩

theorem refined_projection (after : GeneralNominalState.State)
 (refinement : GeneralNominalRefinements.Refines state after) (a u : Ty) :
 ProjectionModels after
  (inspect after query (GeneralDictionaryNestedRefinement.mapBounds refinement.base.embed bounds) none)
  (model a a u) := by
 rw [GeneralDictionaryNestedRefinementExamples.arbitrary_refinement after refinement]
 exact (GeneralDictionaryNestedBranchTransport.projection_map refinement result _).mpr (projection a u)

theorem observed_leaves_general (a b u : Ty) :
 Observes (model a b u) (embed leftLeaf) a ∧
 Observes (model a b u) (embed rightLeaf) b := by
 constructor
 · exact .nominal (.nominal (.source 0) ⟨subtype_refl _,subtype_refl _⟩ rfl)
     ⟨subtype_refl _,subtype_refl _⟩ rfl
 · exact .nominal (.nominal (.source 3) ⟨subtype_refl _,subtype_refl _⟩ rfl)
     ⟨subtype_refl _,subtype_refl _⟩ rfl

theorem projection_requires_equal_leaves (a b u : Ty)
 (valid : ProjectionModels state result (model a b u)) : Equivalent a b := by
 apply valid.2.2.2 ⟨7,(2,2),some (embed leftLeaf)⟩
   (by rw [captures]; exact List.mem_cons_self) ⟨7,(5,5),some (embed rightLeaf)⟩
   (by rw [captures]; simp) rfl (embed leftLeaf) (embed rightLeaf) rfl rfl a b
 · exact (observed_leaves_general a b u).1
 · exact (observed_leaves_general a b u).2

end Yulang.GeneralDictionaryPositiveNestedProjection
