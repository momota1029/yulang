import Yulang.GeneralDictionaryCompoundCurrent238
import Yulang.GeneralDictionaryCompoundPointModel238
import Yulang.GeneralNominalVersionedPlans231
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryCompoundPointHead238
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryCompoundSource238
abbrev newBindings := [(0,2,2),(0,2,2)]
abbrev freshName := GeneralDictionaryCompoundPointModel238.nextName
open GeneralDictionaryCompoundPacket238 (actual)
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
open GeneralNominalVersionedPlans231

abbrev context := GeneralDictionaryCompoundCurrent238.currentContext
abbrev packet := GeneralDictionaryCompoundCurrent238.packet
abbrev plan := GeneralDictionaryCompoundCurrent238.plan

structure Values (model : Assignment) : Prop where
  zero : (model 0).1 = foo
  two : (model 2).1 = .emptyRecord
  actual : (model actual).1 = .emptyRecord
  output : (model 4).1 = GeneralDictionaryOptionalOutput229.value
  lower : (model (freshName 0)).1 = .emptyRecord
  upper : (model (freshName 1)).1 = .emptyRecord

variable (allocated reserved ordinary)

theorem bindings_exact : (packet allocated reserved ordinary).bindings = newBindings :=
  GeneralDictionaryCompoundCurrent238.bindings_exact allocated reserved ordinary

theorem capture_exact :
    (GeneralNominalVersionedFrame231.capture (packet allocated reserved ordinary)).inputs 0 =
      (freshName 0,freshName 1) := by
  change (GeneralNominalVersionedAllocation231.capture (context allocated reserved ordinary).state registry root.identity declaration.id (packet allocated reserved ordinary).bindings).inputs 0 = _
  rw [bindings_exact]
  rfl

theorem binder_exact : GeneralNominalVersionedFrame231.binder (plan allocated reserved ordinary) 0 = actual := by
  rw [GeneralNominalVersionedFrame231.binder_eq]
  unfold Plan.binder
  change (if 0 ∈ declaration.outputNames then _ else if _ then _ else _) = actual
  simp only [show ¬ 0 ∈ declaration.outputNames by decide, ite_false]
  have oldCapture : (GeneralNominalPacketSupport.capture (packet allocated reserved ordinary)).inputs 0 =
      (GeneralDictionaryCompoundPacket238.lo,GeneralDictionaryCompoundPacket238.hi) := by
    unfold GeneralNominalPacketSupport.capture
    rw [bindings_exact]
    rfl
  rw [oldCapture]
  have distinct : GeneralDictionaryCompoundPacket238.lo ≠ GeneralDictionaryCompoundPacket238.hi :=
    Ne.symm (GeneralNominalCenteredAllocation.fresh_namespaces (by decide : (1:Nat) ≠ 0))
  simp only [distinct,ite_false]
  rfl

theorem head_schema : (plan allocated reserved ordinary).headSchema = GeneralDictionaryCompoundPacket238.plan.headSchema := rfl

variable {model : Assignment} (values : Values model)

include values in
theorem seen (index : Nat) (small : index < 2) : Observes model (.nominal (.source 0) 0 index) .emptyRecord := by
  refine Observes.nominal (arguments := [.inl .emptyRecord,.inl .emptyRecord]) (.source 0) ?_ ?_
  · change Equivalent (model 0).1 foo
    rw [values.zero]
    exact ⟨subtype_refl _,subtype_refl _⟩
  · rcases (show index = 0 ∨ index = 1 by omega) with rfl | rfl <;> rfl

include values in
theorem observed_value (index : Nat) (small : index < 2)
    (seenValue : Observes model (.nominal (.source 0) 0 index) value) : Equivalent value .emptyRecord :=
  nominal_observation_unique model (.argument (.source 0) 0 index) value .emptyRecord seenValue (seen values index small)

include values in
theorem fit_observed (index : Nat) (small : index < 2)
    (seenValue : Observes model (.nominal (.source 0) 0 index) value) :
    Fits (context allocated reserved ordinary).state model (2,2) value := by
  have equal := observed_value values index small seenValue
  change Subtype (model 2).1 value ∧ Subtype value (model 2).1
  rw [values.two]
  exact ⟨equal.2,equal.1⟩

include values in
theorem raw_projection : ProjectionModels (context allocated reserved ordinary).state
    (report (context allocated reserved ordinary) declaration [(0,0)]) model := by
  rw [GeneralDictionaryCompoundCurrent238.report_exact]
  refine ⟨?_,?_,?_,?_⟩
  · intro anchor member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨⟨_,seen values 0 (by decide)⟩,fun _ h => fit_observed allocated reserved ordinary values 0 (by decide) h⟩
    · cases List.mem_singleton.mp member
      exact ⟨⟨_,seen values 1 (by decide)⟩,fun _ h => fit_observed allocated reserved ordinary values 1 (by decide) h⟩
  · intro test member; cases member
  · intro first one last two _ origin located value h
    rcases List.mem_cons.mp one with rfl | one
    all_goals first | cases List.mem_singleton.mp one | skip
    all_goals cases Option.some.inj located
    all_goals rcases List.mem_cons.mp two with rfl | two
    all_goals first | cases List.mem_singleton.mp two | skip
    all_goals first | exact fit_observed allocated reserved ordinary values 0 (by decide) h | exact fit_observed allocated reserved ordinary values 1 (by decide) h
  · intro first one last two _ a b firstOrigin lastOrigin x y seenX seenY
    rcases List.mem_cons.mp one with rfl | one
    all_goals first | cases List.mem_singleton.mp one | skip
    all_goals cases Option.some.inj firstOrigin
    all_goals rcases List.mem_cons.mp two with rfl | two
    all_goals first | cases List.mem_singleton.mp two | skip
    all_goals cases Option.some.inj lastOrigin
    all_goals
      have ex : Equivalent x .emptyRecord := by first | exact observed_value values 0 (by decide) seenX | exact observed_value values 1 (by decide) seenX
      have ey : Equivalent y .emptyRecord := by first | exact observed_value values 0 (by decide) seenY | exact observed_value values 1 (by decide) seenY
      exact ⟨subtype_trans ex.1 ey.2,subtype_trans ey.1 ex.2⟩

theorem self_checks : PresenceNormalForm.All CommonNominalFullCarrier.model model
    (selfChecks (context allocated reserved ordinary).state (report (context allocated reserved ordinary) declaration [(0,0)])) := by
  rw [GeneralDictionaryCompoundCurrent238.report_exact]
  intro atom member
  simp only [selfChecks,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  all_goals exact subtype_refl _

include values in
theorem merges : PresenceNormalForm.All CommonNominalFullCarrier.model model
    (GeneralNominalVersionedAllocation231.merges (context allocated reserved ordinary).state registry root.identity declaration newBindings) := by
  have pair : PresenceNormalForm.All CommonNominalFullCarrier.model model
      (GeneralNominalAllocation.equations (freshName 0) (.union (.var 2) (.var 2)) ++
        GeneralNominalAllocation.equations (freshName 1) (.inter (.var 2) (.var 2))) := by
    rw [PresenceNormalForm.all_append,GeneralNominalCaptureMerges.equations_exact,
      GeneralNominalCaptureMerges.equations_exact]
    change Equivalent (model (freshName 0)).1 (.union (model 2).1 (model 2).1) ∧
      Equivalent (model (freshName 1)).1 (.inter (model 2).1 (model 2).1)
    rw [values.lower,values.upper,values.two]
    exact ⟨⟨(common_union_is_join _ _ _).mp (subtype_refl _) |>.1,
      (common_union_is_join _ _ _).mpr ⟨subtype_refl _,subtype_refl _⟩⟩,
      ⟨(common_inter_is_meet _ _ _).mpr ⟨subtype_refl _,subtype_refl _⟩,
      (common_inter_is_meet _ _ _).mp (subtype_refl _) |>.1⟩⟩
  change PresenceNormalForm.All CommonNominalFullCarrier.model model (_ ++ _)
  exact (PresenceNormalForm.all_append ..).mpr ⟨pair,pair⟩

include values in
theorem ordinary_holds : Ordinary (packet allocated reserved ordinary) model := by
  unfold Ordinary
  rw [bindings_exact]
  refine ⟨?_,merges allocated reserved ordinary values,self_checks allocated reserved ordinary⟩
  intro first one last two _
  rcases List.mem_cons.mp one with rfl | one
  all_goals first | cases List.mem_singleton.mp one | skip
  all_goals rcases List.mem_cons.mp two with rfl | two
  all_goals first | cases List.mem_singleton.mp two | skip
  all_goals exact subtype_refl _

include values in
theorem head_holds : SchemaHolds (plan allocated reserved ordinary)
    (plan allocated reserved ordinary).headSchema model := by
  rw [head_schema,GeneralDictionaryCompoundPacket238.head_schema]
  constructor
  · intro test member
    cases List.mem_singleton.mp member
    refine ⟨⟨_,.source 0⟩,?_⟩
    intro value h
    cases h
    refine ⟨[.inl .emptyRecord,.inl .emptyRecord],rfl,?_⟩
    rw [values.zero]
    exact ⟨subtype_refl _,subtype_refl _⟩
  · intro entry member
    rcases List.mem_cons.mp member with rfl | member
    all_goals first | cases List.mem_singleton.mp member | skip
    all_goals
      simp only [ite_true]
      refine ⟨?_,⟨_,.source _⟩,?_⟩
      · first | exact ⟨_,seen values 0 (by decide)⟩ | exact ⟨_,seen values 1 (by decide)⟩
      · intro x y seenX seenY
        cases seenY
        rw [binder_exact,values.actual]
        first | exact observed_value values 0 (by decide) seenX | exact observed_value values 1 (by decide) seenX

include values in
theorem head_models (valid : GeneralNominalState.Models (context allocated reserved ordinary).state model) :
    HeadModels (packet allocated reserved ordinary) model :=
  ⟨(private_models_iff ..).mpr ⟨valid,ordinary_holds allocated reserved ordinary values⟩,raw_projection allocated reserved ordinary values⟩

end Yulang.GeneralDictionaryCompoundPointHead238
