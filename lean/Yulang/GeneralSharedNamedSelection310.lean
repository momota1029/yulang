import Yulang.GeneralSharedNamedNodes310
import Yulang.GeneralNominalVersionedDiagnosticLaws232

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 26500
set_option maxHeartbeats 15000000
namespace Yulang.GeneralSharedNamedSelection310
open GeneralSharedNamedSource310 (compiled registry root impl checked)
open GeneralSharedNamedMerge310 (merged inhabited reached aliases)
open GeneralSharedNamedCurrent310 (current_parent current_leaf receiver_classes)
open GeneralSharedNamedNodes310
open GeneralDeclarationExamples (roles)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedCandidates231 (Survivor Unique)
open GeneralNominalVersionedPlans231 (Holds)
open GeneralNominalVersionedDiagnostic232 (AdministrativeReady)
open GeneralNominalVersionedMixedSourceBoundary234 (Local)
open GeneralNominalExamples (model)
open GeneralNominalCenters (SameInputs Site)
open GeneralNominalCenteredHeadMatEffects (Ready)
open GeneralNominalVersionedEffects231 (ClassEffects)
open GeneralDeclarations (Declaration)

theorem registered (n : Node) : site n ∈ merged.core.sites := (current_frame n).center_recorded

theorem merge_already {a b : Site roles} (one : a ∈ merged.core.sites) (two : b ∈ merged.core.sites)
    (h : SameInputs (Models merged) a b) :
    GeneralNominalSaturationState.Alias merged.core.erased.current a.occurrence.identity b.occurrence.identity := by
  obtain ⟨i,rfl⟩ := center_known a one
  obtain ⟨j,rfl⟩ := center_known b two
  have edge : GeneralNominalSaturationState.Alias merged.core.erased.current
      (focus .low).identity (focus .high).identity :=
    .edge (aliases ▸ List.mem_singleton_self _)
  cases i <;> cases j <;> first | exact .refl _ | exact edge | exact .symm edge | cases h.1

theorem admin (n : Node) : AdministrativeReady merged (focus n) :=
  ⟨⟨site n,registered n,rfl⟩,fun _ one _ _ two h => merge_already one two h⟩

theorem recorded_decl (n : Node) (d : Declaration) (found : d ∈ compiled.declarations)
    (rightRole : d.role = (focus n).demand.role) : d = (plan n).packet.declaration := by
  cases n
  · exact GeneralSharedNamedPreinstall310.member_parent found rightRole
  · exact GeneralSharedNamedLeafFrame310.declaration_eq .low d found rightRole
  · exact GeneralSharedNamedLeafFrame310.declaration_eq .high d found rightRole

theorem known (n : Node) : ¬ GeneralNominalState.RootPending merged.core.erased.current.context.state
    (GeneralNominalVersionedCandidates231.inputs (focus n)).demand := by
  cases n
  · exact GeneralSharedNamedPreinstall310.known
  · exact GeneralSharedNamedLeafFrame310.known .low
  · exact GeneralSharedNamedLeafFrame310.known .high

theorem safe (n : Node) : B4TargetV8.SafeKnown (GeneralNominalVersionedDiagnostic232.boundary roles) compiled merged (focus n) := by
  refine ⟨known n,?_,?_,?_⟩
  · rintro (raw | (⟨i,cycle⟩ | ⟨s,_,_,i,cycle⟩))
    · obtain ⟨_,_,_,slot,_,cycle⟩ := raw
      exact GeneralRebaseDisplaySafety276.raw_acyclic merged.core.erased.current.context.state rfl inhabited.1.1 slot cycle
    · exact GeneralRebaseDisplaySafety276.semantic inhabited _ cycle
    · exact GeneralRebaseDisplaySafety276.semantic inhabited _ cycle
  · rintro (raw | ⟨p,_,entry,_,cycle⟩)
    · obtain ⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩ := raw
      exact GeneralRebaseDisplaySafety276.raw_acyclic merged.core.erased.current.context.state rfl inhabited.1.1 visited.1 cycle
    · exact GeneralRebaseDisplaySafety276.semantic inhabited _ cycle
  · rintro (⟨_,d,visible,role,_,unprepared⟩ | pending)
    · cases recorded_decl n d visible role
      exact unprepared (current_frame n).prepared
    · exact pending (admin n)

theorem survivor (n : Node) : Survivor compiled merged.core.erased.current.context (focus n) (key n) ((links n).map focus) := by
  rw [← child_list n]
  exact GeneralNominalVersionedMixedFrameSelection235.frame_survivor (current_frame n) (known n)

theorem unique (n : Node) : Unique compiled merged.core.erased.current.context (focus n) (key n) ((links n).map focus) := by
  refine ⟨survivor n,?_⟩
  intro other kids h
  have c := h
  obtain ⟨_,d,seen,check,tag,role,_⟩ := c
  cases recorded_decl n d seen role
  have eq : other = key n := tag.symm
  subst other
  exact ⟨rfl,GeneralNominalVersionedCandidates231.survivor_children_functional
    GeneralSharedNamedPreinstall310.compiled_checked h (survivor n)⟩

theorem certificate (n : Node) (m : Assignment) (valid : Models merged m) :
    GeneralNominalVersionedEvidence231.Certificate compiled merged.core m (focus n) (key n)
      ((links n).map focus) (plan n) := by
  cases n
  · exact GeneralSharedNamedCurrent310.parent_certificate m valid
  · exact GeneralSharedNamedCurrent310.receiver_certificate .low m valid
  · exact GeneralSharedNamedCurrent310.receiver_certificate .high m valid

theorem ready (n : Node) : Ready merged.core (focus n) (plan n) :=
  GeneralNominalVersionedMixedReady235.ready ⟨rfl,checked⟩ reached (current_frame n)

theorem classes (n : Node) (m : Assignment) (valid : Models merged m) :
    ClassEffects merged.core (focus n) (plan n) m := by
  cases n
  · have effect := (valid.2.2 GeneralSharedNamedPreinstall310.effect List.mem_cons_self).2
    have first := (GeneralNominalVersionedReplayEffects232.replay_class_effects_iff ..).mpr effect
    exact (GeneralNominalVersionedReplayEffects232.class_effects_iff [] GeneralSharedNamedMerge310.added []
       merged.core root GeneralSharedNamedEvidence310.parentPlan m).mpr first
  · exact receiver_classes .low m valid
  · exact receiver_classes .high m valid

theorem all_equal (m : Assignment) (valid : Models merged m) (d)
    (present : GeneralNominalVersionedMergedConflict232.Old.Registered merged.legacy d) :
    GeneralNominalCenteredHeadOutputs.EqualOutputs merged.core d m := by
  obtain ⟨s,seen,eq⟩ := present
  obtain ⟨n,h⟩ := raw_known s seen
  subst s
  change focus n = d at eq
  exact eq ▸ (classes n m valid).2

theorem no_merged (n : Node) : ¬ GeneralNominalVersionedMergedConflict232.MergedOutputConflict merged (focus n) :=
  GeneralNominalVersionedMergedConflict232.models_exclude_conflict inhabited
    (all_equal _ inhabited) (classes n _ inhabited).2

theorem actual_pick (n : Node) : Local registry merged (focus n) (.selected (key n) ((links n).map focus)) := by
  apply GeneralNominalVersionedMixedSourceBoundary234.local_iff.mpr
  apply GeneralNominalVersionedMixedBoundary234.local_iff.mpr
  exact GeneralNominalVersionedDiagnosticLaws232.selected_of_model (safe n) (unique n) inhabited
    (current_frame n) (ready n) (certificate n _ inhabited).packet (classes n _ inhabited) (no_merged n)

end Yulang.GeneralSharedNamedSelection310
