import Yulang.GeneralPositiveForkPayload309
import Yulang.GeneralNominalVersionedDiagnosticLaws232

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 26500
set_option maxHeartbeats 15000000
namespace Yulang.GeneralPositiveForkSelection309
open GeneralPositiveForkSource309 (compiled registry root parent)
open GeneralPositiveForkInstall309 (after inhabited)
open GeneralPositiveForkNodes309
open GeneralPositiveForkLeaf309 (ctx)
open GeneralPositiveForkEvidence309 (parentPlan parent_ready leaf_ready)
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

theorem registered (n : Node) : site n ∈ after.core.sites := (current_frame n).center_recorded

theorem merge_already {a b : Site roles} (one : a ∈ after.core.sites) (two : b ∈ after.core.sites)
    (h : SameInputs (Models after) a b) :
    GeneralNominalSaturationState.Alias after.core.erased.current a.occurrence.identity b.occurrence.identity := by
  obtain ⟨i,rfl⟩ := center_known a one
  obtain ⟨j,rfl⟩ := center_known b two
  cases role_injective h.1
  exact .refl _

theorem admin (n : Node) : AdministrativeReady after (focus n) :=
  ⟨⟨site n,registered n,rfl⟩,fun _ one _ _ two h => merge_already one two h⟩

theorem recorded_decl (n : Node) (d : Declaration) (found : d ∈ compiled.declarations)
    (rightRole : d.role = (focus n).demand.role) : d = (plan n).packet.declaration := by
  cases n
  · exact GeneralPositiveForkPreinstall309.member_parent found rightRole
  · exact GeneralPositiveForkLeafFrame309.declaration_eq .low d found rightRole
  · exact GeneralPositiveForkLeafFrame309.declaration_eq .high d found rightRole

theorem known (n : Node) : ¬ GeneralNominalState.RootPending ctx.state
    (GeneralNominalVersionedCandidates231.inputs (focus n)).demand := by
  cases n
  · exact GeneralPositiveForkPreinstall309.known
  · exact GeneralPositiveForkLeafFrame309.known .low
  · exact GeneralPositiveForkLeafFrame309.known .high

theorem safe (n : Node) : B4TargetV8.SafeKnown (GeneralNominalVersionedDiagnostic232.boundary roles) compiled after (focus n) := by
  refine ⟨known n,?_,?_,?_⟩
  · rintro (raw | (⟨i,cycle⟩ | ⟨s,_,_,i,cycle⟩))
    · obtain ⟨_,_,_,slot,_,cycle⟩ := raw
      exact GeneralRebaseDisplaySafety276.raw_acyclic ctx.state rfl inhabited.1.1 slot cycle
    · exact GeneralRebaseDisplaySafety276.semantic inhabited _ cycle
    · exact GeneralRebaseDisplaySafety276.semantic inhabited _ cycle
  · rintro (raw | ⟨p,_,entry,_,cycle⟩)
    · obtain ⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩ := raw
      exact GeneralRebaseDisplaySafety276.raw_acyclic ctx.state rfl inhabited.1.1 visited.1 cycle
    · exact GeneralRebaseDisplaySafety276.semantic inhabited _ cycle
  · rintro (⟨_,d,visible,role,_,unprepared⟩ | pending)
    · cases recorded_decl n d visible role
      exact unprepared (current_frame n).prepared
    · exact pending (admin n)

theorem survivor (n : Node) : Survivor compiled ctx (focus n) (key n) ((links n).map focus) := by
  cases n with
  | low => exact (GeneralPositiveForkLeafFrame309.unique .low _ inhabited).1
  | high => exact (GeneralPositiveForkLeafFrame309.unique .high _ inhabited).1
  | parent =>
    have f := current_frame .parent
    exact ⟨known .parent,parent,f.visible,(plan .parent).packet.checked,rfl,f.role_eq,
      (plan .parent).packet.bounds,f.located,f.prepared,(child_list .parent).symm⟩

theorem unique (n : Node) : Unique compiled ctx (focus n) (key n) ((links n).map focus) := by
  refine ⟨survivor n,?_⟩
  intro other kids h
  have c := h
  obtain ⟨_,d,seen,check,tag,role,_⟩ := c
  cases recorded_decl n d seen role
  have eq : other = key n := tag.symm
  subst other
  exact ⟨rfl,GeneralNominalVersionedCandidates231.survivor_children_functional
    GeneralPositiveForkPreinstall309.compiled_checked h (survivor n)⟩

theorem holds (n : Node) (m : Assignment) (valid : Models after m) : Holds (plan n) m := by
  cases n
  · exact GeneralNominalVersionedInstalledEvidence233.replay_holds valid
  · exact GeneralPositiveForkLeaf309.holds .low m valid
  · exact GeneralPositiveForkLeaf309.holds .high m valid

theorem ready (n : Node) : Ready after.core (focus n) (plan n) := by
  cases n
  · exact parent_ready
  · exact leaf_ready .low
  · exact leaf_ready .high

theorem classes (n : Node) (m : Assignment) (valid : Models after m) :
    ClassEffects after.core (focus n) (plan n) m := by
  cases n
  · exact GeneralNominalVersionedInstalledEvidence233.class_effects valid
  · exact GeneralRebaseDisplayFrame276.classes_empty (GeneralPositiveForkEvidence309.side_requests .low) _ _
  · exact GeneralRebaseDisplayFrame276.classes_empty (GeneralPositiveForkEvidence309.side_requests .high) _ _

theorem no_merged (n : Node) : ¬ GeneralNominalVersionedMergedConflict232.MergedOutputConflict after (focus n) := by
  rintro ⟨⟨a,b,alias,_,_⟩,_⟩
  change (a,b) ∈ ([] : List (Nat × Nat)) at alias
  cases alias

theorem actual_pick (n : Node) : Local registry after (focus n) (.selected (key n) ((links n).map focus)) := by
  apply GeneralNominalVersionedMixedSourceBoundary234.local_iff.mpr
  apply GeneralNominalVersionedMixedBoundary234.local_iff.mpr
  exact GeneralNominalVersionedDiagnosticLaws232.selected_of_model (safe n) (unique n) inhabited
    (current_frame n) (ready n) (holds n _ inhabited) (classes n _ inhabited) (no_merged n)

end Yulang.GeneralPositiveForkSelection309
