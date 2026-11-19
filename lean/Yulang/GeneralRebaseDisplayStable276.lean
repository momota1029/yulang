import Yulang.GeneralRebaseDisplaySelection276
import Yulang.GeneralRebaseDisplaySeparators276

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28200
set_option maxHeartbeats 9900000
namespace Yulang.GeneralRebaseDisplayStable276
open GeneralNominalExamples (registry displayRoot displayChild intDisplay state listDescriptor model)
open GeneralDeclarationExamples (roles display)
open GeneralNominalNonleafPlan193 (centerSite)
open GeneralRebaseDisplayFrame276 (after no_new_request classes_empty)
open GeneralRebaseDisplayChild276 (context)
open GeneralRebaseDisplayEndpoint276 (raw_for centers_for generates_only wrong_parent_prepared wrong_child_prepared)
open GeneralRebaseDisplayEvidence276 (raw_sites center_sites)
open GeneralRebaseDisplaySelection276 (parent child parent_frame child_frame no_cross_merge no_reverse_merge)
open GeneralNominalVersionedMixedKernel234 (Step Stable Committed Installable)
open GeneralNominalVersionedJournal232 (Effect Models)
open GeneralNominalCenters GeneralSourceDictionaries

theorem point_closed : GeneralNominalReobservationSteps.PointClosed context.state := by
 intro slot descriptor recorded
 change (if slot = (0 : Fin 2) then some listDescriptor else none) = some descriptor at recorded
 split at recorded
 · cases Option.some.inj recorded
   intro parameter member
   change parameter ∈ [GeneralNominalState.Parameter.type ((1 : Fin 2),(1 : Fin 2))] at member
   cases List.mem_singleton.mp member
   rfl
 · cases recorded

theorem committed_parent : Committed after parent :=
 GeneralNominalVersionedCommitted232.replay_committed GeneralRebaseDisplayFrame276.before GeneralRebaseDisplayFrame276.effect

theorem committed_child : Committed after child := by
 refine ⟨fun m valid => ⟨GeneralRebaseDisplayChild276.holds m valid,classes_empty
   (no_new_request displayChild) child m⟩,?_⟩
 intro next seen
 rw [GeneralRebaseDisplayChild276.no_children] at seen
 cases seen

theorem framed_parent {p : Plan roles} {key : Nat}
 (frame : GeneralNominalVersionedEvidence231.Frame registry after.core displayRoot key p) : p = parent := by
 apply GeneralRebaseScopedFrame276.same_frame frame parent_frame
 · exact GeneralRebaseScopedFrame276.declaration_for_focus frame wrong_parent_prepared
 · exact raw_for frame.raw_recorded frame.occurrence_eq parent_frame.raw_recorded rfl
 · exact centers_for frame.center_recorded (GeneralRebaseScopedFrame276.frame_input_occurrence frame) parent_frame.center_recorded rfl

theorem framed_child {p : Plan roles} {key : Nat}
 (frame : GeneralNominalVersionedEvidence231.Frame registry after.core displayChild key p) : p = child := by
 apply GeneralRebaseScopedFrame276.same_frame frame child_frame
 · have declaration := frame.visible
   simp only [List.mem_cons,List.not_mem_nil,or_false] at declaration
   rcases declaration with good|wrong|different
   · exact good
   · exact False.elim (wrong_child_prepared (wrong ▸ frame.prepared))
   · have sameRole := frame.role_eq
     rw [different] at sameRole
     cases sameRole
 · exact raw_for frame.raw_recorded frame.occurrence_eq child_frame.raw_recorded rfl
 · exact centers_for frame.center_recorded (GeneralRebaseScopedFrame276.frame_input_occurrence frame) child_frame.center_recorded rfl

theorem no_install (candidate : Effect roles) (enabled : Installable registry after candidate)
 (scope : candidate.plan.packet.site.occurrence = displayRoot ∨ candidate.plan.packet.site.occurrence = displayChild) :
 Committed after candidate.plan := by
 have frame := candidate.frame
 rw [enabled.registry_eq,enabled.snapshot_eq] at frame
 rcases scope with p|c
 · rw [p] at frame
   rw [framed_parent frame]
   exact committed_parent
 · rw [c] at frame
   rw [framed_child frame]
   exact committed_child

theorem recorded {focus : Occurrence roles} (scope : focus = displayRoot ∨ focus = displayChild) :
 ∃ site ∈ after.core.erased.current.sites, site.occurrence = focus := by
 rcases scope with rfl|rfl
 · exact ⟨_,raw_sites ▸ List.mem_cons_self,rfl⟩
 · exact ⟨centerSite.observed,raw_sites ▸ List.mem_cons_of_mem _ List.mem_cons_self,rfl⟩

theorem halted (next : GeneralNominalVersionedJournal232.State roles) : ¬ Step registry displayRoot after next := by
 rintro ⟨focus,generated,operation⟩
 have scope := generates_only generated
 cases operation with
 | administrative action =>
   cases action with
   | enqueue _ absent =>
     obtain ⟨site,held,eq⟩ := recorded scope
     exact absent site held eq
   | refresh context cert id tracked unknown known =>
     exact GeneralNominalVersionedMixedTerminalStable234.no_refresh GeneralRebaseDisplaySeparators276.headless cert
       tracked unknown known
   | equate first last a b same novel =>
     exact novel (GeneralRebaseDisplaySeparators276.equality_closed first last a b same)
   | reobserve revision _ improves =>
     exact GeneralNominalReobservationSteps.pointClosed_no_revision point_closed revision improves
 | refresh focus context cert id tracked unknown known =>
   exact GeneralNominalVersionedMixedTerminalStable234.no_refresh GeneralRebaseDisplaySeparators276.headless cert
     tracked unknown known
 | install candidate enabled novel => exact novel (no_install candidate enabled scope)
 | merge first last a b same novel =>
   rw [center_sites] at a b
   simp only [List.mem_cons,List.not_mem_nil,or_false] at a b
   rcases a with rfl|rfl <;> rcases b with rfl|rfl
   · exact novel (.refl _)
   · exact no_cross_merge same
   · exact no_reverse_merge same
   · exact novel (.refl _)

theorem stable_parent : Stable registry after displayRoot :=
 (GeneralNominalVersionedMixedKernel234.closure halted).1

theorem stable_child : Stable registry after displayChild :=
 (GeneralNominalVersionedMixedKernel234.closure halted).2 _ GeneralRebaseDisplayFrame276.generated

end Yulang.GeneralRebaseDisplayStable276
