import Yulang.GeneralPositiveForkSelection309
import Yulang.GeneralNominalVersionedMixedTerminalStable234

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 26500
set_option maxHeartbeats 15000000
namespace Yulang.GeneralPositiveForkHalt309
open GeneralPositiveForkSource309 (root compiled initial)
open GeneralPositiveForkInstall309 (after edges models)
open GeneralPositiveForkNodes309
open GeneralPositiveForkSelection309 (holds classes merge_already)
open GeneralNominalExamples (state listDescriptor)
open GeneralPositiveForkLeaf309 (ctx)
open GeneralDeclarationExamples (roles)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (Models State Effect)
open GeneralNominalVersionedMixedKernel234 (Step Committed Installable Stable)
open GeneralNominalVersionedMixedTerminalStable234 (HeadlessUnknown EqualityClosed no_refresh)
open GeneralRebaseDisplaySeparators276 (patch base_patched private_value)
open GeneralNominalCenters (Plan)
open GeneralNominalVersionedFrame231 (children)
open GeneralNominalState (Known)

theorem point_closed : GeneralNominalReobservationSteps.PointClosed ctx.state := by
  intro slot descriptor found
  change (if slot = (0 : Fin 2) then some listDescriptor else none) = some descriptor at found
  split at found
  · cases Option.some.inj found
    intro p accepted
    change p ∈ [GeneralNominalState.Parameter.type ((1 : Fin 2),(1 : Fin 2))] at accepted
    cases List.mem_singleton.mp accepted
    rfl
  · cases found

theorem known0 : Known ctx.state 0 := ⟨(0 : Fin 2),rfl,Or.inr ⟨listDescriptor,rfl⟩⟩
theorem known1 : Known ctx.state 1 := ⟨(1 : Fin 2),rfl,Or.inl (by decide +kernel)⟩

theorem from_raw (m : Assignment) (valid : GeneralNominalState.Models (state true) m) : Models after m :=
  (models _).mpr ((GeneralNominalVersionedJournal232.initial_models ..).mpr
    ⟨valid,GeneralNominalCenters.point_root_holds _ _ (fun _ => rfl) _⟩)

theorem raw_implies_full (m : Assignment) (valid : GeneralNominalState.Models ctx.state m) :
    Models after m := by
  apply from_raw
  change GeneralNominalState.Models
    (GeneralNominalState.extend (state true)
      (GeneralNominalVersionedInstallation231.reserved GeneralPositiveForkPlan309.packet)
      (GeneralNominalVersionedInstallation231.atoms GeneralPositiveForkPlan309.packet)) m at valid
  exact ((GeneralNominalState.extend_models ..).mp valid).1

theorem no_hidden_heads : HeadlessUnknown after := by
  refine ⟨patch (fun _ => .top),from_raw _ (base_patched _),?_⟩
  intro id _ notKnown test found
  have high : 1 < id := by
    by_cases z : id = 0
    · subst id; exact False.elim (notKnown known0)
    · by_cases o : id = 1
      · subst id; exact False.elim (notKnown known1)
      · omega
  rw [private_value _ _ high] at found
  exact GeneralDictionaryGroundCopy218Refresh.top_no_head test found

theorem equality_closed : EqualityClosed after := by
  intro a b _ _ entailed m raw
  exact entailed m (raw_implies_full m raw)

theorem committed (n : Node) : Committed after (plan n) := by
  refine ⟨fun m valid => ⟨holds n m valid,?_⟩,?_⟩
  · cases n
    · exact classes .parent m valid
    · exact classes .low m valid
    · exact classes .high m valid
  · intro c member
    rw [child_list] at member
    cases n
    · change c ∈ [focus .low,focus .high] at member
      rw [edges]
      rcases List.mem_cons.mp member with rfl|tail
      · exact List.mem_cons_self
      · cases List.mem_singleton.mp tail
        exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
    · cases member
    · cases member

theorem no_install (e : Effect roles) (enabled : Installable compiled after e)
    (reached : GeneralNominalSaturationState.Generated after.core.erased.current root e.plan.packet.site.occurrence) :
    Committed after e.plan := by
  obtain ⟨n,whereAt⟩ := generated_nodes _ reached
  have f := e.frame
  rw [enabled.registry_eq,enabled.snapshot_eq,whereAt] at f
  exact (exact_frame n f).symm ▸ committed n

theorem halted (t : State roles) : ¬ Step compiled root after t := by
  rintro ⟨focus,generated,op⟩
  cases op with
  | administrative act =>
    cases act with
    | enqueue _ missing =>
      obtain ⟨n,rfl⟩ := generated_nodes _ generated
      have f := current_frame n
      exact missing _ f.raw_recorded f.occurrence_eq
    | refresh _ cert _ tracked old new =>
      exact no_refresh no_hidden_heads cert tracked old new
    | equate a b one two same novel => exact novel (equality_closed a b one two same)
    | reobserve revision _ improves =>
      exact GeneralNominalReobservationSteps.pointClosed_no_revision point_closed revision improves
  | refresh _ _ cert _ tracked old new => exact no_refresh no_hidden_heads cert tracked old new
  | install e enabled novel => exact novel (no_install e enabled generated)
  | merge a b one two same novel => exact novel (merge_already one two same)

theorem stable (n : Node) : Stable compiled after (focus n) := by
  have close := GeneralNominalVersionedMixedKernel234.closure halted
  cases n
  · exact close.1
  · exact close.2 _ GeneralPositiveForkInstall309.actual_low
  · exact close.2 _ GeneralPositiveForkInstall309.actual_high

end Yulang.GeneralPositiveForkHalt309
