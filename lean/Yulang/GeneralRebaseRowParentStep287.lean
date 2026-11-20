import Yulang.GeneralRebaseRowParentFrame287
import Yulang.GeneralRebaseRowSpineCycles287
import Yulang.GeneralRebaseRowGroundBoundary287

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28500
set_option maxHeartbeats 14500000
namespace Yulang.GeneralRebaseRowParentStep287
open GeneralRebaseRowChildSource287
open GeneralRebaseRowParentPacket287
open GeneralRebaseRowParentFrame287
open GeneralRebaseRowSpineCycles287 (Form acyclic)
open GeneralNominalVersionedMixedKernel234 (Step Installable AlternativesSafe Committed)
open GeneralNominalVersionedCycles232 (Cyclic Safe)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalCenters (Plan)

theorem model_forms (row : Common.Row) (n : Nat) : ∃ f : Form, (model row n).1 = f.value row := by
  unfold model
  by_cases zero : n = 0
  · exact ⟨.row,by simp [zero,Form.value]⟩
  by_cases one : n = 1
  · exact ⟨.wrap .row,by simp [one,Form.value]⟩
  by_cases two : n = 2
  · exact ⟨.wrap (.wrap .row),by simp [two,Form.value]⟩
  exact ⟨.scalar,by simp [zero,one,two,Form.value]⟩

theorem no_cycle_before (o) : ¬ Cyclic before o :=
  acyclic (before_model Common.rowEmpty) (model_forms Common.rowEmpty) o

theorem no_cycle_after (choice : Bool) (o) : ¬ Cyclic (after choice) o :=
  acyclic (after_model choice Common.rowEmpty) (model_forms Common.rowEmpty) o

theorem no_raw_before (i : Fin raw.base.slots) : ¬ GeneralNominalCycleK2.RecursAt raw i :=
  fun bad => no_cycle_before _ (GeneralRebaseRawIntoFull271.recurs before ⟨_,before_model Common.rowEmpty⟩ i bad)

theorem at_frame (choice : Bool) {p : Plan roles} {key : Nat}
    (one : Frame (registry choice) before.core root key p) : p = plan choice := by
  have exactDecl := at_role choice _ one.visible one.role_eq
  have raw : p.packet.site = (plan choice).packet.site := List.mem_singleton.mp one.raw_recorded
  have center : p.input = (plan choice).input := List.mem_singleton.mp one.center_recorded
  exact GeneralRebaseScopedFrame276.same_frame one (frame choice) exactDecl raw center

theorem positions (choice : Bool) : Safe before (plan choice) := by
  refine ⟨?_,fun entry _ => no_cycle_before entry.1⟩
  cases choice <;> decide +kernel

theorem admin : GeneralNominalVersionedDiagnostic232.AdministrativeReady before root := by
  refine ⟨⟨_,List.mem_singleton_self _,rfl⟩,?_⟩
  intro a one _ b two _
  cases List.mem_singleton.mp one
  cases List.mem_singleton.mp two
  exact .refl _

theorem safe (choice : Bool) :
    B4TargetV8.SafeKnown (GeneralNominalVersionedDiagnostic232.boundary roles) (registry choice) before root := by
  refine ⟨root_known,?_,?_,?_⟩
  · rintro (old | (⟨_,cycle⟩ | ⟨_,_,_,_,cycle⟩))
    · obtain ⟨_,_,_,i,_,cycle⟩ := old
      exact no_raw_before i cycle
    · exact no_cycle_before _ cycle
    · exact no_cycle_before _ cycle
  · rintro (old | ⟨_,_,_,_,cycle⟩)
    · obtain ⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩ := old
      exact no_raw_before visited.1 cycle
    · exact no_cycle_before _ cycle
  · rintro (⟨_,d,visible,role,_,unfit⟩ | missing)
    · cases at_role choice d visible role
      exact unfit (prepared choice)
    · exact missing admin

theorem alternatives (choice : Bool) : AlternativesSafe (registry choice) before (plan choice).input := by
  intro candidate _ same
  change Frame (registry choice) before.core root candidate.packet.declaration.id candidate at same
  rw [at_frame choice same]
  exact positions choice

theorem installable (choice : Bool) : Installable (registry choice) before (effect choice) := by
  refine ⟨rfl,rfl,safe choice,?_,?_,?_,positions choice,alternatives choice,
    model Common.rowEmpty,(install_check choice _).mpr ?_⟩
  · exact GeneralNominalVersionedMixedObservations233.legacy_cache
      (GeneralDictionaryDefaultCache208.initial_valid ctx root)
  · change (GeneralNominalVersionedPlans231.emittedSchema (plan choice)).unknown = false
    rw [emitted]
  · intro _ member; cases member
  · exact (after_exact choice _).mp (after_model choice Common.rowEmpty)

theorem novelty (choice : Bool) : ¬ Committed before (plan choice) := by
  intro committed
  have impossible := committed.2 _ ((sole_child choice).symm ▸ List.mem_singleton_self _)
  change (root,child choice) ∈ [] at impossible
  cases impossible

theorem actual_step (choice : Bool) : Step (registry choice) root before (after choice) :=
  ⟨root,.root,.install (effect choice) (installable choice) (novelty choice)⟩

theorem actual_edge (choice : Bool) : (root,child choice) ∈ (after choice).core.erased.current.edges := by
  exact GeneralNominalVersionedInstall232.installed_child
    ((sole_child choice).symm ▸ List.mem_singleton_self _)

theorem generated (choice : Bool) : GeneralNominalSaturationState.Generated
    (after choice).core.erased.current root (child choice) :=
  .child .root (actual_edge choice)

end Yulang.GeneralRebaseRowParentStep287
