import Yulang.GeneralPositiveForkCertifiedTrace309
import Yulang.GeneralPositiveForkMachine309

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 27500
set_option maxHeartbeats 17000000
namespace Yulang.GeneralPositiveForkBefore309
open GeneralPositiveForkSource309 (initial init_reached init_model compiled registry root parent checked)
open GeneralPositiveForkPlan309 (plan kids loSite hiSite ordered_children)
open GeneralPositiveForkPreinstall309 (frame member_parent unique safe ready)
open GeneralPositiveForkInstall309 (after step models class_effects)
open GeneralPositiveForkLeaf309 (Side site args)
open GeneralPositiveForkEvidence309 (payload)
open GeneralPositiveForkCompiler309 (read decode exact_root_tree)
open GeneralPositiveForkSelection309 (actual_pick)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary Local)
open GeneralNominalVersionedEvidence231 (Frame Evidence Certificate)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarationExamples (roles)
open GeneralNominalExamples (state state_models)
open GeneralNominalCenters (rootSite)
open GeneralDictionaryReadback (Payload payload_iff_erased)
open GeneralGeneratedDictionaryScope299 (Faithful)
open CommonRoleOutermostResolver (classification)

theorem not_root (side : Side) : (site side).occurrence ≠ root := by
  intro equal
  exact GeneralPositiveForkLeafFrame309.invocations side
    (congrArg GeneralSourceDictionaries.Occurrence.identity equal)

theorem absent_center (side : Side) :
    ¬ ∃ s ∈ initial.core.sites, s.occurrence = (site side).occurrence := by
  rintro ⟨s,present,seen⟩
  cases List.mem_singleton.mp present
  exact not_root side seen.symm

theorem no_leaf_frame (side : Side) (p : GeneralNominalCenters.Plan roles) (k : Nat) :
    ¬ Frame compiled initial.core (site side).occurrence k p :=
  fun f => absent_center side ⟨p.input,f.center_recorded,p.input_exact.trans f.occurrence_eq⟩

theorem no_leaf_evidence (side : Side) (m : Assignment) (p : Payload) :
    ¬ Evidence compiled initial.core m (site side).occurrence p := by
  intro live
  have indexed := (payload_iff_erased _ _ _).mpr live
  cases indexed with
  | node inst _ =>
    obtain ⟨q,c⟩ := inst
    exact no_leaf_frame side q _ c.frame

theorem pre_parent (m : Assignment) (valid : Models initial m) :
    Certificate compiled initial.core m root parent.id kids plan :=
  GeneralNominalVersionedEvidence231.certificate_of_semantics frame ordered_children.symm
    (GeneralPositiveForkPlan309.holds _ valid.1.1) ready (class_effects m)

theorem no_root_evidence (m : Assignment) (p : Payload) : ¬ Evidence compiled initial.core m root p := by
  intro positive
  have proof := (payload_iff_erased _ _ _).mpr positive
  cases proof with
  | node one children =>
    obtain ⟨q,cert⟩ := one
    have eq := GeneralRebaseScopedFrame276.same_frame cert.frame frame
      (member_parent cert.frame.visible cert.frame.role_eq)
      (List.mem_singleton.mp cert.frame.raw_recorded) (List.mem_singleton.mp cert.frame.center_recorded)
    subst q
    have observed := cert.children_eq.trans ordered_children
    change _ = [loSite.occurrence,hiSite.occurrence] at observed
    cases observed
    cases children with
    | cons first _ => exact no_leaf_evidence .low m _ ((payload_iff_erased _ _ _).mp first)

theorem no_merged (focus : GeneralSourceDictionaries.Occurrence roles) :
    ¬ GeneralNominalVersionedMergedConflict232.MergedOutputConflict initial focus := by
  rintro ⟨⟨a,b,alias,_,_⟩,_⟩
  change (a,b) ∈ ([] : List (Nat × Nat)) at alias
  cases alias

theorem known_initial (side : Side) :
    ¬ GeneralNominalState.RootPending (state true)
      (GeneralNominalVersionedCandidates231.inputs (site side).occurrence).demand := by
  rintro ⟨i,no⟩
  have k : GeneralNominalState.Known (state true) 1 := ⟨(1 : Fin 2),rfl,Or.inl (by decide +kernel)⟩
  exact no ((congrArg Prod.fst (args side i)).symm ▸ k)

theorem pending_side (side : Side) : Local registry initial (site side).occurrence .pending := by
  apply GeneralNominalVersionedMixedSourceBoundary234.local_iff.mpr
  apply GeneralNominalVersionedMixedBoundary234.local_iff.mpr
  have unavailable : ¬ GeneralNominalVersionedDiagnostic232.AdministrativeReady initial (site side).occurrence :=
    fun h => absent_center side h.1
  have inspection : (GeneralNominalVersionedDiagnostic232.boundary roles).InspectionPending
      compiled initial (site side).occurrence := Or.inr unavailable
  have noSharing : ¬ GeneralNominalVersionedDiagnostic232.SharingConflict compiled initial (site side).occurrence := by
    rintro ⟨_,_,_,safe,_⟩
    exact safe.2.2.2 inspection
  refine .ordinary noSharing (.ordinary (no_merged _) (.inspectionPending (known_initial side) inspection ?_ ?_))
  · rintro (raw | (⟨i,cycle⟩|⟨c,_,_,i,cycle⟩))
    · obtain ⟨_,_,_,slot,_,cycle⟩ := raw
      exact GeneralRebaseDisplaySafety276.raw_acyclic (state true) rfl (state_models true) slot cycle
    · exact GeneralRebaseDisplaySafety276.semantic init_model _ cycle
    · exact GeneralRebaseDisplaySafety276.semantic init_model _ cycle
  · rintro (raw | ⟨p,_,entry,_,cycle⟩)
    · obtain ⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩ := raw
      exact GeneralRebaseDisplaySafety276.raw_acyclic (state true) rfl (state_models true) visited.1 cycle
    · exact GeneralRebaseDisplaySafety276.semantic init_model _ cycle

theorem picked_root : Local registry initial root (.selected 1 kids) := by
  apply GeneralNominalVersionedMixedSourceBoundary234.local_iff.mpr
  apply GeneralNominalVersionedMixedBoundary234.local_iff.mpr
  exact GeneralNominalVersionedDiagnosticLaws232.selected_of_model safe unique init_model frame ready
    (GeneralPositiveForkPlan309.holds _ init_model.1.1) (class_effects _) (no_merged root)

theorem initial_tree :
    GeneralNominalVersionedMixedResolver236.tree ⟨rfl,checked⟩ init_reached root =
      .selected 1 [.pending,.pending] :=
  (GeneralNominalVersionedMixedResolver236.tree_exact ⟨rfl,checked⟩ init_reached root _).mpr
    (.selected picked_root (.cons (.pending (pending_side .low)) (.cons (.pending (pending_side .high)) .nil)))

theorem wrong_phase_not_faithful : ¬ Faithful (b:=boundary roles) (r:=registry) (s:=initial) read decode := by
  intro supposed
  have bad := supposed 1 _ GeneralPositiveForkCheck309.read_low
  cases B4TargetV8.local_functional bad (pending_side .low)

theorem actual_boundary (m : Assignment) (valid : Models initial m) :
    Certificate compiled initial.core m root parent.id kids plan ∧
    (∀ p, ¬ Evidence compiled initial.core m root p) ∧
    Models after m ∧ (boundary roles).Evidence registry after m root payload :=
  ⟨pre_parent m valid,no_root_evidence m,(models _).mpr valid,
    GeneralPositiveForkEvidence309.root_evidence _ ((models _).mpr valid)⟩

end Yulang.GeneralPositiveForkBefore309
