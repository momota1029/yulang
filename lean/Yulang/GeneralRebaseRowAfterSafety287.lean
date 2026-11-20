import Yulang.GeneralRebaseRowPublic287

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28500
set_option maxHeartbeats 15000000
namespace Yulang.GeneralRebaseRowAfterSafety287
open GeneralRebaseRowChildSource287
open GeneralRebaseRowParentPacket287 (child center plan)
open GeneralRebaseRowParentFrame287 (after after_model)
open GeneralRebaseRowGeneratedChild287 (current known)
open GeneralRebaseRowParentStep287 (no_cycle_after)
open GeneralRebaseRowParentEvidence287 (centers roles_distinct)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedCandidates231 (Prepared)
open GeneralNominalVersionedDiagnostic232 (AdministrativeReady)

abbrev diag := GeneralNominalVersionedDiagnostic232.boundary roles

theorem no_raw (choice : Bool) (slot : Fin (current choice).state.base.slots) :
    ¬ GeneralNominalCycleK2.RecursAt (current choice).state slot :=
  fun bad => no_cycle_after choice _
    (GeneralRebaseRawIntoFull271.recurs _ ⟨_,after_model choice Common.rowEmpty⟩ slot bad)

theorem root_clear (choice : Bool) (focus : Occurrence roles) :
    ¬ diag.RootK2 (registry choice) (after choice) focus := by
  rintro (rawCycle | (⟨_,cyclic⟩ | ⟨_,_,_,_,cyclic⟩))
  · obtain ⟨_,_,_,slot,_,cyclic⟩ := rawCycle
    exact no_raw choice slot cyclic
  · exact no_cycle_after choice _ cyclic
  · exact no_cycle_after choice _ cyclic

theorem candidate_clear (choice : Bool) (focus : Occurrence roles) :
    ¬ diag.CandidateK2 (registry choice) (after choice) focus := by
  rintro (rawCycle | ⟨_,_,_,_,cyclic⟩)
  · obtain ⟨_,_,_,_,_,_,_,_,seen,_,cyclic⟩ := rawCycle
    exact no_raw choice seen.1 cyclic
  · exact no_cycle_after choice _ cyclic

theorem administrative (choice : Bool) {focus : Occurrence roles}
    (scope : focus = root ∨ focus = child choice) : AdministrativeReady (after choice) focus := by
  constructor
  · rcases scope with rfl|rfl
    · exact ⟨(plan choice).input,centers choice ▸ List.mem_cons_self,rfl⟩
    · exact ⟨center choice,centers choice ▸ List.mem_cons_of_mem _ List.mem_cons_self,rfl⟩
  · intro a first _ b last same
    rw [centers] at first last
    simp only [List.mem_cons,List.not_mem_nil,or_false] at first last
    rcases first with rfl|rfl <;> rcases last with rfl|rfl
    · exact .refl _
    · exact (roles_distinct choice same.1).elim
    · exact (roles_distinct choice same.1.symm).elim
    · exact .refl _

theorem pending_root_no (choice : Bool) :
    ¬ diag.RootPending (registry choice) (after choice) root := by
  rintro ⟨_,forget⟩
  exact forget ⟨(1 : Fin 3),rfl,Or.inr ⟨outer,rfl⟩⟩

theorem safe_of_prepared (choice : Bool) {focus : Occurrence roles}
    (scope : focus = root ∨ focus = child choice)
    (pending : ¬ diag.RootPending (registry choice) (after choice) focus)
    (ready : ∀ d ∈ (registry choice).declarations, d.role = focus.demand.role →
      Prepared (registry choice) (current choice) focus d) :
    B4TargetV8.SafeKnown diag (registry choice) (after choice) focus := by
  refine ⟨pending,root_clear choice focus,candidate_clear choice focus,?_⟩
  rintro (⟨_,d,visible,role,_,notReady⟩ | absent)
  · exact notReady (ready d visible role)
  · exact absent (administrative choice scope)

theorem merged_clear (choice : Bool) (focus : Occurrence roles) :
    ¬ GeneralNominalVersionedMergedConflict232.MergedOutputConflict (after choice) focus := by
  rintro ⟨⟨a,b,member,_,_⟩,_⟩
  change (a,b) ∈ ([] : List (Nat × Nat)) at member
  cases member

theorem blocked_local :
    GeneralNominalVersionedMixedBoundary234.Local (registry false) (after false) (child false) .pending := by
  apply GeneralNominalVersionedMixedBoundary234.local_iff.mpr
  have pending : diag.InspectionPending (registry false) (after false) (child false) :=
    Or.inl GeneralRebaseRowGeneratedChild287.pending_actual
  refine .ordinary (fun ⟨_,_,_,safe,_⟩ => safe.2.2.2 pending) (.ordinary (merged_clear false _) ?_)
  exact .inspectionPending (known false) pending (root_clear false _) (candidate_clear false _)

end Yulang.GeneralRebaseRowAfterSafety287
