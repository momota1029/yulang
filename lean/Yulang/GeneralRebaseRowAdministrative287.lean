import Yulang.GeneralRebaseRowSemanticMark287

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29000
set_option maxHeartbeats 15200000
namespace Yulang.GeneralRebaseRowAdministrative287
open GeneralRebaseRowChildSource287
open GeneralRebaseRowParentFrame287 (after after_model after_exact)
open GeneralRebaseRowParentStep287 (model_forms)
open GeneralRebaseRowGeneratedChild287 (current)
open GeneralRebaseRowTrustedBoundary287 (putTop forbidden_known)
open GeneralRebaseRowChildRaw287 (SourceCheck OutputCheck)
open GeneralRebaseRowSpineCycles287 (Form equivalent_rank)
open GeneralNominalVersionedJournal232 (Models State)
open GeneralNominalVersionedMixedKernel234 (Equal)
open GeneralNominalState (Known)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

private abbrev good := GeneralRebaseRowChildSource287.model Common.rowEmpty

theorem output_elsewhere (m : Assignment) {n : Nat} (outside : 2 < n) :
    OutputCheck (putTop m n) ↔ OutputCheck m := by
  have n0 : (0 : Nat) ≠ n := by omega
  have n1 : (1 : Nat) ≠ n := by omega
  have n2 : (2 : Nat) ≠ n := by omega
  simp [OutputCheck,SourceCheck,putTop,n0,n1,n2]

theorem spine_not_top (f : Form) : ¬ Equivalent .top (f.value Common.rowEmpty) := by
  intro eq
  cases f with
  | scalar => exact GeneralNominalTopObservation.top_not_scalar .int eq.1
  | row => exact GeneralNominalTopObservation.top_not_nominal 6 _ eq.1
  | wrap => exact GeneralNominalTopObservation.top_not_nominal 0 _ eq.1

theorem isolate {choice : Bool} {n k : Nat} (outside : 2 < n) (other : n ≠ k) :
    ¬ Equal (after choice) n k := by
  intro eq
  have valid := (after_exact choice _).mpr ((output_elsewhere good outside).mpr
    ((after_exact choice _).mp (after_model choice Common.rowEmpty)))
  have got := eq (putTop good n) valid
  change Equivalent (if n = n then .top else (good n).1) (if k = n then .top else (good k).1) at got
  rw [ite_eq_left rfl,ite_eq_right other.symm] at got
  obtain ⟨f,decl⟩ := model_forms Common.rowEmpty k
  exact spine_not_top f (decl ▸ got)

theorem exact_rank (n : Nat) (small : n ≤ 2) :
    ∃ f : Form, (good n).1 = f.value Common.rowEmpty ∧ f.rank = n := by
  have which : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases which with rfl|rfl|rfl
  · exact ⟨.row,rfl,rfl⟩
  · exact ⟨.wrap .row,rfl,rfl⟩
  · exact ⟨.wrap (.wrap .row),rfl,rfl⟩

theorem equality_is_reflexive (choice : Bool) (n k : Nat) (same : Equal (after choice) n k) :
    n = k := by
  by_cases apart : n = k
  · exact apart
  by_cases nHigh : 2 < n
  · exact (isolate nHigh apart same).elim
  by_cases kHigh : 2 < k
  · exact (isolate kHigh (Ne.symm apart) (fun m held => ⟨(same m held).2,(same m held).1⟩)).elim
  obtain ⟨f,first,rankFirst⟩ := exact_rank n (by omega)
  obtain ⟨g,last,rankLast⟩ := exact_rank k (by omega)
  have both := same good (after_model choice Common.rowEmpty)
  rw [first,last] at both
  exact rankFirst.symm.trans ((equivalent_rank Common.rowEmpty f g both).trans rankLast)

theorem already_known (choice : Bool) (n : Nat) (low : n ≤ 1) : Known (current choice).state n := by
  have two : n = 0 ∨ n = 1 := by omega
  rcases two with rfl|rfl
  · exact ⟨(0 : Fin 3),rfl,Or.inr ⟨inner,rfl⟩⟩
  · exact ⟨(1 : Fin 3),rfl,Or.inr ⟨outer,rfl⟩⟩

theorem point_closed (choice : Bool) : GeneralNominalReobservationSteps.PointClosed (current choice).state := by
  intro slot d seen
  let j : Fin 3 := slot
  change (if j = 0 then some inner else if j = 1 then some outer else none) = some d at seen
  split at seen
  · cases Option.some.inj seen
    intro parameter member
    cases List.mem_singleton.mp member
    rfl
  · split at seen
    · cases Option.some.inj seen
      intro parameter member
      cases List.mem_singleton.mp member
      rfl
    · cases seen

theorem no_refresh (choice : Bool) {context : GeneralNominalCandidates.Context}
    (cert : GeneralNominalVersionedMixedObservations233.Refresh (after choice) context)
    (n : Nat) (old : ¬ Known (current choice).state n) (new : Known context.state n) : False := by
  by_cases low : n ≤ 1
  · exact old (already_known choice n low)
  · exact forbidden_known choice context.state cert.cache n (by omega) new

end Yulang.GeneralRebaseRowAdministrative287
