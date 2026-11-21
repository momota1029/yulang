import Yulang.GeneralMixedCompoundBatchBase307
import Yulang.GeneralMixedCompoundHalfRun307

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 19000
set_option maxHeartbeats 11000000
namespace Yulang.GeneralMixedCompoundBatch307
open GeneralDictionaryCompoundPoint238 (point)
open GeneralDictionaryCompoundRefresh239 (refreshed models_iff)
open GeneralDictionaryCompoundBase239 (lo)
open GeneralMixedCompoundUpperSnapshot307 (snap context)
open GeneralMixedCompoundUpperRefresh307 (upperState cert)
open GeneralMixedCompoundBatchBase307 (refineBatch)
open GeneralNominalVersionedMixedObservations233 (Refresh CacheSound)
open GeneralMixedCompoundRefreshBound307 (Run)
open GeneralNominalVersionedJournal232 (State)

theorem alias_forward (al : GeneralNominalSaturationState.Alias refreshed.core.erased.current a b) :
    GeneralNominalSaturationState.Alias point.core.erased.current a b := by
  induction al with
  | refl => exact .refl _
  | edge mem => exact .edge mem
  | symm _ ih => exact .symm ih
  | trans _ _ one two => exact .trans one two

theorem settled_forward (h : GeneralNominalSupport.Discharged refreshed.core.erased.current focus) :
    GeneralNominalSupport.Discharged point.core.erased.current focus := by
  induction h with
  | packet p mem _ ih => exact .packet p mem ih
  | alias a b one two same _ ih => exact .alias a b one two (alias_forward same) ih

theorem discharged_forward (h : GeneralNominalVersionedSupport233.Discharged refreshed focus) :
    GeneralNominalVersionedSupport233.Discharged point focus := by
  induction h with
  | packet p mem _ ih => exact .packet p mem ih
  | alias a b one two same _ ih => exact .alias a b one two (alias_forward same) ih

theorem legacy_forward {facts} (previous : GeneralNominalCenteredHeadMatStepSupport.Trusted refreshed.legacy facts) :
    GeneralNominalCenteredHeadMatStepSupport.Trusted point.legacy facts := by
  induction previous with
  | source => exact .source
  | input p _ one read ih => exact .input p ih one read
  | output effect _ one plan within read stable ih =>
    exact .output effect ih one plan within read
      ⟨stable.1,fun d h => settled_forward (stable.2 d h)⟩
  | merge a b _ one two al all witnessed same ih =>
    exact .merge a b ih one two (alias_forward al) all witnessed same

theorem versioned_forward {facts} (previous : GeneralNominalVersionedSupport233.Trusted refreshed facts) :
    GeneralNominalVersionedSupport233.Trusted point facts := by
  induction previous with
  | source => exact .source
  | input p _ mem read ih => exact .input p ih mem read
  | output e _ mem keep input read settled ih =>
    exact .output e ih mem keep input read
      ⟨settled.1,fun d h => discharged_forward (settled.2 d h)⟩
  | merge a b _ one two al all witnessed same ih =>
    exact .merge a b ih one two (alias_forward al) all witnessed same


theorem cached : CacheSound point snap := by
  intro item seen
  obtain ⟨older,newer,oldTrust,newTrust,sound⟩ := cert.cache item seen
  exact ⟨older,newer,legacy_forward oldTrust,versioned_forward newTrust,sound⟩

noncomputable def batch : Refresh point context :=
  ⟨refineBatch,rfl,(fun n h => GeneralDictionaryCompoundRefresh239.certificate.support _
    (cert.support n h)),(fun m valid => cert.constraints m ((models_iff m).mpr valid)),cached⟩

theorem by_one : Run 1 upperState :=
  .more .zero context batch lo (GeneralDictionaryCompoundRefresh239.supported 5 (by decide))
    GeneralDictionaryCompoundRefreshStep239.lower_unknown
    GeneralMixedCompoundUpperSupport307.known_lo

theorem feasible_exact (n : Nat) : Run n upperState ↔ n = 1 ∨ n = 2 ∨ n = 3 := by
  constructor
  · intro given
    have bound := GeneralMixedCompoundRefreshBound307.bound given
    have nonzero : n ≠ 0 := by
      intro h; subst n
      have equal : upperState = point := by cases given
      have observable : GeneralNominalState.Known upperState.core.erased.current.context.state lo :=
        GeneralMixedCompoundUpperSupport307.known_lo
      rw [equal] at observable
      exact GeneralDictionaryCompoundRefreshStep239.lower_unknown observable
    omega
  · rintro (rfl|rfl|rfl)
    · exact by_one
    · exact GeneralMixedCompoundHalfRun307.by_two
    · exact GeneralMixedCompoundHalfRun307.by_three

end Yulang.GeneralMixedCompoundBatch307
