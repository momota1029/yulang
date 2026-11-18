import Yulang.GeneralDictionaryObservedRebase259
namespace Yulang.GeneralDictionaryRebaseCertificate259
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryInitialFill258 (complete bind)
open GeneralDictionaryLooseIterationBook240 (plan)
open GeneralDictionaryLooseIterationIteration240 (state)
open GeneralDictionaryRebaseStep258 (initialState finalState)

/-- All fields concern the same explicit reconstruction, rather than unrelated
existential witnesses for each old plan or each completed state. -/
structure Certificate (n : Nat) (boundary : Assignment) : Prop where
 agrees : GeneralDictionaryInitialProjection257.Agree (complete boundary) boundary
 current : GeneralNominalVersionedJournal232.Models (state n) (complete boundary)
 packet : GeneralNominalVersionedPlans231.Holds (plan n) (complete boundary)
 next : GeneralNominalVersionedJournal232.Models (state (n+1)) (complete boundary)
 final : GeneralDictionaryRebasePublic258.Models finalState (complete boundary)

/-- Construct the actual old packet certificate from the initial raw model.
The I45 terminal fixture has empty children/outputs; no general producer is claimed. -/
theorem certificate (n : Nat) (boundary : Assignment)
 (source : GeneralNominalState.Models GeneralDictionaryLooseLoopSource240.snapshot boundary) :
 Certificate n boundary := by
 have all := (GeneralDictionaryInitialFill258.all_stages boundary).mpr source
 have future := (GeneralDictionaryJournalRepair257.exact n (complete boundary)).mp (all (n+1))
 have packet := GeneralDictionaryPastPacket257.holds (n+1) n (by omega) (complete boundary) future.1 future.2
 have finite := (GeneralDictionaryUniformView258.journal_exact 0 (bind boundary)).mp (all 1)
 have final := (GeneralDictionaryUniformView258.journal_view_exact 1 (bind boundary)).mpr finite
 exact ⟨GeneralDictionaryInitialFill258.public_agrees boundary,all n,packet,all (n+1),final⟩

/-- Actual report-derived initial write, accompanied by the actual plan model
and the final finite-state model on one boundary-preserving assignment. -/
theorem initial_install (n : Nat) (boundary : Assignment)
 (source : GeneralNominalState.Models GeneralDictionaryLooseLoopSource240.snapshot boundary) :
 GeneralRebaseStep258.Step (GeneralDictionaryObservedRebase259.observeAt n) initialState finalState ∧
 Certificate n boundary :=
 ⟨GeneralDictionaryObservedRebase259.initial_install n,certificate n boundary source⟩

theorem old_new (n : Nat) (boundary : Assignment) :
 (∃ assignment, GeneralDictionaryInitialProjection257.Agree assignment boundary ∧
 GeneralNominalVersionedJournal232.Models (state n) assignment) ↔
 (∃ assignment, GeneralDictionaryInitialProjection257.Agree assignment boundary ∧
 GeneralDictionaryRebasePublic258.Models (GeneralDictionaryRebaseStep258.project n) assignment) :=
 GeneralDictionaryRebasePublic258.old_new n boundary

theorem certificate_source (n : Nat) (boundary : Assignment) (valid : Certificate n boundary) :
 GeneralNominalState.Models GeneralDictionaryLooseLoopSource240.snapshot boundary :=
 (GeneralDictionaryRebasePublic258.final_public boundary).mp ⟨complete boundary,valid.agrees,valid.final⟩

theorem certificate_exact (n : Nat) (boundary : Assignment) : Certificate n boundary ↔
 GeneralNominalState.Models GeneralDictionaryLooseLoopSource240.snapshot boundary :=
 ⟨certificate_source n boundary,certificate n boundary⟩
end Yulang.GeneralDictionaryRebaseCertificate259
