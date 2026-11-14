import Yulang.GeneralDictionaryCenteredLedger181
import Yulang.GeneralDictionaryCenteredPointExample179
import Yulang.GeneralDictionaryCenteredJournalCandidate180

/-! A nonempty modeled ledger with a real inspected Candidate and a nonpoint
binder overlap. FreshInputs fails but registered coverage gives joint readback.
This is not asserted to be reachable, stable, or a new installation step. -/
namespace Yulang.GeneralDictionaryCenteredLedgerExample181
open GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralDictionaryCenteredNominalPointExample178 (root start leaf plan)
open GeneralDictionaryNominalPairExample178 (registry declaration)
open GeneralNominalRawFrame179 (fullSources)
open GeneralNominalCenteredFrame179

abbrev ledger := { start with plans := [plan] }

 theorem candidate : GeneralDictionaryCenteredCandidate176.Candidate registry ledger root declaration.id [] plan := by
  have c := GeneralDictionaryCenteredNominalPointExample178.candidate
  exact ⟨c.registry_eq,c.context_eq,c.occurrence_eq,c.key_eq,c.children_eq,c.raw_recorded,
    c.centered_recorded,c.visible,c.role,c.located,c.prepared,c.branch⟩

 theorem modeled : ∃ model, Models ledger model := by
  obtain ⟨model,valid,holds,_⟩ := GeneralDictionaryCenteredPointExample179.joint
  refine ⟨model,valid.1,valid.2.1,?_⟩
  intro old member
  cases List.mem_singleton.mp member
  exact holds.2

 theorem binder_member : plan.binder 0 ∈ fullSources ledger := by
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨plan,List.mem_singleton_self _,?_⟩
  have input : 0 ∈ captureNames plan := (capture_mem plan 0).mpr (.inl (by decide +kernel))
  have member : plan.binder 0 ∈ captureSources plan :=
    List.mem_flatMap.mpr ⟨0,input,by simp⟩
  simp [equationSources,member]

 theorem not_fresh : ¬ GeneralDictionaryCenteredJournalCandidate180.FreshInputs ledger plan := by
  apply GeneralDictionaryCenteredJournalCandidate180.not_freshInputs_of_overlap
    0 (by decide +kernel) _ binder_member
  rw [GeneralDictionaryCenteredPointJoint179.capture_exact plan leaf rfl (0 : Fin 1)]
  decide +kernel

 theorem covered : GeneralDictionaryCenteredProvenance181.Covered plan leaf ledger :=
  GeneralDictionaryCenteredLedger181.registered_covered plan leaf (List.mem_singleton_self _)
    (fun index equal => point_center _ root index equal)

 theorem nonempty_joint :
    ∃ previous extended, Models ledger previous ∧ Models ledger extended ∧ plan.Holds extended ∧
      (∀ name ∈ fullSources ledger, extended name = previous name) ∧
      ¬ GeneralDictionaryCenteredJournalCandidate180.FreshInputs ledger plan := by
  obtain ⟨previous,valid⟩ := modeled
  obtain ⟨extended,models,holds,kept⟩ := GeneralDictionaryCenteredLedger181.joint
    plan leaf candidate (fun index equal => point_center _ root index equal) covered previous valid
  exact ⟨previous,extended,valid,models,holds,kept,not_fresh⟩

end Yulang.GeneralDictionaryCenteredLedgerExample181
