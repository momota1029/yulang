import Yulang.GeneralObservedMetadataReleaseFixture290

/-! Public source-specific statement for the sealed auxiliary output.
No new rule of the old MixedKernel or extra raw Known fact is asserted. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29500
set_option maxHeartbeats 20000000
namespace Yulang.GeneralObservedMetadataReleased290
open GeneralRebaseRowChildSource287
open GeneralRebaseRowParentFrame287 (after)
open GeneralRebaseRowParentPacket287 (child)
open GeneralRebaseReceiptFixture289 (request wire)
open GeneralRebaseReceiptWitness289 (ActualPath Witness check_iff only_actual_release)
open GeneralRebaseReceiptCompile289 (Mark actualMark compile concrete_compile)
open GeneralObservedMetadataSeal290 (Seal)
open GeneralObservedMetadataReleaseFixture290 (normalized accepted_seals actual_replay)
open GeneralObservedMetadataPublication290 (publish publishFrom_exact ready_release)
open GeneralObservedMetadataGate290 (Outcome)
open GeneralObservedMetadataActual290 (strict_path_agrees)
open GeneralObservedMetadataHistorical290 (ready_exact)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralRebaseInertLeaf288 (SourceSlice)
open GeneralNominalCommonBridge (Assignment)

theorem released_exact (choice : Bool) {s : State roles} (path : ActualPath choice s)
    (saved : Seal) (value : Mark) :
    publish (registry choice) s root (child choice) (request choice) interp saved = .released value ↔
      choice = true ∧ s = after true ∧ saved = normalized ∧ value = actualMark := by
  constructor
  · intro pub
    have ready := (ready_release pub).1
    have prior := ((ready_exact ..).mp ready).1
    have diagnostic := Outcome.receipt.inj ((strict_path_agrees choice path).symm.trans prior)
    have witness := (check_iff choice path).mp diagnostic
    obtain ⟨happy,same⟩ := (only_actual_release choice path).mp witness
    subst choice
    subst s
    rw [actual_replay] at pub
    obtain ⟨member,computed⟩ := (publishFrom_exact _ _ _ _ _).mp pub
    rw [concrete_compile] at computed
    exact ⟨rfl,rfl,List.mem_singleton.mp member,(Option.some.inj computed).symm⟩
  · rintro ⟨rfl,rfl,rfl,rfl⟩
    rw [actual_replay]
    exact (publishFrom_exact _ _ _ _ _).mpr ⟨List.mem_singleton_self _,concrete_compile true⟩

theorem public_models (choice : Bool) {s : State roles} (path : ActualPath choice s)
    (saved : Seal) (value : Mark)
    (pub : publish (registry choice) s root (child choice) (request choice) interp saved = .released value) :
    Witness choice s ∧ (∀ m, Models s m ↔ SourceSlice s m ∧ value.Holds m) ∧
      ¬ GeneralNominalState.Known s.core.erased.current.context.state value.target := by
  obtain ⟨rfl,rfl,rfl,rfl⟩ := (released_exact choice path saved value).mp pub
  refine ⟨GeneralRebaseReceiptWitness289.witness_positive,?_,GeneralRebaseRowLedger288.unknown_output true⟩
  have supported := (GeneralRebaseReceiptScopedTrace289.family_iff true
    ⟨after true,.published (request true)⟩).mpr (.published rfl)
  intro m
  exact GeneralRebaseReceiptPublic289.exact_raw_gate true supported actualMark (concrete_compile true) m

theorem bounded_release_still_does_not_imply_global_metadata :
    publish (registry true) (after true) root (child true) (request true)
      GeneralObservedMetadataControls290.primitiveOutside normalized = .released actualMark ∧
    ¬ GeneralNominalCandidates.Metadata (registry true)
      ⟨(GeneralObservedMetadataGate290.context (after true)).state,GeneralObservedMetadataControls290.primitiveOutside⟩ := by
  refine ⟨?_,GeneralObservedMetadataActual290.unobserved_wrong_proposed_primitive_does_not_block.2⟩
  decide +kernel

end Yulang.GeneralObservedMetadataReleased290
