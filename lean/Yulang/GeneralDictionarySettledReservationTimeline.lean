import Yulang.GeneralDictionarySettledReservedExample

/-! A concrete terminal producer separates settlement from current observation.
This is not the missing generated nonterminal consumer example. -/
namespace Yulang.GeneralDictionarySettledReservationTimeline
open GeneralDictionaryFiniteObservedExampleReserved
open GeneralDictionaryFiniteObservedExampleReservedPositive
open GeneralDictionaryFiniteObservedExample (registry)
open GeneralDictionaryReservedNominalRefresh
open GeneralNominalSupport
open GeneralNominalSettledSupport (PacketSettled Trusted HeadJustified ReadyAt)

/-- The actual terminal installation settles its own recorded packet. -/
theorem installed_settled : PacketSettled installed.current packet := by
  refine ⟨GeneralDictionaryFiniteObservedExampleReservedPositive.packet_recorded,?_⟩
  intro child member
  rw [packet_children] at member
  cases member

/-- The output ledger is trusted before the equality and refresh transitions. -/
theorem installed_output_trusted : ∃ support,
    Trusted installed [Fact.outputs packet support,Fact.inputs packet support] := by
  obtain ⟨support,trusted⟩ := GeneralDictionarySettledReservedExample.output_trusted
  refine ⟨support,GeneralNominalSettledSupport.trusted_monotone (before := refreshed) (after := installed) rfl (fun _ h => h) ?_ trusted⟩
  intro p done
  have same : p = packet := by
    have member : p ∈ [packet] := done.1
    simpa using member
  subst p
  exact installed_settled

/-- Semantic output justification already holds before a slot is materialized. -/
theorem installed_output_justified : HeadJustified installed 2 (.nominal 0 3) := by
  apply GeneralNominalSettledSupport.head_monotone (before := refreshed) (after := installed) rfl (fun _ h => h) ?_
    GeneralDictionarySettledReservedExample.output_head_justified
  intro p done
  have same : p = packet := by
    have member : p ∈ [packet] := done.1
    simpa using member
  subst p
  exact installed_settled

private theorem head_has_slot {snapshot : GeneralNominalState.State} (head : Head snapshot identity test observation) :
    ∃ slot, snapshot.base.source slot = identity := by
  cases head <;> exact ⟨_,rfl⟩

/-- Settlement and semantic justification do not manufacture a current head. -/
theorem installed_not_ready : ¬ ReadyAt installed 2 := by
  rintro ⟨test,observation,head,_⟩
  obtain ⟨slot,equal⟩ := head_has_slot head
  have bound := slot.isLt
  change slot.val = 2 at equal
  change slot.val < 2 at bound
  omega

/-- The recorded equality alone still does not manufacture the current slot. -/
theorem equated_not_ready : ¬ ReadyAt GeneralDictionaryReservedEqualityStep.after 2 := by
  rintro ⟨test,observation,head,_⟩
  exact GeneralDictionaryReservedSuccessorBoundary.no_target_slot (head_has_slot head)

/-- Concrete actual transitions, followed by the first available current read.
The final consumer is only a query: generation/installation is not asserted. -/
theorem timeline :
    GeneralNominalSettledSteps.Step registry root start installed ∧
    GeneralNominalSettledSteps.Step registry root installed GeneralDictionaryReservedEqualityStep.after ∧
    GeneralNominalSettledSteps.Step registry root GeneralDictionaryReservedEqualityStep.after refreshed ∧
    HeadJustified installed 2 (.nominal 0 3) ∧ ¬ ReadyAt installed 2 ∧
    ¬ ReadyAt GeneralDictionaryReservedEqualityStep.after 2 ∧ ReadyAt refreshed 2 :=
  ⟨GeneralDictionarySettledReservedExample.install_step,
   GeneralDictionarySettledReservedExample.equality_step,
   GeneralDictionarySettledReservedExample.refresh_step,
   installed_output_justified,installed_not_ready,equated_not_ready,
   GeneralDictionarySettledReservedExample.output_ready⟩

end Yulang.GeneralDictionarySettledReservationTimeline
