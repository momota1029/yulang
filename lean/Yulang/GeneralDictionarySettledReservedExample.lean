import Yulang.GeneralDictionarySettledRecursiveExample
import Yulang.GeneralDictionaryReservedRefreshedStability

/-! The reserved-output fixture has a terminal packet, hence its output is
settled rather than a counterexample to the child-ledger condition. -/
namespace Yulang.GeneralDictionarySettledReservedExample
open GeneralDictionaryFiniteObservedExampleReserved
open GeneralDictionaryFiniteObservedExampleReservedPositive
open GeneralDictionaryFiniteObservedExample (registry declaration)
open GeneralDictionaryReservedNominalRefresh
open GeneralNominalSupport (Head)
open GeneralDeclarationExamples (roles)

private theorem initial_ready (slot : Fin 2) :
    GeneralNominalSettledSupport.ReadyAt start slot.val := by
  by_cases zero : slot.val = 0
  · have same : slot = 0 := Fin.ext zero
    subst slot
    exact ⟨_,_,Head.nominal (snapshot := state) (0 : Fin 2) _ rfl,
      GeneralNominalSettledSupport.source_head start (Head.nominal (snapshot := state) (0 : Fin 2) _ rfl)⟩
  · have same : slot = 1 := by apply Fin.ext; omega
    subst slot
    exact ⟨_,_,Head.scalar (snapshot := state) (1 : Fin 2) .int rfl,
      GeneralNominalSettledSupport.source_head start (Head.scalar (snapshot := state) (1 : Fin 2) .int rfl)⟩

theorem initial_decision : GeneralNominalSettledSupport.DecisionGuard registry start root :=
  ⟨fun _ => initial_ready 1,fun _ _ _ _ _ slot _ => initial_ready slot⟩

theorem install_step : GeneralNominalSettledSteps.Step registry root start installed :=
  ⟨root,.root,.install packet [] enabled novel ⟨GeneralNominalValueSupport.source_packet start packet guard,initial_decision⟩⟩

theorem equality_step : GeneralNominalSettledSteps.Step registry root installed GeneralDictionaryReservedEqualityStep.after := by
  exact ⟨root,.root,.administrative root _ (.equate root 2 0
    (GeneralNominalRefinements.sources (GeneralNominalRefinements.installed registry context root declaration [(1,1)]) 2 reserved_source)
    (GeneralNominalRefinements.sources (GeneralNominalRefinements.installed registry context root declaration [(1,1)]) 0
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨(0 : Fin 2),rfl⟩)))))
    GeneralDictionaryReservedOutputEquality.journal_equal GeneralDictionaryReservedEqualityStep.not_raw_equal)⟩

theorem refresh_step : GeneralNominalSettledSteps.Step registry root GeneralDictionaryReservedEqualityStep.after refreshed :=
  ⟨root,.root,.administrative root _ (.refresh root refreshedContext certificate 2 output_member
    GeneralDictionaryReservedSuccessorBoundary.output_not_known output_known)⟩

theorem reachable : B4TargetV5.Reachable (GeneralNominalSettledBoundary.boundary roles) registry root refreshed :=
  ⟨start,⟨context,initial_source,rfl⟩,.tail (.tail (.tail .refl install_step) equality_step) refresh_step⟩

theorem formed : GeneralNominalSettledSteps.SourceFormed registry root refreshed :=
  .update (.update (.update (.initial context initial_source) install_step) equality_step) refresh_step

theorem stable : GeneralNominalSettledSteps.Stable registry refreshed root :=
  fun focus reached next update => GeneralDictionaryReservedRefreshedStability.stable focus reached next
    (GeneralNominalSettledSteps.at_old update)

theorem packet_settled : GeneralNominalSettledSupport.PacketSettled refreshed.current packet := by
  refine ⟨?_,?_⟩
  · exact packet_recorded
  · intro child member
    rw [packet_children] at member
    cases member

theorem not_unsettled : ¬ GeneralNominalSettledSupport.Unsettled refreshed.current packet := by
  intro openPacket
  exact ((GeneralNominalSettledSupport.unsettled_iff packet_settled.1).mp openPacket) packet_settled

/-- The actual output journal entry is admitted by the new trust discipline. -/
theorem output_trusted : ∃ support,
    GeneralNominalSettledSupport.Trusted refreshed
      [GeneralNominalSupport.Fact.outputs packet support,GeneralNominalSupport.Fact.inputs packet support] := by
  obtain ⟨support,member⟩ := GeneralNominalSupportChoices.alternatives_exists start packet [] guard
  have input : GeneralNominalSupport.Fact.inputs packet support ∈ refreshed.facts := by
    apply List.mem_append_left
    apply List.mem_flatMap.mpr
    exact ⟨support,member,by simp⟩
  have output : GeneralNominalSupport.Fact.outputs packet support ∈ refreshed.facts := by
    apply List.mem_append_left
    apply List.mem_flatMap.mpr
    exact ⟨support,member,by simp⟩
  refine ⟨support,.output packet support (.input packet support .source input ?_) output (by simp) packet_settled⟩
  intro slot member test observation head model valid
  exact GeneralCanonicalObservations.recorded_sound _ model valid.1 (GeneralNominalSupport.head_recorded head)

theorem output_head_justified : GeneralNominalSettledSupport.HeadJustified refreshed 2 (.nominal 0 3) := by
  obtain ⟨support,trusted⟩ := output_trusted
  refine ⟨_,trusted,snapshot,_,Head.nominal (snapshot := snapshot) (2 : Fin 3) descriptor rfl,?_⟩
  intro model valid
  have all : GeneralNominalSupport.AllModels refreshed model := by
    refine ⟨valid.1,?_⟩
    intro fact member
    have facts : ∀ fact ∈ GeneralNominalSupportChoices.installedFacts start packet, fact.Holds model :=
      (GeneralNominalSupportChoices.facts_exact start packet [] guard model).mpr
        ⟨valid.2 (.inputs packet support) (by simp),valid.2 (.outputs packet support) (by simp)⟩
    apply facts fact
    simpa only [refreshed,GeneralDictionaryReservedEqualityStep.after,installed,
      GeneralNominalSupportSteps.install,GeneralNominalSupport.initial,List.append_nil] using member
  have models := (GeneralNominalSettledSteps.formed_exact formed model).mpr all
  exact GeneralCanonicalObservations.recorded_sound _ model models.1
    (GeneralNominalSupport.head_recorded (Head.nominal (snapshot := snapshot) (2 : Fin 3) descriptor rfl))

theorem output_ready : GeneralNominalSettledSupport.ReadyAt refreshed 2 :=
  ⟨_,_,Head.nominal (snapshot := snapshot) (2 : Fin 3) descriptor rfl,output_head_justified⟩

private theorem current_ready (slot : Fin 3) :
    GeneralNominalSettledSupport.ReadyAt refreshed slot.val := by
  have options : slot = 0 ∨ slot = 1 ∨ slot = 2 := by
    have := slot.isLt
    have : slot.val = 0 ∨ slot.val = 1 ∨ slot.val = 2 := by omega
    rcases this with h | h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Or.inl (Fin.ext h))
    · exact Or.inr (Or.inr (Fin.ext h))
  rcases options with rfl | rfl | rfl
  · exact ⟨_,_,Head.nominal (snapshot := snapshot) (0 : Fin 3) descriptor rfl,
      GeneralNominalSettledSupport.source_head refreshed (Head.nominal (snapshot := state) (0 : Fin 2) _ rfl)⟩
  · exact ⟨_,_,Head.scalar (snapshot := snapshot) (1 : Fin 3) .int rfl,
      GeneralNominalSettledSupport.source_head refreshed (Head.scalar (snapshot := state) (1 : Fin 2) .int rfl)⟩
  · exact output_ready

/-- This distinct query reads newly observed output 2. No claim that the query
has been enqueued or generated is made. -/
abbrev consumer : GeneralSourceDictionaries.Occurrence roles :=
  ⟨157,{root.demand with arguments := fun _ => (2,2)}⟩

theorem consumer_decision : GeneralNominalSettledSupport.DecisionGuard registry refreshed consumer :=
  ⟨fun _ => output_ready,fun _ _ _ _ _ slot _ => current_ready slot⟩

end Yulang.GeneralDictionarySettledReservedExample
