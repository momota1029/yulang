import Yulang.GeneralDictionarySharedTerminalObstruction

/-! The actual output ambiguity blocks certified input-head expansion, even
after arbitrary exact-refresh chains. This does not deny an independently
defined semantic Evidence judgment: no successful guarded installation is
manufactured from that judgment. -/
namespace Yulang.GeneralDictionarySharedBlockedOutput
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport

theorem head_known (head : Head snapshot identity test observation) :
    GeneralNominalState.Known snapshot identity := by
  cases head with
  | scalar slot base seen =>
    exact ⟨slot,rfl,Or.inl (by simp [GeneralNormalizedObservation.Snapshot.graph,seen,GeneralNormalizedObservation.Head.node])⟩
  | structural slot kind children seen =>
    exact ⟨slot,rfl,Or.inl (by simp [GeneralNormalizedObservation.Snapshot.graph,seen,GeneralNormalizedObservation.Head.node])⟩
  | nominal slot descriptor seen => exact ⟨slot,rfl,Or.inr ⟨descriptor,seen⟩⟩

theorem unknown_not_ready (state : Tracked roles) (identity : Nat)
    (unknown : ¬ GeneralNominalState.Known state.current.context.state identity) :
    ¬ GeneralNominalSharedSupport.ReadyAt state identity := by
  rintro ⟨test,observation,head,justified⟩
  exact unknown (head_known head)

theorem unknown_input_blocks (registry : Registry) (state : Tracked roles) (consumer : Occurrence roles)
    (index : Fin (roles consumer.demand.role).arity)
    (unknown : ¬ GeneralNominalState.Known state.current.context.state (consumer.demand.arguments index).1) :
    ¬ GeneralNominalSharedSupport.DecisionGuard registry state consumer :=
  fun guard => unknown_not_ready state _ unknown (guard.1 index)

/-- An inspected nested head, not only an argument's top level, can block. -/
theorem unknown_query_blocks (registry : Registry) (state : Tracked roles) (consumer : Occurrence roles)
    (declaration : Declaration) (member : declaration ∈ registry.declarations)
    (role : declaration.role = consumer.demand.role) (bounds)
    (located : GeneralNominalRecursiveCandidates.arguments state.current.context consumer = some bounds)
    (slot : Fin state.current.context.state.base.slots)
    (read : slot ∈ readsMany state.current.context.state
      (GeneralNominalInspection.queries state.current.context.state state.current.context.interpretation declaration) bounds)
    (unknown : ¬ GeneralNominalState.Known state.current.context.state (state.current.context.state.base.source slot)) :
    ¬ GeneralNominalSharedSupport.DecisionGuard registry state consumer :=
  fun guard => unknown_not_ready state _ unknown (guard.2 declaration member role bounds located slot read)

/-- Every exact-refresh continuation of the actual Shared terminal prefix still
blocks every consumer requiring this output as an input head, regardless of
which support list is proposed. No generated consumer is fabricated here. -/
theorem output_blocks_packet (registry : Registry) (after : Tracked GeneralDeclarationExamples.roles)
    (path : B4Target.Steps GeneralDictionaryExactRefreshChain.ExactRefresh
      GeneralDictionarySharedTerminalInstallation.after.current after.current)
    (consumer : Packet GeneralDeclarationExamples.roles)
    (index : Fin (GeneralDeclarationExamples.roles consumer.site.occurrence.demand.role).arity)
    (input : (consumer.site.occurrence.demand.arguments index).1 = GeneralNominalSupportSiblings.out)
    (enabled : GeneralNominalFeedbackSteps.Installable registry after.current consumer)
    (support : List (Occurrence GeneralDeclarationExamples.roles)) :
    ¬ GeneralNominalSharedSteps.PacketGuard after consumer support := by
  intro guard
  have decision : GeneralNominalSharedSupport.DecisionGuard consumer.registry after consumer.site.occurrence := by
    simpa only [enabled.1.2.1] using guard.2.1
  apply unknown_input_blocks consumer.registry after consumer.site.occurrence index _ decision
  rw [input]
  exact GeneralDictionarySharedTerminalObstruction.shared_unknown_after_exact_chain after.current path

theorem no_output_install_contract (registry : Registry) (after : Tracked GeneralDeclarationExamples.roles)
    (path : B4Target.Steps GeneralDictionaryExactRefreshChain.ExactRefresh
      GeneralDictionarySharedTerminalInstallation.after.current after.current)
    (consumer : Packet GeneralDeclarationExamples.roles)
    (index : Fin (GeneralDeclarationExamples.roles consumer.site.occurrence.demand.role).arity)
    (input : (consumer.site.occurrence.demand.arguments index).1 = GeneralNominalSupportSiblings.out) :
    ¬ ∃ support, GeneralNominalFeedbackSteps.Installable registry after.current consumer ∧
      ¬ GeneralNominalFeedbackSteps.Committed after.current consumer ∧
      GeneralNominalSharedSteps.PacketGuard after consumer support := by
  rintro ⟨support,enabled,novel,guard⟩
  exact output_blocks_packet registry after path consumer index input enabled support guard
end Yulang.GeneralDictionarySharedBlockedOutput
