import Yulang.GeneralNominalSettledSteps

/-! Dynamic settlement after an actual child installation. This is a sufficient
resumption contract, not construction of an installation from semantic Evidence.
In particular, existence/novelty of the terminal child install is explicit. -/
namespace Yulang.GeneralDictionarySettledConsumerResume
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport
open GeneralNominalSettledSupport (PacketSettled Trusted)
variable {roles : Roles.RoleDecls} {registry : Registry} {before after : Tracked roles}
variable {root focus : Occurrence roles} {producer leaf : Packet roles}

/-- The whole trusted ledger survives the real guarded transition. -/
theorem trusted_at (update : GeneralNominalSettledSteps.At registry before focus after)
    (trusted : Trusted before ledger) : Trusted after ledger :=
  GeneralNominalSettledSupport.trusted_monotone
    (GeneralNominalSupportSteps.at_source (GeneralNominalDownstreamSteps.at_old
      (GeneralNominalValueSteps.at_old (GeneralNominalSettledSteps.at_old update))))
    (GeneralNominalValueBudget.at_facts (GeneralNominalSettledSteps.at_old update))
    (fun _ done => GeneralNominalSettledSteps.settled_monotone update done) trusted

/-- A real leaf install, not just a selected semantic leaf, records a discharged
packet. There is no hypothesis claiming this leaf was already discharged. -/
theorem installed_leaf_discharged (support : List (Occurrence roles))
    (terminal : leaf.children = []) :
    Discharged (GeneralNominalSettledSteps.install before leaf support).current leaf.site.occurrence := by
  refine .packet leaf (List.mem_cons_self) ?_
  intro child member
  rw [terminal] at member
  cases member

/-- Existing siblings are transported; a matching child obtains its certificate
from the newly recorded terminal packet. Producer settlement is a conclusion. -/
theorem producer_settled_after_leaf (support : List (Occurrence roles))
    (enabled : GeneralNominalFeedbackSteps.Installable registry before.current leaf)
    (novel : ¬ GeneralNominalFeedbackSteps.Committed before.current leaf)
    (guard : GeneralNominalSettledSteps.PacketGuard before leaf support)
    (terminal : leaf.children = []) (present : producer ∈ before.current.packets)
    (others : ∀ child ∈ producer.children, child ≠ leaf.site.occurrence → Discharged before.current child) :
    PacketSettled (GeneralNominalSettledSteps.install before leaf support).current producer := by
  have update : GeneralNominalSettledSteps.At registry before leaf.site.occurrence
      (GeneralNominalSettledSteps.install before leaf support) := .install leaf support enabled novel guard
  refine ⟨GeneralNominalValueBudget.at_packets (GeneralNominalSettledSteps.at_old update) producer present,?_⟩
  intro child member
  by_cases same : child = leaf.site.occurrence
  · subst child
    exact installed_leaf_discharged support terminal
  · exact GeneralNominalValueBudget.at_discharged (GeneralNominalSettledSteps.at_old update) (others child member same)

/-- The producer's output entry is trusted after the actual leaf install.
Input trust and output membership refer to the old ledger, before settlement. -/
theorem producer_output_after_leaf (support dependencies : List (Occurrence roles))
    (enabled : GeneralNominalFeedbackSteps.Installable registry before.current leaf)
    (novel : ¬ GeneralNominalFeedbackSteps.Committed before.current leaf)
    (guard : GeneralNominalSettledSteps.PacketGuard before leaf support)
    (terminal : leaf.children = []) (present : producer ∈ before.current.packets)
    (others : ∀ child ∈ producer.children, child ≠ leaf.site.occurrence → Discharged before.current child)
    (trusted : Trusted before ledger) (input : Fact.inputs producer dependencies ∈ ledger)
    (output : Fact.outputs producer dependencies ∈ before.facts) :
    Trusted (GeneralNominalSettledSteps.install before leaf support)
      (Fact.outputs producer dependencies :: ledger) := by
  have update : GeneralNominalSettledSteps.At registry before leaf.site.occurrence
      (GeneralNominalSettledSteps.install before leaf support) := .install leaf support enabled novel guard
  exact .output producer dependencies (trusted_at update trusted)
    (GeneralNominalValueBudget.at_facts (GeneralNominalSettledSteps.at_old update) _ output) input
    (producer_settled_after_leaf support enabled novel guard terminal present others)

/-- Independent semantic readback from a specified finite fact list, without a
Trusted or DecisionGuard premise. Its certificate observes the current head. -/
def ExplainedRead (state : Tracked roles) (facts : List (Fact roles)) (identity : Nat) : Prop :=
  ∃ test observation, Head state.current.context.state identity test observation ∧
    ∀ model, GeneralNominalSettledSupport.Models state facts model → observation.Holds model

def ConsumerReads (registry : Registry) (state : Tracked roles)
    (facts : List (Fact roles)) (consumer : Occurrence roles) : Prop :=
  (∀ index, ExplainedRead state facts (consumer.demand.arguments index).1) ∧
  ∀ declaration ∈ registry.declarations, declaration.role = consumer.demand.role →
    ∀ bounds, GeneralNominalRecursiveCandidates.arguments state.current.context consumer = some bounds →
      ∀ slot ∈ readsMany state.current.context.state
        (GeneralNominalInspection.queries state.current.context.state state.current.context.interpretation declaration) bounds,
        ExplainedRead state facts (state.current.context.state.base.source slot)

theorem ready_of_explained (trusted : Trusted after facts) (read : ExplainedRead after facts identity) :
    GeneralNominalSettledSupport.ReadyAt after identity := by
  obtain ⟨test,observation,head,entailed⟩ := read
  exact ⟨test,observation,head,facts,trusted,after.current.context.state,observation,head,entailed⟩

theorem decision_of_reads (trusted : Trusted after facts)
    (reads : ConsumerReads registry after facts consumer) :
    GeneralNominalSettledSupport.DecisionGuard registry after consumer :=
  ⟨fun index => ready_of_explained trusted (reads.1 index),
    fun declaration visible same bounds located slot member =>
      ready_of_explained trusted (reads.2 declaration visible same bounds located slot member)⟩

/-- A generated consumer with independently enabled ordinary installation can
actually step once its readback is justified. Ordinary guards are not discarded. -/
theorem consumer_step (consumer : Packet roles) (support : List (Occurrence roles))
    (generated : Generated after.current root consumer.site.occurrence)
    (enabled : GeneralNominalFeedbackSteps.Installable registry after.current consumer)
    (novel : ¬ GeneralNominalFeedbackSteps.Committed after.current consumer)
    (oldGuard : GeneralNominalValueSupport.PacketGuard after consumer support)
    (trusted : Trusted after facts) (reads : ConsumerReads registry after facts consumer.site.occurrence) :
    GeneralNominalSettledSteps.Step registry root after (GeneralNominalSettledSteps.install after consumer support) := by
  refine ⟨consumer.site.occurrence,generated,.install consumer support enabled novel ⟨oldGuard,?_⟩⟩
  have guard := decision_of_reads trusted reads
  have context := enabled.1.2.1
  have reg := enabled.1.1
  simpa only [context,reg] using guard

/-- Actual two-step execution, retaining all the ordinary enablement checks.
The output's new trust is derived from the first step, not hypothesized. -/
theorem leaf_then_consumer (support dependencies consumerSupport : List (Occurrence roles))
    (leafGenerated : Generated before.current root leaf.site.occurrence)
    (enabled : GeneralNominalFeedbackSteps.Installable registry before.current leaf)
    (novel : ¬ GeneralNominalFeedbackSteps.Committed before.current leaf)
    (guard : GeneralNominalSettledSteps.PacketGuard before leaf support)
    (terminal : leaf.children = []) (present : producer ∈ before.current.packets)
    (others : ∀ child ∈ producer.children, child ≠ leaf.site.occurrence → Discharged before.current child)
    (trusted : Trusted before ledger) (input : Fact.inputs producer dependencies ∈ ledger)
    (output : Fact.outputs producer dependencies ∈ before.facts)
    (consumer : Packet roles)
    (consumerGenerated : Generated (GeneralNominalSettledSteps.install before leaf support).current root consumer.site.occurrence)
    (consumerEnabled : GeneralNominalFeedbackSteps.Installable registry
      (GeneralNominalSettledSteps.install before leaf support).current consumer)
    (consumerNovel : ¬ GeneralNominalFeedbackSteps.Committed
      (GeneralNominalSettledSteps.install before leaf support).current consumer)
    (consumerOldGuard : GeneralNominalValueSupport.PacketGuard
      (GeneralNominalSettledSteps.install before leaf support) consumer consumerSupport)
    (reads : ConsumerReads registry (GeneralNominalSettledSteps.install before leaf support)
      (Fact.outputs producer dependencies :: ledger) consumer.site.occurrence) :
    B4Target.Steps (GeneralNominalSettledSteps.Step registry root) before
      (GeneralNominalSettledSteps.install
        (GeneralNominalSettledSteps.install before leaf support) consumer consumerSupport) := by
  exact .tail (.tail .refl ⟨leaf.site.occurrence,leafGenerated,.install leaf support enabled novel guard⟩)
    (consumer_step consumer consumerSupport consumerGenerated consumerEnabled consumerNovel consumerOldGuard
      (producer_output_after_leaf support dependencies enabled novel guard terminal present others trusted input output) reads)

end Yulang.GeneralDictionarySettledConsumerResume
