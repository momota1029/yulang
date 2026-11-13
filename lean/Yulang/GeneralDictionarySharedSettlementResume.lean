import Yulang.GeneralDictionarySharedTrustTransport
import Yulang.GeneralDictionarySharedRecordedTree

/-! Actual terminal Shared installation can settle a recorded producer and
promote its certified output readback. Input trust, finite output recipes and
other siblings' recorded discharge remain explicit. No observed current head,
consumer applicability, novelty or successful consumer is inferred from trust. -/
namespace Yulang.GeneralDictionarySharedSettlementResume
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalSharedSupport
open GeneralNominalOriginTerms
variable {roles : Roles.RoleDecls} {registry : Registry} {before : Tracked roles}
variable {producer leaf : Packet roles}

theorem terminal_discharged (support : List (Occurrence roles)) (terminal : leaf.children = []) :
    Discharged (GeneralNominalSharedSteps.install before leaf support).current leaf.site.occurrence := by
  refine .packet leaf List.mem_cons_self ?_
  intro child member
  rw [terminal] at member
  cases member

theorem producer_settled (support : List (Occurrence roles))
    (enabled : GeneralNominalFeedbackSteps.Installable registry before.current leaf)
    (novel : ¬ GeneralNominalFeedbackSteps.Committed before.current leaf)
    (guard : GeneralNominalSharedSteps.PacketGuard before leaf support)
    (terminal : leaf.children = []) (present : producer ∈ before.current.packets)
    (others : ∀ child ∈ producer.children, child ≠ leaf.site.occurrence → Discharged before.current child) :
    GeneralNominalSettledSupport.PacketSettled (GeneralNominalSharedSteps.install before leaf support).current producer := by
  have update : GeneralNominalSharedSteps.At registry before leaf.site.occurrence
      (GeneralNominalSharedSteps.install before leaf support) := .install leaf support enabled novel guard
  refine ⟨GeneralDictionarySharedTrustTransport.at_packets update producer present,?_⟩
  intro child member
  by_cases same : child = leaf.site.occurrence
  · subst child
    exact terminal_discharged support terminal
  · exact GeneralDictionarySharedTrustTransport.at_discharged update (others child member same)

/-- Explicit leaf membership and missing discharge make the settlement change
strict. The earlier sufficient result alone permits already-settled producers. -/
theorem producer_becomes_settled (support : List (Occurrence roles))
    (enabled : GeneralNominalFeedbackSteps.Installable registry before.current leaf)
    (novel : ¬ GeneralNominalFeedbackSteps.Committed before.current leaf)
    (guard : GeneralNominalSharedSteps.PacketGuard before leaf support)
    (terminal : leaf.children = []) (present : producer ∈ before.current.packets)
    (child : leaf.site.occurrence ∈ producer.children)
    (missing : ¬ Discharged before.current leaf.site.occurrence)
    (others : ∀ child ∈ producer.children, child ≠ leaf.site.occurrence → Discharged before.current child) :
    GeneralNominalSettledSupport.Unsettled before.current producer ∧
    GeneralNominalSettledSupport.PacketSettled (GeneralNominalSharedSteps.install before leaf support).current producer :=
  ⟨⟨present,leaf.site.occurrence,child,missing⟩,
   producer_settled support enabled novel guard terminal present others⟩

/-- Same finite term substitution, because installation preserves the source
model basis used by this certificate; current contexts are not identified. -/
def installed_certificate (support : List (Occurrence roles))
    (certificate : OutputCertificate before ledger readbacks producer) :
    OutputCertificate (GeneralNominalSharedSteps.install before leaf support) ledger readbacks producer where
  substitution := certificate.substitution
  recipes := certificate.recipes
  inputs := certificate.inputs
  binders := certificate.binders
  uses := certificate.uses

theorem producer_output (support dependencies : List (Occurrence roles))
    (enabled : GeneralNominalFeedbackSteps.Installable registry before.current leaf)
    (novel : ¬ GeneralNominalFeedbackSteps.Committed before.current leaf)
    (guard : GeneralNominalSharedSteps.PacketGuard before leaf support)
    (terminal : leaf.children = []) (present : producer ∈ before.current.packets)
    (others : ∀ child ∈ producer.children, child ≠ leaf.site.occurrence → Discharged before.current child)
    (trusted : Trusted before ledger readbacks)
    (input : Fact.inputs producer dependencies ∈ ledger)
    (output : Fact.outputs producer dependencies ∈ before.facts)
    (certificate : OutputCertificate before ledger readbacks producer)
    (target : Nat) (term : Expr Nat)
    (recipe : Recipe (GeneralNominalPacketSupport.namedSchema producer) (.source target) term) :
    Trusted (GeneralNominalSharedSteps.install before leaf support)
      (Fact.outputs producer dependencies :: ledger)
      ((target,term.bind certificate.substitution) :: readbacks) := by
  have update : GeneralNominalSharedSteps.At registry before leaf.site.occurrence
      (GeneralNominalSharedSteps.install before leaf support) := .install leaf support enabled novel guard
  exact .output producer dependencies (installed_certificate support certificate) target term
    (GeneralDictionarySharedTrustTransport.trusted_at update trusted)
    (GeneralDictionarySharedTrustTransport.at_facts update _ output) input
    (producer_settled support enabled novel guard terminal present others) recipe

/-- A real step and newly promoted output readback. The conclusion is semantic
readback under its explicit ledger, not ReadyAt or successful consumer execution. -/
theorem leaf_step_and_readback (root : Occurrence roles) (support dependencies : List (Occurrence roles))
    (generated : Generated before.current root leaf.site.occurrence)
    (enabled : GeneralNominalFeedbackSteps.Installable registry before.current leaf)
    (novel : ¬ GeneralNominalFeedbackSteps.Committed before.current leaf)
    (guard : GeneralNominalSharedSteps.PacketGuard before leaf support)
    (terminal : leaf.children = []) (present : producer ∈ before.current.packets)
    (others : ∀ child ∈ producer.children, child ≠ leaf.site.occurrence → Discharged before.current child)
    (trusted : Trusted before ledger readbacks)
    (input : Fact.inputs producer dependencies ∈ ledger)
    (output : Fact.outputs producer dependencies ∈ before.facts)
    (certificate : OutputCertificate before ledger readbacks producer)
    (target : Nat) (term : Expr Nat)
    (recipe : Recipe (GeneralNominalPacketSupport.namedSchema producer) (.source target) term) :
    GeneralNominalSharedSteps.Step registry root before (GeneralNominalSharedSteps.install before leaf support) ∧
    ∀ model, GeneralNominalSharedSupport.Models (GeneralNominalSharedSteps.install before leaf support)
      (Fact.outputs producer dependencies :: ledger) model →
      Holds model (term.bind certificate.substitution) (.source target) := by
  refine ⟨⟨leaf.site.occurrence,generated,.install leaf support enabled novel guard⟩,?_⟩
  exact fun model valid => settled_readback
    (producer_output support dependencies enabled novel guard terminal present others trusted input output certificate target term recipe)
    List.mem_cons_self model valid
end Yulang.GeneralDictionarySharedSettlementResume
