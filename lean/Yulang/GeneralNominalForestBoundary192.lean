import Yulang.GeneralNominalForestProducer192
import Yulang.GeneralNominalCenteredHeadWFJoinCounterexample

/-! Exact limitation of the new certificate: allowing committed reuse does
not repair the existing multi-tag materialization obstruction. This is a
corollary of the existing WF counterexample, not a new language decision. -/
namespace Yulang.GeneralNominalForestBoundary192
open GeneralNominalCenteredHeadWFJoinSource
open GeneralNominalCenteredHeadWFJoinLocal
open GeneralNominalCenteredHeadWFJoinCounterexample
open GeneralNominalCenteredHeadStepEffects
open GeneralNominalCenteredHeadWFBoundary (boundary Local)
open GeneralNominalReusableForest192
open GeneralDictionaryReadback (Payload)

theorem no_build (payload : Payload) (after : State roles) :
    ¬ Build registry root start [root] [payload] after := by
  intro certificate
  obtain ⟨plan,support,focus,enabled⟩ := GeneralNominalForestProducer192.first_enabled certificate
  exact no_install plan focus support enabled

/-- This stronger-than-EvidenceNode producer is impossible for the current
WF boundary. This does NOT assert that EvidenceNode itself is false. -/
theorem not_universal_selected_build : ¬ (∀ (r : GeneralDeclarations.Registry),
    (boundary roles).Checked r → ∀ state focus key children,
    B4TargetV6.Reachable (boundary roles) r focus state →
    (boundary roles).Stable r state focus → Local r state focus (.selected key children) →
    ∃ after payload, Build r focus state [focus] [payload] after) := by
  intro producer
  obtain ⟨after,payload,certificate⟩ := producer registry ⟨rfl,checked⟩ start root 37 children
    reachable stable selected
  exact no_build payload after certificate

end Yulang.GeneralNominalForestBoundary192
