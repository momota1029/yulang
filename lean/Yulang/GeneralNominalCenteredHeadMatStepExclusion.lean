import Yulang.GeneralNominalCenteredHeadMatStepBoundary

namespace Yulang.GeneralNominalCenteredHeadMatStepExclusion
open GeneralNominalCenteredHeadMatStepJournal (State Effect)
open GeneralNominalCenteredHeadMatStepSupport (Fact Trusted)
open GeneralNominalCenteredHeadMatStepObservations
open GeneralCanonicalObservations (Observation Recorded)
variable {roles : Roles.RoleDecls} {state : State roles} {effect : Effect roles}

def Necessary (state : State roles) (effect : Effect roles) (observation : Observation) : Prop :=
  ∀ facts, Trusted state facts →
    (∀ model, GeneralNominalCenteredHeadMatStepSupport.Models state facts model → observation.Holds model) →
    Fact.output effect ∈ facts

theorem necessary_settled (needed : Necessary state effect observation)
    (justified : Justifies state observation.Holds) :
    GeneralNominalSettledSupport.PacketSettled state.core.erased.current effect.plan.packet := by
  obtain ⟨facts,trusted,sound⟩ := justified
  exact GeneralNominalCenteredHeadMatStepSupport.outputs_settled trusted (needed facts trusted sound)

theorem unsettled_no_refresh (needed : Necessary state effect observation)
    (unsettled : ¬ GeneralNominalSettledSupport.PacketSettled state.core.erased.current effect.plan.packet)
    (recorded : Recorded context.state observation) :
    ¬ Nonempty (GeneralNominalCenteredHeadMatStepRefresh.Refresh state context) := by
  rintro ⟨certificate⟩
  exact unsettled (necessary_settled needed (certificate.cache observation recorded))

theorem unsettled_no_reobserve (needed : Necessary state effect observation)
    (unsettled : ¬ GeneralNominalSettledSupport.PacketSettled state.core.erased.current effect.plan.packet)
    (recorded : Recorded revision.snapshot observation) :
    ¬ GeneralNominalCenteredHeadMatStepRefresh.Reobserve state revision :=
  fun certificate => unsettled (necessary_settled needed (certificate.cache observation recorded))

def UnsettledOnly (state : State roles) (effect : Effect roles) (identity : Nat) : Prop :=
  ∀ snapshot test observation, GeneralNominalSupport.Head snapshot identity test observation →
    Necessary state effect observation

theorem input_stays_unknown (valid : GeneralNominalCenteredHeadMatStepCache.Valid state)
    (needed : UnsettledOnly state effect identity)
    (unsettled : ¬ GeneralNominalSettledSupport.PacketSettled state.core.erased.current effect.plan.packet) :
    ¬ GeneralNominalState.Known state.core.erased.current.context.state identity := by
  intro known
  obtain ⟨test,observation,head⟩ := GeneralNominalCenteredHeadMatStepCache.known_has_head known
  exact unsettled (necessary_settled (needed _ test observation head)
    (valid observation (GeneralNominalSupport.head_recorded head)))

theorem reachable_pending
    (reachable : B4TargetV6.Reachable (GeneralNominalCenteredHeadMatStepBoundary.boundary roles) registry root state)
    (index : Fin (roles demand.demand.role).arity)
    (needed : UnsettledOnly state effect (demand.demand.arguments index).1)
    (unsettled : ¬ GeneralNominalSettledSupport.PacketSettled state.core.erased.current effect.plan.packet) :
    GeneralNominalCenteredHeadMatStepBoundary.Local registry state demand .pending :=
  .pending ⟨index,input_stays_unknown (GeneralNominalCenteredHeadMatStepBoundary.reachable_cache reachable) needed unsettled⟩

theorem necessity_of_cut
    (model : GeneralNominalCommonBridge.Assignment)
    (cut : ∀ facts, Trusted state facts → Fact.output effect ∉ facts →
      GeneralNominalCenteredHeadMatStepSupport.Models state facts model)
    (falseHead : ¬ observation.Holds model) : Necessary state effect observation := by
  classical
  intro facts trusted sound
  apply Classical.byContradiction
  intro absent
  exact falseHead (sound model (cut facts trusted absent))

end Yulang.GeneralNominalCenteredHeadMatStepExclusion
