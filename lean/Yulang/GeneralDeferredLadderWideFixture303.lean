import Yulang.GeneralDeferredLadderEarlyExact303
import Yulang.GeneralDeferredLadderWiderRefresh303

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeferredLadderWideFixture303
open GeneralDeferredLadderLedger302 (Phase)
open GeneralDeferredLadderRefresh302 (promotedContext)
open GeneralDeferredLadderWiderRefresh303 (widerContext)
open GeneralDeferredLadderExact302 (RawStep Promotion promotion_legal)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralNominalVersionedInstall232 (install)
open GeneralNominalVersionedMixedObservations233 (Refresh)
open GeneralDeclarationExamples (roles)

abbrev context (p : Phase n k) := widerContext (promotedContext p) rfl
abbrev certificate (p : Phase n k) : Refresh p.state (context p) :=
  GeneralDeferredLadderWiderRefresh303.certificate p.state (promotedContext p)
    (GeneralDeferredLadderRefresh302.certificate p) rfl

theorem known (p : Phase n k) : GeneralNominalState.Known (context p).state (n+1) :=
  (GeneralDeferredLadderWiderRefresh303.known (promotedContext p) rfl _).mpr
    (GeneralDeferredLadderRefresh302.strict p)

theorem legal_distinct_refresh (p : Phase n k) :
    RawStep p.state (refresh p.state (context p)) ∧
    refresh p.state (context p) ≠ refresh p.state (promotedContext p) := by
  refine ⟨promotion_legal p _ ⟨context p,certificate p,known p,rfl⟩,?_⟩
  intro eq
  have same := congrArg (fun s : State roles => s.core.erased.current.context) eq
  exact GeneralDeferredLadderWiderRefresh303.nontrivial (promotedContext p) rfl same

theorem outside_old_family (p : Phase n k)
    (other : GeneralObservedLadderLedger301.Phase n k) :
    refresh p.state (context p) ≠ other.state := by
  intro eq
  have count := congrArg (fun st : State roles => st.core.erased.current.context.state.view.kinds) eq
  have none : other.state.core.erased.current.context.state.view.kinds = 0 := by
    rw [other.context_eq]
    rfl
  change 1 = other.state.core.erased.current.context.state.view.kinds at count
  omega

theorem wider_unique_install (p : Phase n k) (hi : k ≤ n) (s : State roles) :
    RawStep (refresh p.state (context p)) s ↔
      s = install (refresh p.state (context p))
        (GeneralDeferredLadderEarlyInstall303.effect p hi (context p) (certificate p)) :=
  GeneralDeferredLadderEarlyExact303.exact_next p hi (context p) (certificate p) (known p) s

end Yulang.GeneralDeferredLadderWideFixture303
