import Yulang.GeneralDeferredLadderWiderView303
import Yulang.GeneralNominalVersionedMixedObservations233

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeferredLadderWiderRefresh303
open GeneralDeferredLadderWiderView303
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedMixedObservations233 (Refresh)
open GeneralNominalRecursiveCandidates (Context)

def widerContext (ctx : Context) (none : ctx.state.view.kinds = 0) : Context :=
  ⟨wider ctx.state none,ctx.interpretation⟩

def certificate (s : State roles) (ctx : Context) (before : Refresh s ctx) (none : ctx.state.view.kinds = 0) :
    Refresh s (widerContext ctx none) :=
  ⟨widen_refines before.refines none,before.interpretation,before.support,before.constraints,
    fun obs seen => before.cache obs (recorded ctx.state none obs seen)⟩

theorem known (ctx : Context) (none : ctx.state.view.kinds = 0) (source : Nat) :
    GeneralNominalState.Known (widerContext ctx none).state source ↔
      GeneralNominalState.Known ctx.state source :=
  known_iff ctx.state none source

theorem nontrivial (ctx : Context) (none : ctx.state.view.kinds = 0) :
    widerContext ctx none ≠ ctx := by
  intro same
  have count := congrArg (fun c : Context => c.state.view.kinds) same
  change 1 = ctx.state.view.kinds at count
  omega

end Yulang.GeneralDeferredLadderWiderRefresh303
