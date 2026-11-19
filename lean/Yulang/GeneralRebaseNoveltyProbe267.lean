import Yulang.GeneralRebaseNoveltyBoundary267

namespace Yulang.GeneralRebaseNoveltyProbe267
open GeneralNominalCenters (Plan)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedInstallStep232 (Committed)
open GeneralRebaseInstallChecks267 (edgesRecorded semanticCommitted novel_exact)

def novel (state : State roles) (counterexample : Plan roles → Bool) (plan : Plan roles) : Bool :=
 !(edgesRecorded state.core.erased.current plan) || counterexample plan

theorem flags (state : State roles) (counterexample : Plan roles → Bool) (plan : Plan roles) :
 novel state counterexample plan = true ↔
 edgesRecorded state.core.erased.current plan = false ∨ counterexample plan = true := by
 cases h : edgesRecorded state.core.erased.current plan <;> simp [novel,h]

/-- A callback's positive result must certify non-entailment of the plan.
Failure of that callback is not in general a proof of commitment. -/
theorem sound (state : State roles) (counterexample : Plan roles → Bool) (plan : Plan roles)
 (certified : counterexample plan = true → ¬ semanticCommitted state plan)
 (fresh : novel state counterexample plan = true) : ¬ Committed state plan := by
 apply (novel_exact ..).mpr
 exact ((flags ..).mp fresh).imp id certified

theorem exact_on_complete_probe (state : State roles) (counterexample : Plan roles → Bool) (plan : Plan roles)
 (certified : counterexample plan = true ↔ ¬ semanticCommitted state plan) :
 novel state counterexample plan = true ↔ ¬ Committed state plan := by
 rw [flags,certified,novel_exact]

end Yulang.GeneralRebaseNoveltyProbe267
