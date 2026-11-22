import Yulang.GeneralDeclarativeOpenFixtureModel339
import Yulang.GeneralDeclarativeOpenSelected339

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
namespace Yulang.GeneralDeclarativeOpenFixtureWitness339
open GeneralDeclarativeOpenFixtureBase339
open GeneralDeclarativeOpenFixtureRoutes339
open GeneralDeclarativeOpenFixtureSelection339
open GeneralDeclarativeOpenFixtureModel339
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeExactOverlay337 (ModelsExact)
open GeneralDeclarativeCompoundDictionary338 (Evidence)
open GeneralDeclarativeOpenReceipt339 (receipt)
open GeneralDeclarativeGrowth327 (Extends trans)
open GeneralDeclarativeEntailment320 (model_append)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans)
open CommonNominalFullCarrier (Equivalent exactEmpty)
open GeneralDeclarativeExactDelete337 (subtract)
open GeneralDeclarativeHiddenDecl324 (interpretation)

theorem rootReceipt (m) (fit : ModelsExact final w2.reads m) : receipt m arg [7] outerTail := by
  have seeds : Extends initial rootFinal :=
    GeneralDeclarativeGrowth327.trans
      (GeneralDeclarativeCompoundTree338.tree_exact routed).1.1.1 root_grows
  have minted : routeOuterTail ∈ GeneralDeclarativeCompoundBatch338.minted
      initial [] keep outerTicket.jobs :=
    List.mem_cons_of_mem _ List.mem_cons_self
  have haveIt : routeOuterTail ∈ w2.reads := by
    rw [full_receipts]; exact List.mem_cons_of_mem _ List.mem_cons_self
  exact (GeneralDeclarativeOpenSelected339.output rootSelection outerTicket actual_open
    seeds minted haveIt rfl checked covered wanted m fit).2.2.1

/-- The same existing selected compiler consumes the actual native
residual address in the literal fixed root output. It does not use an
open-tail RHS as ordinary syntax for that output. -/
theorem rootOutput (m) (fit : ModelsExact final w2.reads m) :
    Equivalent (m 6).1 (subtract [7] (m 1).1) := by
  have inherited := (GeneralDeclarativeGrowth327.restrict child_grows m fit.1)
  have fixed := inherited.2 rootWrite (List.mem_append_right _ List.mem_cons_self)
  exact eqv_trans fixed (rootReceipt m fit).2.1

/-- No center RHS or tail-4 RHS is assumed. Independent old readiness,
native projected values, fixed writes, and recursing into the genuinely
emitted child hold in one actual model. -/
theorem actual_open_dictionary :
    ∃ m, ModelsExact final w2.reads m ∧
      Evidence registry interpretation m root dictionary ∧
      Equivalent (m 6).1 (subtract [7] (m 1).1) ∧ (m 11).1 = exactEmpty ∧ (m 17).1 = exactEmpty := by
  obtain ⟨m,fit,a,b⟩ := inhabited
  exact ⟨m,fit,every_model m fit,rootOutput m fit,a,b⟩

end Yulang.GeneralDeclarativeOpenFixtureWitness339
