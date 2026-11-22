import Yulang.GeneralDeclarativeTaggedField340
import Yulang.GeneralDeclarativeEndpointBody336

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeTaggedParent340
open GeneralDeclarativeCompoundTree338
open GeneralDeclarativeCompoundBatch338 (Ticket minted)
open GeneralDeclarativeCompoundRoutes338 (dispatch dispatch_exact)
open GeneralDeclarativeCompoundSources338 (minted_valid)
open GeneralDeclarativeCompoundReadback338 (operandLow operandHigh)
open GeneralDeclarativeTaggedSources340 (merge)
open GeneralDeclarativeTaggedField340 (routed_whole)
open GeneralDeclarativeTaggedWhole340 (copied)
open GeneralDeclarativeStableReads329 (One)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeGrowth327 (fits)
open GeneralDeclarativeEndpointBody336 (Body calculate)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralDeclarativeNestedBody332 (compileBody)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarations (Checked Declaration Clause Registry)
open GeneralDeclarationPatterns (normalize normalizeArgs variablesArgs)
open GeneralCandidateInspection (plainNames)
open GeneralNominalCenteredHeadMatExpressions (translate)
open GeneralNominalCenteredHeadWFSource (Coverage)
open GeneralNominalInspection (Interpretation)

/-- A real record route with one joined field and an open binder tail:
its exact ordered forest is computed from the actual dispatch, not
from an arbitrarily supplied termination or target table. The field's
authorizing endpoints and reconstructing actual read are retained. -/
theorem normalized_parent {w : World done} (t : Ticket w.source arg fs)
    (peel : GeneralDeclarativeCompoundPattern338.peel pat = (fs,.var tailBinder))
    (routed : dispatch fs (minted w.state w.reads keep t.jobs) = some ([task],residual))
    (lower : merge tag (operandLow task.1.1) = some lo)
    (upper : merge tag (operandHigh task.1.1) = some hi)
    (already : normalize task.2 = task.2)
    (printed : normalize task.2 = .variant tag body)
    (plain : plainNames body = some order) (translated : translate c i body = some code) :
    ∃ v shared,
      TreeExact keep w pat v (copied shared order ++ [(tailBinder,residual.2)]) ∧
      One v.state c i task.1.2 task.2 (copied shared order) ∧
      v.reads = (advance w t keep).reads := by
  obtain ⟨v,shared,_,tree,head,exactReads⟩ := routed_whole t routed List.mem_cons_self lower upper printed plain translated
  rw [already] at tree
  have forest : ForestExact keep (advance w t keep) [task] v (copied shared order) := by
    have nil : ForestExact keep v [] v [] :=
      ⟨identity v keep,rfl,fun _ h => False.elim (List.not_mem_nil h)⟩
    simpa only [List.append_nil] using combine_fields tree nil
  have residualMinted : residual ∈ minted w.state w.reads keep t.jobs := by
    rw [(dispatch_exact routed).2.1]
    exact List.mem_append_right _ List.mem_cons_self
  have known := fits tree.1.1.1 (minted_valid t residualMinted)
  have tail : TreeExact keep v (.var tailBinder) v [(tailBinder,residual.2)] := by
    refine ⟨identity v keep,rfl,?_⟩
    intro x appears
    cases List.mem_singleton.mp appears
    exact known
  exact ⟨v,shared,combine_record t peel routed forest tail,head,exactReads⟩

/-- The existing ordered body compiler consumes a genuine nested
record capture certificate. This asserts exact signed-out children and
target table, not eligibility from the capture alone. -/
theorem compile_parent {w v : World done} {r : Registry} {d : Demand} {impl : Declaration} {i : Interpretation}
    (tree : TreeExact keep w (normalize pat) v used)
    (single : impl.head = [pat])
    (checked : Checked r) (covered : Coverage r i) (visible : impl ∈ r.declarations)
    (role : impl.role = d.role) (declared : Declared r d)
    (fallback : Nat → Capture) (targets : Clause → Nat → Nat) :
    ∃ result children, ∃ b : @Body r i d impl result children,
      compileBody r i d impl v.state used keep fallback targets = some (result,children) ∧
      b.spans = used ∧ b.targets = targets := by
  have order : used.map Prod.fst = impl.inputNames := by
    rw [GeneralDeclarations.Declaration.inputNames,single,tree.2.1]
    simp [normalizeArgs,variablesArgs]
  obtain ⟨result,kids,b,ran,_,uses,whereTargets,_,_⟩ :=
    calculate checked covered visible role declared keep fallback targets order tree.2.2
  exact ⟨result,kids,b,ran,uses,whereTargets⟩

end Yulang.GeneralDeclarativeTaggedParent340
