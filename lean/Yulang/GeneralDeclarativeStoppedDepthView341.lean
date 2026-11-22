import Yulang.GeneralDeclarativeStoppedDepth341
import Yulang.GeneralDeclarativeStoppedDisplayModern341

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 34000
set_option maxHeartbeats 16000000
namespace Yulang.GeneralDeclarativeStoppedDepthView341
open GeneralDictionaryOutputDepth252 (sourceRegistry roles root interpretation declaration snapshot source_checked coverage)
open GeneralRebaseDepthScalar285 (target refreshed)
open GeneralRebaseDepthCommit285 (finalPlan)
open GeneralDeclarativeStoppedDepth341 (terminal classification only_root)
open GeneralDeclarativeStoppedRetarget340 (exact_requests exact_stopped_current row)
open GeneralStoppedOrdinarySite335 (demand)
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Demand)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeStoppedLower339 (lower exact_models)
open GeneralStoppedLower335 (normal original)
open GeneralDeclarativeEntailment320 (appendFacts Holds model_append)
open GeneralDeclarativeOrigins321 (Supported restriction backed_iff from_source)
open GeneralDeclarativeTaggedElection340 (Ranked Election tests Head)
open GeneralDeclarativePlainCapture323
open GeneralDeclarativeOpaqueNominal328 (point point_bounded)
open GeneralDeclarativeLowerKnown321 (alias_refl knows_row)
open GeneralDeclarativeTaggedInputs340 (Inputs)
open GeneralDeclarativeTaggedSelected340 (Selected)
open GeneralDeclarativeTaggedDictionary340 (Rule)
open GeneralDeclarativeNestedBody332 (compileBody)
open GeneralDeclarativeCurrentReceipt330 (Receipt literal)
open GeneralDeclarativeClauseBatch327 (reflexive)
open GeneralDeclarativeWitnessHead334 (full)
open GeneralDeclarativeOutputSource323 (Declared)
open CommonRoleOutermostResolver (All₂ Classify)

abbrev inputRow : Equation := ⟨2,.nominal 0 [.variable 0]⟩
abbrev outRow : Equation := ⟨3,.nominal 0 [.nominal 0 [.variable 2]]⟩
abbrev scalar (n : Nat) : Equation := ⟨n,.primitive (.scalar .int) []⟩
abbrev source : State := ⟨normal snapshot,[inputRow]⟩
noncomputable abbrev before : State := ⟨normal target.state,[inputRow]⟩
abbrev requested : Demand := ⟨0,[point 2],[⟨0,3⟩]⟩
abbrev used : List (Nat × Capture) := [(0,point 2)]
abbrev keep : List Nat := [0,1,2,3]
def fall (_ : Nat) : Capture := point 2
def targets (_ : GeneralDeclarations.Clause) (_ : Nat) : Nat := 3
def waiting (_ : Demand) (_ : GeneralDeclarations.Declaration) : Prop := False

theorem exact_source : lower snapshot = some source := rfl
theorem exact_before : lower target.state = some before := rfl
theorem raw_demand : demand GeneralDictionaryOutputDepth252.plan.input = requested := rfl

theorem exact_rhs : row = outRow := by
  have binder : finalPlan.binder 0 = 2 := by decide +kernel
  change (⟨3,.nominal 0 [.nominal 0 [.variable (finalPlan.binder 0)]]⟩ : Equation) = outRow
  rw [binder]

noncomputable abbrev final : State := appendFacts before [outRow]

theorem current_model (m : Assignment) (fit : GeneralNominalVersionedJournal232.Models refreshed m) :
    Models final m := by
  apply (model_append m).mpr
  refine ⟨(exact_models _ m exact_before).mpr fit.1.1,?_⟩
  intro e here
  cases List.mem_singleton.mp here
  rw [← exact_rhs]
  exact (exact_stopped_current m fit).2.1

noncomputable def support (done : Nat → Prop) : Supported final done :=
  original source final (fun row member => by cases List.mem_singleton.mp member; exact List.mem_append_left _ List.mem_cons_self) done

theorem authored (done : Nat → Prop) : inputRow ∈ (restriction (support done)).equations :=
  from_source _ ⟨List.mem_cons_self,rfl⟩

theorem no_promoted_targets (done : Nat → Prop) :
    outRow ∉ (restriction (support done)).equations ∧ scalar 0 ∉ (restriction (support done)).equations := by
  constructor <;> intro used
  all_goals
    obtain ⟨_,⟨old,_⟩,_⟩ := (backed_iff (support done) _).mp used
    have impossible := List.mem_singleton.mp old
    cases impossible

end Yulang.GeneralDeclarativeStoppedDepthView341
