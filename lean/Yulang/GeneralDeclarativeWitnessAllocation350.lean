import Yulang.GeneralDeclarativeWitnessProjection349
import Yulang.GeneralDeclarativeWitnessExactProjection349
import Yulang.GeneralDeclarativeTaggedInputs340
import Yulang.GeneralDeclarativeWitnessLiteral349

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessAllocation350
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeGrowth327 (Extends)
open GeneralDeclarativeWitnessProjection349 (Checked)
open GeneralDeclarativeWitnessManifest349 (Manifest Attached support)
open GeneralDeclarativeEndpointOverlay336 (Entry footprintKeep receipts spans span_order)
open GeneralDeclarativeEndpointBatch336 (prepare)
open GeneralDeclarativeExactOverlay337 (ModelsExact)
open GeneralDeclarativeWitnessExactRest349 (Wire)
open GeneralDeclarativeWitnessProblem349 (splitAnd)
open GeneralNominalCommonBridge (Assignment)

variable {before : State} {manifest : Manifest} {source : Attached before manifest}

def next (out : Checked source arg pat) (keep : List Nat) : State :=
  prepare before (footprintKeep keep out.jobs) out.jobs.length

def used (out : Checked source arg pat) (keep : List Nat) : List (Nat × Capture) :=
  spans before (footprintKeep keep out.jobs) out.jobs

def entries (out : Checked source arg pat) (keep : List Nat) : List Entry :=
  receipts before (footprintKeep keep out.jobs) out.jobs

/-- Decode uses the anchored pre-allocation state and the actual normalized pattern.
It never computes freshness against the later state containing the allocated names. -/
theorem input (out : Checked source arg pat) (keep : List Nat) :
    GeneralDeclarativeTaggedInputs340.Input (support source) c i keep before arg pat
      (next out keep) (used out keep) (entries out keep) :=
  .prior (.record out.pattern out.source.fact out.generated)

def names (used : List (Nat × Capture)) : List (Nat × Nat × Nat × Nat) :=
  used.map (fun (binder,arg) => (binder,arg.lower,arg.center,arg.upper))

theorem exact_order (out : Checked source arg pat) (keep : List Nat) :
    (used out keep).map Prod.fst = (GeneralDeclarationPatterns.normalize pat).variables :=
  (span_order _ _ _).trans (GeneralDeclarativeWitnessProjection349.ordered out)

/-- This check compares the literal named slots, in sequence (including duplicate
binder positions), before deriving the actual model of the projection sidecar. -/
def check (out : Checked source arg pat) (keep : List Nat) (current : State)
    (reported : List (Nat × Nat × Nat × Nat)) (exact : List Wire) : Bool :=
  (GeneralDeclarativeWitnessLiteral349.preserves (next out keep) current &&
   decide (reported = names (used out keep))) &&
    GeneralDeclarativeWitnessExactProjection349.checkedList current (entries out keep) exact

theorem sound {out : Checked source arg pat} {keep current reported exact}
    (ok : check out keep current reported exact = true) :
    Extends (next out keep) current ∧
      reported = names (used out keep) ∧
      ∀ m : Assignment, Models current m → ModelsExact current (entries out keep) m := by
  have ⟨part,projections⟩ := splitAnd ok
  have ⟨growth,order⟩ := splitAnd part
  exact ⟨(GeneralDeclarativeWitnessLiteral349.preserves_iff _ _).mp growth,
    of_decide_eq_true order,fun m fit => GeneralDeclarativeWitnessExactProjection349.fixed_models projections m fit⟩

theorem observed {out : Checked source arg pat} {keep current reported exact}
    {c : GeneralDeclarationPatterns.Constructors} {i : GeneralNominalInspection.Interpretation}
    (ok : check out keep current reported exact = true) (m : Assignment) (fit : Models current m) :
    GeneralDeclarativeExactDictionary337.Observed c i m arg pat := by
  have ⟨later,_,holds⟩ := sound ok
  have assembled : GeneralDeclarativeTaggedInputs340.Inputs (support source) c i keep
      before [arg] [pat] (next out keep) (used out keep ++ []) (entries out keep ++ []) :=
    .cons (input out keep) .nil
  have reads : ∀ e ∈ entries out keep ++ [], GeneralDeclarativeExactOverlay337.Holds m e :=
    fun e p => (holds m fit).2 e (by simpa using p)
  cases GeneralDeclarativeTaggedInputs340.observed assembled
      (GeneralDeclarativeClauseBatch327.reflexive before) later m fit reads with
  | cons first _ => exact first

end Yulang.GeneralDeclarativeWitnessAllocation350
