import Yulang.GeneralDeclarativeWitnessCycle350
import Yulang.GeneralDeclarativeWitnessManifest349

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessCycleFixture350
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWitnessCycle350 (Wire check rooted)
open GeneralDeclarativeWitnessManifest349 (Manifest Attached cannot_promote support)
open GeneralDeclarativeOrigins321 (restriction)
open GeneralDeclarativePriority321 (RootRecurs)

def via : Equation := ⟨0,.variable 1⟩
def shape : Equation := ⟨1,.record 7 (.variable 2) (.primitive .emptyRecord [])⟩
def endAlias : Equation := ⟨2,.variable 0⟩
def state : State := ⟨⟨[],[]⟩,[via,shape,endAlias]⟩
def d : Demand := ⟨3,[⟨0,0,0⟩],[]⟩
def certificate : Wire := ⟨0,⟨1,.forward 0,2⟩,[],.forward 2⟩

theorem accepted : check state d certificate = true := by decide +kernel

theorem plain_alias_is_no_descent :
    check state d {certificate with first := ⟨0,.same,1⟩} = false := by decide +kernel

theorem wrong_root :
    check state {d with arguments := [⟨4,0,0⟩]} certificate = false := by decide +kernel

theorem wrong_closure : check state d {certificate with closeAt := .same} = false := by decide +kernel

def other : State := ⟨⟨[],[]⟩,
  [via,shape,⟨2,.variant 8 (.variable 2)⟩]⟩

/-- Even an independently cyclic descendant is not a closed path back
to the demanded root if the aliases and last return edge lack evidence. -/
theorem child_cycle_not_root :
    check other d {certificate with rest := [⟨2,.same,2⟩], closeAt := .same} = false := by decide +kernel

def empty : Manifest := ⟨[]⟩
def attached : Attached state empty := ⟨fun _ h => False.elim (List.not_mem_nil h)⟩

theorem unbacked_root :
    shape ∉ (restriction (support attached)).equations ∧ RootRecurs state d :=
  ⟨cannot_promote attached (fun x => False.elim (List.not_mem_nil x)),rooted accepted⟩

end Yulang.GeneralDeclarativeWitnessCycleFixture350
