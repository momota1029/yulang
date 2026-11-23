import Yulang.GeneralDeclarativeWitnessVarianceReportFixture357

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 48000
set_option maxHeartbeats 59000000
namespace Yulang.GeneralDeclarativeWitnessGeneratedEndpoints357
open GeneralDeclarativeWitnessJoinedFixture357 (Data data root written layout test)
open GeneralDeclarativeWitnessJoinedCheck357 (Answer replay)
open GeneralDeclarativeWitnessDeclaredState357 (ModelsCurrent)
open GeneralDeclarativeWitnessVarianceModel357 (model views fits_data)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeHead320 (Models)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarativeWitnessCompiler350 (printDemand map_injective print_injective)
open CommonNominalFullCarrier (Ty Subtype Equivalent)
open PresenceNormalForm (Atom)

def cap : Capture := ⟨63,10,64⟩
def child : Demand := ⟨6,[cap],[]⟩

def links : List (Atom Nat) :=
  [.tyLe (.var 63) (.var 10),.tyLe (.var 10) (.var 63),
   .tyLe (.var 10) (.var 64),.tyLe (.var 64) (.var 10)]

def inspected (d : Data) : Bool :=
    d.wire.children == [printDemand child] &&
    links.all (fun a => decide (a ∈ d.current.ordinary.normal.ordinary)) &&
    (replay d.current root written layout d.wire).isSome

theorem genuine_nonpoint : ((data true).map inspected).getD false = true := by decide +kernel

theorem checked_link {d : Data} (found : data true = some d) :
    ∃ a : Answer d.current root d.wire,
      a.kids = [child] ∧
      (∀ m : Assignment,Models d.current.ordinary m →
        Equivalent (m cap.lower).1 (m cap.center).1 ∧ Equivalent (m cap.center).1 (m cap.upper).1) := by
  have accepted := genuine_nonpoint
  rw [found] at accepted
  have active : inspected d = true := accepted
  have ⟨compared,decoded⟩ := GeneralDeclarativeWitnessProblem349.splitAnd active
  have ⟨printed,rows⟩ := GeneralDeclarativeWitnessProblem349.splitAnd compared
  have eq : d.wire.children = [printDemand child] := beq_iff_eq.mp printed
  change (replay d.current root written layout d.wire).isSome = true at decoded
  cases result : replay d.current root written layout d.wire with
  | none => rw [result] at decoded; cases decoded
  | some a =>
    refine ⟨a,map_injective (fun h => print_injective h) (a.actualChildren.symm.trans eq),?_⟩
    intro m fit
    have formal (atom : Atom Nat) (here : atom ∈ links) :=
      fit.1.1 atom (of_decide_eq_true (List.all_eq_true.mp rows atom here))
    exact ⟨⟨formal (.tyLe (.var 63) (.var 10)) (by simp [links]),
        formal (.tyLe (.var 10) (.var 63)) (by simp [links])⟩,
      ⟨formal (.tyLe (.var 10) (.var 64)) (by simp [links]),
        formal (.tyLe (.var 64) (.var 10)) (by simp [links])⟩⟩

theorem child_not_point : cap.lower ≠ cap.center ∧ cap.center ≠ cap.upper := by decide +kernel

theorem actual_child_one_shared_model :
    ∃ (d : Data) (a : Answer d.current root d.wire),
      data true = some d ∧ ModelsCurrent d.current model views ∧ a.kids = [child] ∧
      Equivalent (model cap.lower).1 (model cap.center).1 ∧
      Equivalent (model cap.center).1 (model cap.upper).1 := by
  have accepted := genuine_nonpoint
  cases found : data true with
  | none => rw [found] at accepted; cases accepted
  | some d =>
    obtain ⟨run,kid,link⟩ := checked_link found
    have fit := fits_data found
    exact ⟨d,run,rfl,fit,kid,link model fit.1⟩

end Yulang.GeneralDeclarativeWitnessGeneratedEndpoints357
