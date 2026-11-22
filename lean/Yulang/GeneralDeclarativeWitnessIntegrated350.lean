import Yulang.GeneralDeclarativeWitnessUnfinished350
import Yulang.GeneralDeclarativeWitnessRecordWhole350

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessIntegrated350
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarations (Registry Declaration Checked)
open GeneralNominalInspection (Interpretation)
open GeneralNominalCenteredHeadWFSource (Coverage)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralDeclarativeEndpointOverlay336 (Entry)
open GeneralDeclarativeExactOverlay337 (ModelsExact)
open GeneralDeclarativeExactDictionary337 (Evidence)
open GeneralDeclarativeUnfinishedRoot330 (UnfinishedRoot)
open GeneralDeclarativeTaggedElection340 (Election guarded)
open CommonRoleOutermostResolver (Frontier Result Tree Dictionary Classify Resolves Summarizes All₂)

inductive Rule {s : State} (p : Supported s done) (sidecar : List Entry) (r : Registry)
    (i : Interpretation) (wait : Demand → Declaration → Prop) : Demand → Frontier Demand → Prop where
  | positive : GeneralDeclarativeTaggedDictionary340.Rule p sidecar r i wait d step →
      Rule p sidecar r i wait d step
  | rootK2 : UnfinishedRoot p d → Rule p sidecar r i wait d .rejected

theorem excludes_positive {s : State} {p : Supported s done}
    (cycle : UnfinishedRoot p d) (claim : Election p r i wait d impl) : False :=
  guarded claim (.inl (GeneralDeclarativeUnfinishedRoot330.blocked_and_cyclic cycle).2)

theorem actual_rejected {s : State} {p : Supported s done} (cycle : UnfinishedRoot p d) :
    Classify (Rule p sidecar r i wait) d .rejected :=
  ⟨.rejected,.rejected (.rootK2 cycle),.rejected⟩

section
variable {s : State} {p : Supported s done} {sidecar : List Entry} {r : Registry} {i : Interpretation}
  {wait : Demand → Declaration → Prop}
mutual
theorem positive_tree (d : Demand) (tree : Tree) (out : Dictionary)
    (derived : Resolves (Rule p sidecar r i wait) d tree)
    (printed : Summarizes tree (.selected out)) :
    Resolves (GeneralDeclarativeTaggedDictionary340.Rule p sidecar r i wait) d tree := by
  cases derived with
  | pending _ => cases printed
  | rejected _ => cases printed
  | ambiguous _ => cases printed
  | selected here others =>
    cases printed with
    | selected rest last =>
      cases last with
      | selected same =>
        subst_vars
        cases here with
        | positive pos => exact .selected pos (positive_forest _ _ _ others rest)
termination_by sizeOf tree

theorem positive_forest (ds : List Demand) (ts : List Tree) (dicts : List Dictionary)
    (derived : All₂ (Resolves (Rule p sidecar r i wait)) ds ts)
    (printed : All₂ Summarizes ts (dicts.map Result.selected)) :
    All₂ (Resolves (GeneralDeclarativeTaggedDictionary340.Rule p sidecar r i wait)) ds ts := by
  cases dicts with
  | nil => cases printed; cases derived; exact .nil
  | cons first more =>
    cases printed with
    | cons info rest =>
      cases derived with
      | cons here later => exact .cons (positive_tree _ _ _ here info) (positive_forest _ _ _ later rest)
termination_by sizeOf ts
end
end

/-- The explicit I-59 root rule does not change any proof of a positive
dictionary. A successful summary cannot use it at any depth. This is
only composition of the two checked fragments, not coverage of every
language diagnostic or an implementation correspondence. -/
theorem dictionary_sound {s : State} {p : Supported s done}
    (checked : Checked r) (covered : Coverage r i) (declared : Declared r d)
    (fit : ModelsExact s sidecar m) (chosen : Classify (Rule p sidecar r i wait) d (.selected out)) :
    Evidence r i m d out := by
  obtain ⟨tree,steps,printed⟩ := chosen
  exact GeneralDeclarativeTaggedDictionary340.dictionary_sound checked covered declared
    ⟨tree,positive_tree d tree out steps printed,printed⟩ fit

theorem checked_reject {pr : GeneralDeclarativeWitnessProblem349.Problem}
    {origins : GeneralDeclarativeWitnessOrigins350.Table}
    {code : GeneralDeclarativeWitnessUnfinished350.Wire}
    {report : GeneralDeclarativeWitnessTree349.Report}
    {sidecar : List Entry} {r : Registry} {i : Interpretation} {wait : Demand → Declaration → Prop}
    (passed : GeneralDeclarativeWitnessUnfinished350.checkResult pr origins code report = true) :
    report.tree = .rejected ∧ report.result = .rejected ∧ report.outputs = pr.demand.outputs ∧
      ∃ a : GeneralDeclarativeWitnessOrigins350.Attached pr.state origins,
        Classify (Rule (GeneralDeclarativeWitnessOrigins350.support a) sidecar r i wait) pr.demand report.result := by
  obtain ⟨certificate,_⟩ := GeneralDeclarativeWitnessProblem349.splitAnd passed
  obtain ⟨a,root⟩ := GeneralDeclarativeWitnessUnfinished350.checked certificate
  have exactMatch := GeneralDeclarativeWitnessUnfinished350.agrees_rejected passed
  exact ⟨exactMatch.1,exactMatch.2.1,exactMatch.2.2.1,a,
    exactMatch.2.1.symm ▸ actual_rejected root⟩

end Yulang.GeneralDeclarativeWitnessIntegrated350
