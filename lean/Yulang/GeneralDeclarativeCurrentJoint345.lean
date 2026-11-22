import Yulang.GeneralDeclarativeCurrentPosition345

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeCurrentJoint345
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedJournal232 (State Effect Models)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalCenteredHeadAllocEncoding (registry)
open GeneralNominalCenteredHeadMatStepRoles (Origin)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeEntailment320 (appendFacts model_append Holds)
open GeneralDeclarativeCurrentOrder345 (Row rows)
open GeneralDeclarativeStoppedOutput339 (Receipt)
open GeneralStoppedProjectedTrace335 (normalized)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (All₂)

def Attributed (r : Registry) (root : Occurrence rs) (final : State rs) (effect : Effect rs)
    (row : Row) (equation : Equation) : Prop :=
  Receipt final effect row.output equation ∧ equation.left = row.output.target ∧
    ∃ site : GeneralNominalDemandMerging.Site rs,
      final.core.erased.current.sites[row.physical]? = some site ∧
      site.occurrence.demand.outputs[row.ordinal]? = some row.output ∧
      GeneralNominalSaturationState.Alias final.core.erased.current
        effect.plan.packet.site.occurrence.identity site.occurrence.identity ∧
      Origin (registry r) final.core.erased.source.state.seed root site.occurrence

def Block (r : Registry) (root : Occurrence rs) (final : State rs)
    (effect : Effect rs) (equations : List Equation) : Prop :=
  All₂ (Attributed r root final effect) (rows final.core effect.plan.packet.site.occurrence) equations

theorem collect {r : Registry} {root : Occurrence rs} {final : State rs}
    {effects : List (Effect rs)} {m : Assignment} (packed : ∀ effect ∈ effects, ∃ equations : List Equation,
      Block r root final effect equations ∧ ∀ equation ∈ equations,Holds m equation) :
    ∃ blocks : List (List Equation), All₂ (Block r root final) effects blocks ∧
      ∀ equation ∈ blocks.flatten,Holds m equation := by
  induction effects with
  | nil => exact ⟨[],.nil,by intro _ h; cases h⟩
  | cons effect rest ih =>
    obtain ⟨equations,one,legal⟩ := packed effect List.mem_cons_self
    obtain ⟨blocks,later,valid⟩ := ih (fun e h => packed e (List.mem_cons_of_mem _ h))
    refine ⟨equations::blocks,.cons one later,?_⟩
    intro equation member
    rcases List.mem_append.mp member with first|second
    · exact legal equation first
    · exact valid equation second

/-- All retained historical effects can be read together, not just one
at a time. Every block uses the same actual final assignment, with
the final journal's list order and each class's literal physical
order/multiplicity. This list is not the elected dictionary tree. -/
theorem one_model {r : Registry} {root : Occurrence rs} {final : State rs}
    (checked : (boundary rs).Checked r)
    (reached : B4TargetV8.Reachable (boundary rs) r root final)
    (lowered : normalized final = some base) (m : Assignment) (fit : Models final m) :
    ∃ blocks : List (List Equation),
      All₂ (Block r root final) final.effects blocks ∧
      GeneralDeclarativeHead320.Models (appendFacts base blocks.flatten) m := by
  have baseOK := (GeneralStoppedLower335.exact_models _ m lowered).mpr fit.1.1
  have packed : ∀ effect ∈ final.effects, ∃ equations : List Equation,
      Block r root final effect equations ∧ ∀ equation ∈ equations,Holds m equation := by
    intro effect retained
    obtain ⟨equations,law,all⟩ := GeneralDeclarativeCurrentPosition345.attached checked reached retained lowered m fit
    exact ⟨equations,all,((model_append m).mp law).2⟩
  obtain ⟨blocks,exact,typed⟩ := collect packed
  exact ⟨blocks,exact,(model_append m).mpr ⟨baseOK,typed⟩⟩

end Yulang.GeneralDeclarativeCurrentJoint345
