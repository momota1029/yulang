import Yulang.GeneralDeclarativeCurrentReturned345

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeCurrentPosition345
open GeneralNominalVersionedJournal232 (State Effect Models)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary checked_compiled)
open GeneralNominalCenteredHeadAllocEncoding (registry)
open GeneralNominalCenteredHeadMatStepRoles (Origin)
open GeneralDeclarativeCurrentOrder345 (Row rows outputs exact_row)
open GeneralDeclarativeStoppedOutput339 (Receipt)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeEntailment320 (appendFacts)
open GeneralStoppedProjectedTrace335 (normalized)
open GeneralStoppedInstallHistory335 (InstalledBetween)
open GeneralSourceDictionaries (Occurrence)
open GeneralDeclarations (Registry)
open CommonRoleOutermostResolver (All₂)
open GeneralNominalCommonBridge (Assignment)

theorem align {P : GeneralSourceState.Output → Equation → Prop}
    {physical : List Row} {equations : List Equation} (placed : All₂ (fun o : GeneralSourceState.Output => fun e : Equation => P o e)
      (physical.map Row.output) equations) :
    All₂ (fun row eq => P row.output eq) physical equations := by
  induction physical generalizing equations with
  | nil => cases placed; exact .nil
  | cons first rest ih =>
    cases equations with
    | nil => cases placed
    | cons head tail =>
      cases placed with
      | cons hit later => exact .cons hit (ih later)

theorem enrich {as : List α} {bs : List β} {P Q : α → β → Prop}
    (linked : All₂ P as bs) (bridge : ∀ a ∈ as, ∀ b, P a b → Q a b) : All₂ Q as bs := by
  induction linked with
  | nil => exact .nil
  | cons here rest ih =>
    exact .cons (bridge _ List.mem_cons_self _ here) (ih (fun a member => bridge a (List.mem_cons_of_mem _ member)))

theorem attached {r : Registry} {root : Occurrence rs} {final : State rs} {effect : Effect rs}
    (checked : (boundary rs).Checked r)
    (reached : B4TargetV8.Reachable (boundary rs) r root final)
    (retained : effect ∈ final.effects) (lowered : normalized final = some base)
    (m : Assignment) (fit : Models final m) :
    ∃ (equations : List Equation),
      GeneralDeclarativeHead320.Models (appendFacts base equations) m ∧
      All₂ (fun row equation =>
        Receipt final effect row.output equation ∧ equation.left = row.output.target ∧
        ∃ site : GeneralNominalDemandMerging.Site rs,
          final.core.erased.current.sites[row.physical]? = some site ∧
          site.occurrence.demand.outputs[row.ordinal]? = some row.output ∧
          GeneralNominalSaturationState.Alias final.core.erased.current
            effect.plan.packet.site.occurrence.identity site.occurrence.identity ∧
          Origin (registry r) final.core.erased.source.state.seed root site.occurrence)
        (rows final.core effect.plan.packet.site.occurrence) equations := by
  obtain ⟨_,equations,_,_,_,valid,_,pointwise⟩ :=
    GeneralDeclarativeCurrentReturned345.output_receipts checked reached retained lowered m fit
  have inv := GeneralNominalVersionedMixedRoles235.reachable checked reached
  rw [← outputs] at pointwise
  have linked := align pointwise
  refine ⟨equations,?_⟩
  refine ⟨valid,?_⟩
  have work : ∀ row ∈ rows final.core effect.plan.packet.site.occurrence, ∀ equation,
      Receipt final effect row.output equation →
      Receipt final effect row.output equation ∧ equation.left = row.output.target ∧
        ∃ site : GeneralNominalDemandMerging.Site rs,
          final.core.erased.current.sites[row.physical]? = some site ∧
          site.occurrence.demand.outputs[row.ordinal]? = some row.output ∧
          GeneralNominalSaturationState.Alias final.core.erased.current
            effect.plan.packet.site.occurrence.identity site.occurrence.identity ∧
          Origin (registry r) final.core.erased.source.state.seed root site.occurrence := by
    intro row listed equation made
    obtain ⟨site,position,ordinal,alias⟩ := exact_row.mp listed
    obtain ⟨_,_,result⟩ := made.authored
    exact ⟨made,GeneralDeclarativeStoppedOutput339.fixed_target result,site,position,ordinal,alias,
      inv.raw _ (List.mem_iff_getElem?.mpr ⟨_,position⟩)⟩
  exact enrich linked work

end Yulang.GeneralDeclarativeCurrentPosition345
