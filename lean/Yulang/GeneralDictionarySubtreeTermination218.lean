import Yulang.GeneralDictionaryDefaultRegistered211
import Yulang.GeneralDictionaryDefaultExecutor208

/-! The unchanged EvidenceAt judgment asks for stability of the selected demand.
A generated subtree can be saturated while another ancestor still has work. -/
namespace Yulang.GeneralDictionarySubtreeTermination218
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalCenteredHeadMatStepJournal
open GeneralDictionaryDefaultBoundary208
open GeneralNominalSaturationState (Generated)
variable {roles : Roles.RoleDecls} {value : Registry} {root child : Occurrence roles}
variable {before after state : State roles}

theorem step_lift (generated : Generated before.core.erased.current root child)
    (step : Step value child before after) : Step value root before after := by
  obtain ⟨focus,within,action⟩ := step
  exact ⟨focus,GeneralNominalSaturationState.generated_trans generated within,action⟩

theorem generated_preserved (generated : Generated before.core.erased.current root child)
    (step : Step value root before after) : Generated after.core.erased.current root child :=
  GeneralDictionaryDefaultRegistered211.generated_growth (GeneralDictionaryDefaultGrowth208.step step)
    (GeneralDictionaryDefaultRegistered211.at_edges step.choose_spec.2) generated

theorem accessible (parent : Acc (fun next current => Step value root current next) state)
    (generated : Generated state.core.erased.current root child) :
    Acc (fun next current => Step value child current next) state := by
  induction parent with
  | intro state prior ih =>
    refine .intro state ?_
    intro after step
    have lifted := step_lift generated step
    exact ih after lifted (generated_preserved generated lifted)

theorem trace_lift (generated : Generated before.core.erased.current root child)
    (path : B4Target.Steps (Step value child) before after) :
    B4Target.Steps (Step value root) before after ∧ Generated after.core.erased.current root child := by
  induction path with
  | refl => exact ⟨.refl,generated⟩
  | tail path step ih =>
    have lifted := step_lift ih.2 step
    exact ⟨.tail ih.1 lifted,generated_preserved ih.2 lifted⟩

theorem terminal (checked : (boundary roles).Checked value)
    (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (generated : Generated state.core.erased.current root child) :
    let final := GeneralDictionaryDefaultExecutor208.terminalState value state child
    B4Target.Steps (Step value child) state final ∧
      B4TargetV7.Reachable (boundary roles) value root final ∧
      Generated final.core.erased.current root child ∧ Stable value final child := by
  have exit := GeneralDictionaryDefaultExecutor208.terminal_exit
    (accessible (GeneralDictionaryDefaultExecutor208.progress value checked state root reachable) generated)
  have lifted := trace_lift generated exit.1
  exact ⟨exit.1,B4TargetV5.reachable_steps _ reachable lifted.1,lifted.2,
    (GeneralDictionaryDefaultKernel208.closure exit.2).1⟩

end Yulang.GeneralDictionarySubtreeTermination218
