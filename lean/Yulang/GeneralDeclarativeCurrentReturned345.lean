import Yulang.GeneralDeclarativeCurrentHistory345

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeCurrentReturned345
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State Effect Models)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalCenteredHeadAllocEncoding (registry)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredHeadOutputs (requests)
open GeneralDeclarativeStoppedOrder339 (compileRequests installed_outputs)
open GeneralStoppedProjectedTrace335 (normalized)
open GeneralStoppedInstallHistory335 (InstalledBetween)
open GeneralDeclarativeStoppedOutput339 (Receipt)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeEntailment320 (appendFacts)
open CommonRoleOutermostResolver (All₂)
open B4Target (Steps)

/-- A finite actual path is enough to remove historical Ready from the
existing ordered output-receipt theorem. The named plan is still a
retained historical effect; this does not elect it at the end. -/
theorem output_receipts {r : Registry} {root : Occurrence rs}
    {final : State rs} {effect : Effect rs}
    (checked : (boundary rs).Checked r)
    (reachable : B4TargetV8.Reachable (boundary rs) r root final)
    (retained : effect ∈ final.effects) (lowered : normalized final = some base)
    (m : Assignment) (fit : Models final m) :
    ∃ start rows, (boundary rs).Initial r root start ∧
      compileRequests effect.plan (requests final.core effect.plan.packet.site.occurrence) = some rows ∧
      rows.map Equation.left = (requests final.core effect.plan.packet.site.occurrence).map GeneralSourceState.Output.target ∧
      GeneralDeclarativeHead320.Models (appendFacts base rows) m ∧
      InstalledBetween (registry r) root start final effect ∧
      All₂ (Receipt final effect) (requests final.core effect.plan.packet.site.occurrence) rows := by
  have ready := (GeneralDeclarativeCurrentHistory345.retained_ready checked reachable retained).2
  obtain ⟨start,initial,path⟩ := reachable
  obtain ⟨rows,ran,literal,modelled,origin,pointwise⟩ := installed_outputs path
    (GeneralDeclarativeCurrentHistory345.initially_empty initial) retained lowered ready m fit
  exact ⟨start,rows,initial,ran,literal,modelled,origin,pointwise⟩

/-- Conditional on the actual executor state being reached by the
given finite kernel trace; no property of other calls or of termination
is assumed. This is only the retained-output projection, not diagnosis
equivalence or a producer for uninstalled nodes. -/
theorem on_return {r : Registry} {root : Occurrence rs}
    {start : State rs} {effect : Effect rs}
    (e : B4TargetV3.Executor (GeneralNominalVersionedDiagnostic232.vocabulary rs))
    (checked : (boundary rs).Checked r) (initial : (boundary rs).Initial r root start)
    (trace : Steps (Step (registry r) root) start (e.run r start root).1)
    (retained : effect ∈ (e.run r start root).1.effects)
    (lowered : normalized (e.run r start root).1 = some base)
    (m : Assignment) (fit : Models (e.run r start root).1 m) :
    ∃ rows,
      rows.map Equation.left =
        (requests (e.run r start root).1.core effect.plan.packet.site.occurrence).map GeneralSourceState.Output.target ∧
      GeneralDeclarativeHead320.Models (appendFacts base rows) m ∧
      InstalledBetween (registry r) root start (e.run r start root).1 effect ∧
      All₂ (Receipt (e.run r start root).1 effect)
        (requests (e.run r start root).1.core effect.plan.packet.site.occurrence) rows := by
  have ready := (GeneralDeclarativeCurrentHistory345.retained_ready checked ⟨start,initial,trace⟩ retained).2
  obtain ⟨rows,_,exact,modelled,installed,ordered⟩ := installed_outputs trace
    (GeneralDeclarativeCurrentHistory345.initially_empty initial) retained lowered ready m fit
  exact ⟨rows,exact,modelled,installed,ordered⟩

end Yulang.GeneralDeclarativeCurrentReturned345
