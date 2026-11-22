import Yulang.GeneralDeclarativeCurrentJoint345

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeCurrentBodies345
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedJournal232 (State Effect Models)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalCenteredHeadAllocEncoding (registry)
open GeneralDeclarativeCurrentJoint345 (Block Attributed collect)
open GeneralDeclarativeCurrentOrder345 (rows outputs exact_row)
open GeneralDeclarativeCurrentPosition345 (align enrich)
open GeneralDeclarativeStoppedOrder339 (complete_known checked_order)
open GeneralDeclarativeStoppedOutput339 (Receipt row_present)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeEntailment320 (appendFacts model_append Holds)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (All₂)

theorem witnessed {r : Registry} {root : Occurrence rs} {final : State rs} {effect : Effect rs}
    (checked : (boundary rs).Checked r)
    (reached : B4TargetV8.Reachable (boundary rs) r root final)
    (retained : effect ∈ final.effects) (m : Assignment) (fit : Models final m) :
    ∃ equations : List Equation,
      Block r root final effect equations ∧ (∀ equation ∈ equations,Holds m equation) := by
  have ready := (GeneralDeclarativeCurrentHistory345.retained_ready checked reached retained).2
  obtain ⟨equations,ran⟩ := complete_known ready (fun _ h => h)
  obtain ⟨pointwise,_⟩ := checked_order (fun _ h => h) ran
  have sound : ∀ equation ∈ equations,Holds m equation := by
    intro equation selected
    obtain ⟨_,_,receipt⟩ := GeneralDeclarativeStoppedOrder339.member_authored pointwise selected
    exact (row_present retained receipt fit).1
  have origin := GeneralNominalVersionedMixedRoles235.reachable checked reached
  rw [← outputs] at pointwise
  refine ⟨equations,enrich (align pointwise) ?_,sound⟩
  intro row use equation receipt
  obtain ⟨site,atSite,atOut,alias⟩ := exact_row.mp use
  exact ⟨receipt,(row_present retained receipt fit).2,site,atSite,atOut,alias,
    origin.raw _ (List.mem_iff_getElem?.mpr ⟨_,atSite⟩)⟩

/-- Completed output RHS equations do not require the old point-only
whole-state normalizer. This does not lower unobserved/full source
descriptors and does not generate any new source author. -/
theorem independent {r : Registry} {root : Occurrence rs} {final : State rs}
    (checked : (boundary rs).Checked r)
    (reached : B4TargetV8.Reachable (boundary rs) r root final)
    (m : Assignment) (fit : Models final m) :
    ∃ blocks, All₂ (Block r root final) final.effects blocks ∧
      ∀ equation ∈ blocks.flatten,Holds m equation :=
  collect (fun _ retained => witnessed checked reached retained m fit)

theorem attach_any_base {r : Registry} {root : Occurrence rs} {final : State rs}
    (checked : (boundary rs).Checked r)
    (reached : B4TargetV8.Reachable (boundary rs) r root final)
    (m : Assignment) (fit : Models final m) (valid : GeneralDeclarativeHead320.Models base m) :
    ∃ blocks, All₂ (Block r root final) final.effects blocks ∧
      GeneralDeclarativeHead320.Models (appendFacts base blocks.flatten) m := by
  obtain ⟨blocks,exact,legal⟩ := independent checked reached m fit
  exact ⟨blocks,exact,(model_append m).mpr ⟨valid,legal⟩⟩

end Yulang.GeneralDeclarativeCurrentBodies345
