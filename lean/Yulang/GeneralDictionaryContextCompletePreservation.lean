import Yulang.GeneralNominalSupportSteps

/-! Context completeness survives actual administrative and merge updates.
Installation is intentionally excluded: a reachable supported installation can
add historical materialization obligations absent from raw constraints. -/
namespace Yulang.GeneralDictionaryContextCompletePreservation
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
variable {roles : Roles.RoleDecls}

/-- All output equations are present in the merged raw context. This result
does not require their entailment before merge, and does not preserve the old
model set or combine distinct Joint witnesses. -/
theorem merge_complete (state : State roles) (first last : GeneralNominalDemandMerging.Site roles)
    (complete : ContextComplete state) : ContextComplete (merge state first last) := by
  intro model valid
  have parts := (GeneralNominalState.extend_models _ _ _ model).mp valid
  exact (merge_models state first last model).mpr ⟨complete model parts.1,parts.2⟩

/-- Every existing administrative constructor preserves raw-to-journal
completeness, including descriptor revision and certified slot refresh. -/
theorem administrative_complete (registry : Registry) (before after : State roles)
    (focus : Occurrence roles)
    (update : GeneralNominalSupportSteps.Administrative registry before focus after)
    (complete : ContextComplete before) : ContextComplete after := by
  intro model valid
  cases update with
  | enqueue => exact (enqueue_models _ _ model).mpr (complete model valid)
  | refresh _ certificate _ _ _ _ =>
    exact (GeneralNominalCycleSteps.refresh_models certificate model).mpr
      (complete model (GeneralNominalRefinements.models certificate.refines model valid))
  | equate _ _ _ _ equal _ =>
    exact (GeneralNominalFeedbackSteps.equate_models _ _ _ equal model).mpr
      (complete model ((GeneralNominalState.extend_models _ _ _ model).mp valid).1)
  | reobserve _ certificate _ =>
    exact (certificate.exact model).mpr (complete model (certificate.raw model valid))

/-- No new transition system is defined: each link is an actual support Step,
with an additional administrative-or-merge endpoint certificate. -/
def OrdinaryEndpoints (registry : Registry) (root : Occurrence roles)
    (before after : GeneralNominalSupport.Tracked roles) : Prop :=
  GeneralNominalSupportSteps.Step registry root before after ∧
    ((∃ focus, GeneralNominalSupportSteps.Administrative registry before.current focus after.current) ∨
     ∃ first last : GeneralNominalDemandMerging.Site roles,
       after.current = merge before.current first last)

/-- Finite actual traces with administrative-or-merge endpoint descriptions preserve completeness.
The hypothesis at the START remains essential; reachability alone is not enough. -/
theorem described_trace_complete (registry : Registry) (root : Occurrence roles)
    (before after : GeneralNominalSupport.Tracked roles)
    (path : B4Target.Steps (OrdinaryEndpoints registry root) before after)
    (complete : ContextComplete before.current) : ContextComplete after.current := by
  induction path with
  | refl => exact complete
  | tail _ update ih =>
    rcases update.2 with ⟨focus,admin⟩ | ⟨first,last,same⟩
    · exact administrative_complete registry _ _ focus admin ih
    · rw [same]
      exact merge_complete _ first last ih

end Yulang.GeneralDictionaryContextCompletePreservation
