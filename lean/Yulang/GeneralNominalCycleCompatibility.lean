import Yulang.GeneralNominalCycleBoundary
import Yulang.GeneralNominalSaturationInvariants

/-! The cycle-based updates strengthen the frozen transition contract. This
transport leaves Step, Stable and Committed unchanged and recovers the existing
journal invariants for every new update trace. -/
namespace Yulang.GeneralNominalCycleCompatibility

open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState

variable {roles : Roles.RoleDecls} {registry : Registry}

theorem selected_legacy (context : GeneralNominalCandidates.Context) (root : Occurrence roles)
    (selected : GeneralNominalCycleK2.Local registry context root (.selected key children)) :
    GeneralNominalLocalBoundary.Local (GeneralNominalLocalBoundary.recursiveFields roles)
      registry context root (.selected key children) := by
  cases selected with
  | selected safe unique =>
    refine .selected ⟨safe.1,?_,?_,fun pending => safe.2.2.2 (Or.inl pending)⟩ unique
    · intro old
      exact safe.2.2.2 (Or.inr ⟨safe.1,Or.inl ⟨old,safe.2.1⟩⟩)
    · intro old
      exact safe.2.2.2 (Or.inr ⟨safe.1,Or.inr ⟨old,safe.2.2.1⟩⟩)

theorem installable_legacy {state : State roles} {packet : Packet roles}
    (enabled : GeneralNominalCycleSteps.Installable registry state packet) :
    GeneralNominalSaturationSteps.Installable registry state packet := by
  obtain ⟨a,b,c,d,e,f,g,h,i,j,k,_⟩ := enabled
  exact ⟨a,b,c,d,e,f,g,selected_legacy _ _ h,i,j,k⟩

theorem update_legacy {before after : State roles} {focus : Occurrence roles}
    (update : GeneralNominalCycleSteps.At registry before focus after) :
    GeneralNominalSaturationSteps.At registry before focus after := by
  cases update with
  | enqueue focus linked absent => exact .enqueue focus linked absent
  | install packet emitted enabled novel => exact .install packet emitted (installable_legacy enabled) novel
  | merge first last one two same novel => exact .merge first last one two same novel
  | refresh focus context certificate source member unknown known =>
      exact .refresh focus context
        ⟨certificate.refines,certificate.interpretation,certificate.exact,certificate.support⟩ source member unknown known

theorem step_legacy {before after : State roles} {root : Occurrence roles}
    (step : GeneralNominalCycleSteps.Step registry root before after) :
    GeneralNominalSaturationSteps.Step registry root before after := by
  obtain ⟨focus,generated,update⟩ := step
  exact ⟨focus,generated,update_legacy update⟩

theorem steps_legacy {before after : State roles} {root : Occurrence roles}
    (path : B4Target.Steps (GeneralNominalCycleSteps.Step registry root) before after) :
    B4Target.Steps (GeneralNominalSaturationSteps.Step registry root) before after := by
  induction path with
  | refl => exact .refl
  | tail _ update ih => exact .tail ih (step_legacy update)

theorem generated_recorded {context : GeneralNominalCandidates.Context} {root child : Occurrence roles}
    {state : State roles}
    (path : B4Target.Steps (GeneralNominalCycleSteps.Step registry root) (initial context root) state)
    (generated : Generated state root child) : ∃ site ∈ state.sites, site.occurrence = child :=
  GeneralNominalSaturationInvariants.generated_recorded (steps_legacy path) generated

end Yulang.GeneralNominalCycleCompatibility
