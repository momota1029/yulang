import Yulang.GeneralNominalVersionedMixedGrowth234
import Yulang.GeneralNominalVersionedMixedRecorded234
set_option backward.isDefEq.respectTransparency false
/-! Actual source reachability retains every installed parent's provenance and
ordered child edges. Historical commitment is not a current Frame certificate. -/
namespace Yulang.GeneralNominalVersionedMixedHistory235
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 GeneralNominalVersionedMixedKernel234
open GeneralNominalSaturationState (Generated)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}
  {before after state : State roles}

def Recorded (root : Occurrence roles) (state : State roles) : Prop :=
  ∀ effect ∈ state.effects,
    Generated state.core.erased.current root effect.plan.packet.site.occurrence ∧
    ∀ child ∈ GeneralNominalVersionedFrame231.children effect.plan.packet,
      (effect.plan.packet.site.occurrence,child) ∈ state.core.erased.current.edges

theorem lift (legacy : Legacy.State roles) : Recorded root (GeneralNominalVersionedJournal232.lift legacy) := by
  intro effect member
  cases member

theorem old_effect (growth : GeneralNominalVersionedMixedGrowth234.Monotone before after)
    (recorded : Recorded root before) (member : effect ∈ before.effects) :
    Generated after.core.erased.current root effect.plan.packet.site.occurrence ∧
    ∀ child ∈ GeneralNominalVersionedFrame231.children effect.plan.packet,
      (effect.plan.packet.site.occurrence,child) ∈ after.core.erased.current.edges :=
  ⟨GeneralNominalVersionedMixedGrowth234.generated growth (recorded effect member).1,
    fun child present => growth.edges ((recorded effect member).2 child present)⟩

theorem step (action : Step registry root before after) (recorded : Recorded root before) : Recorded root after := by
  obtain ⟨focus,generated,action⟩ := action
  have growth := GeneralNominalVersionedMixedGrowth234.at_growth action
  intro effect member
  cases action with
  | administrative action =>
    cases action <;> exact old_effect growth recorded member
  | refresh => exact old_effect growth recorded member
  | merge => exact old_effect growth recorded member
  | install added enabled novel =>
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨GeneralNominalVersionedMixedGrowth234.generated growth generated,
        fun child present => GeneralNominalVersionedInstall232.installed_child present⟩
    · exact old_effect growth recorded member

theorem steps (path : B4Target.Steps (Step registry root) before after)
    (recorded : Recorded root before) : Recorded root after := by
  induction path with
  | refl => exact recorded
  | tail _ action ih => exact step action ih

theorem reachable
    (path : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state) :
    Recorded root state := by
  obtain ⟨first,⟨legacy,_,same⟩,path⟩ := path
  subst first
  exact steps path (lift legacy)

theorem parent_generated
    (path : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state)
    (member : effect ∈ state.effects) :
    Generated state.core.erased.current root effect.plan.packet.site.occurrence := (reachable path effect member).1

theorem child_generated
    (path : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state)
    (member : effect ∈ state.effects)
    (present : child ∈ GeneralNominalVersionedFrame231.children effect.plan.packet) :
    Generated state.core.erased.current root child :=
  .child (parent_generated path member) ((reachable path effect member).2 child present)

theorem committed
    (path : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state)
    (member : effect ∈ state.effects) : Committed state effect.plan := by
  refine ⟨?_,(reachable path effect member).2⟩
  intro model valid
  exact ⟨GeneralNominalVersionedMixedRecorded234.reachable_effect_full_holds path valid member,
    (valid.2.2 effect member).2⟩

/-- No claim that the old packet's snapshot is the current frame. -/
theorem no_identical_reinstall
    (path : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state)
    (member : effect ∈ state.effects) : ¬ (¬ Committed state effect.plan) :=
  fun novel => novel (committed path member)

end Yulang.GeneralNominalVersionedMixedHistory235
