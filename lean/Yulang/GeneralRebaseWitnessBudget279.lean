import Yulang.GeneralRebaseEdgeLedger279
import Yulang.GeneralRebaseBoundedInstallAcc277

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 24000
set_option maxHeartbeats 8800000
namespace Yulang.GeneralRebaseWitnessBudget279
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State Models Effect)
open GeneralNominalVersionedMixedKernel234 (Committed Installable Step)
open GeneralNominalVersionedMixedProgressSplit236 (Reachable InstallationDescent)
open GeneralNominalVersionedMixedAdministrative236 (Update)
open GeneralNominalVersionedInstall232 (install)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredHeadAllocEncoding (registry)
open GeneralRebaseInstallNovelty279 (Edge)
open GeneralNominalFiniteProgress (remaining remaining_monotone remaining_decreases)

inductive Fact (roles : Roles.RoleDecls) where
  | edge : Edge roles → Fact roles
  | removed : Assignment → Fact roles

def Holds (state : State roles) : Fact roles → Prop
  | .edge e => e ∈ state.core.erased.current.edges
  | .removed m => ¬ Models state m

structure WitnessBasis (r : Registry) (root : Occurrence roles) where
  facts : List (Fact roles)
  covers : ∀ before, Reachable r root before → ∀ effect, Installable (registry r) before effect →
    ¬ Committed before effect.plan → ∃ fact ∈ facts,
      ¬ Holds before fact ∧ Holds (install before effect) fact

theorem growth {before after : State roles}
    (edge : before.core.erased.current.edges ⊆ after.core.erased.current.edges)
    (restrict : ∀ m, Models after m → Models before m) :
    ∀ fact, Holds before fact → Holds after fact
  | .edge _, old => edge old
  | .removed m, old => fun valid => old (restrict m valid)

theorem administrative_growth (update : Update before after) :
    ∀ fact, Holds before fact → Holds after fact := by
  apply growth (before := before) (after := after)
  · cases update <;> exact fun _ h => h
  · intro model accepted
    cases update with
    | refresh context cert => exact (GeneralNominalVersionedMixedObservations233.refresh_models cert).mp accepted
    | equate => exact GeneralNominalVersionedAdministrative232.equate_models accepted
    | reobserve revision cert => exact (GeneralNominalVersionedMixedObservations233.reobserve_models cert).mp accepted
    | merge => exact GeneralNominalVersionedAdministrative232.merge_restrict accepted

theorem installation_growth {before : State roles} {eff : Effect roles}
    (snapshot : eff.snapshot = before.core) :
    ∀ fact, Holds before fact → Holds (install before eff) fact :=
  growth GeneralNominalVersionedInstallProperties232.edges_included
    (fun _ m => GeneralNominalVersionedInstall232.step_models snapshot m)

noncomputable def descent (basis : WitnessBasis r root) : InstallationDescent r root :=
  ⟨remaining Holds basis.facts,fun _ _ _ update =>
      remaining_monotone Holds basis.facts (administrative_growth update),
    fun before reached effect enabled novel => by
      obtain ⟨fact,listed,old,new⟩ := basis.covers before reached effect enabled novel
      exact remaining_decreases Holds basis.facts (installation_growth enabled.snapshot_eq) listed old new⟩

theorem accessible (basis : WitnessBasis r root) (reached : Reachable r root before) :
    Acc (fun next current => Step (registry r) root current next) before :=
  GeneralNominalVersionedMixedProgressSplit236.accessible_of_installation_descent (descent basis) reached

theorem consumed_edge {state : State roles} {effect : Effect roles} {child : Occurrence roles}
    (emitted : child ∈ GeneralNominalVersionedFrame231.children effect.plan.packet)
    (novel : (effect.plan.packet.site.occurrence,child) ∉ state.core.erased.current.edges) :
    ¬ Holds state (.edge (effect.plan.packet.site.occurrence,child)) ∧
      Holds (install state effect) (.edge (effect.plan.packet.site.occurrence,child)) :=
  ⟨novel,GeneralNominalVersionedInstall232.installed_child emitted⟩

theorem consumed_model {state : State roles} {effect : Effect roles} {m : Assignment}
    (was : Models state m) (lost : ¬ Models (install state effect) m) :
    ¬ Holds state (.removed m) ∧ Holds (install state effect) (.removed m) :=
  ⟨fun h => h was,lost⟩

end Yulang.GeneralRebaseWitnessBudget279
