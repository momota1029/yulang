import Yulang.GeneralDictionaryDefaultCodes208

/-! The finite support construction for the successor relation. The depth
premise is explicit; it refers to enabled novel installations of this Step. -/
namespace Yulang.GeneralDictionaryDefaultDepth208
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal GeneralDictionaryDefaultKernel208
open GeneralNominalInvocationAncestry (AtDepth frontier bounded_enumerated allocationPool allocation_member)
variable {roles : Roles.RoleDecls} {before after state : State roles} {effect : Effect roles}

theorem frame (enabled : Installable registry state effect) :
    GeneralNominalCenteredHeadOutputs.Frame registry state.core effect.plan.packet.site.occurrence
      effect.plan.packet.declaration.id effect.plan :=
  enabled.snapshot_eq ▸ enabled.registry_eq ▸ effect.frame

theorem configuration_step (step : Step registry root before after) :
    after.core.erased.current.context.state.seed = before.core.erased.current.context.state.seed ∧
    after.core.erased.current.context.state.constructors = before.core.erased.current.context.state.constructors ∧
    after.core.erased.current.context.interpretation = before.core.erased.current.context.interpretation := by
  obtain ⟨focus,_,action⟩ := step
  cases action with
  | administrative action =>
    cases action with
    | refresh _ certificate _ _ _ _ => exact ⟨certificate.refines.seed,certificate.refines.constructors,certificate.interpretation⟩
    | enqueue | equate | reobserve => exact ⟨rfl,rfl,rfl⟩
  | refresh focus context certificate source member unknown known =>
    exact ⟨certificate.refines.seed,certificate.refines.constructors,certificate.interpretation⟩
  | merge => exact ⟨rfl,rfl,rfl⟩
  | install effect enabled novel =>
    change effect.plan.packet.context.state.seed = before.core.erased.current.context.state.seed ∧
      effect.plan.packet.context.state.constructors = before.core.erased.current.context.state.constructors ∧
      effect.plan.packet.context.interpretation = before.core.erased.current.context.interpretation
    rw [(frame enabled).context_eq]
    exact ⟨rfl,rfl,rfl⟩

theorem configuration_trace (path : B4Target.Steps (Step registry root) before after) :
    after.core.erased.current.context.state.seed = before.core.erased.current.context.state.seed ∧
    after.core.erased.current.context.state.constructors = before.core.erased.current.context.state.constructors ∧
    after.core.erased.current.context.interpretation = before.core.erased.current.context.interpretation := by
  induction path with
  | refl => exact ⟨rfl,rfl,rfl⟩
  | tail path step ih =>
    have next := configuration_step step
    exact ⟨next.1.trans ih.1,next.2.1.trans ih.2.1,next.2.2.trans ih.2.2⟩

theorem plan_config (path : B4Target.Steps (Step registry root) (initial context root) state)
    (enabled : Installable registry state effect) :
    GeneralNominalCenteredHeadMatSemanticCodes.Config context effect.plan := by
  have config := configuration_trace path
  unfold GeneralNominalCenteredHeadMatSemanticCodes.Config
  rw [(frame enabled).context_eq]
  exact config

def InstalledDepthBound (registry : Registry) (context : GeneralNominalCandidates.Context)
    (root : Occurrence roles) (limit : Nat) : Prop :=
  ∀ state, B4Target.Steps (Step registry root) (initial context root) state → ∀ effect,
    GeneralNominalSaturationState.Generated state.core.erased.current root effect.plan.packet.site.occurrence →
    Installable registry state effect → ¬ Committed state effect.plan →
    ∃ depth, depth ≤ limit ∧ AtDepth registry context.state.seed root.identity depth effect.plan.packet.site.occurrence.identity

theorem installed_parents_finite (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (generated : GeneralNominalSaturationState.Generated state.core.erased.current root effect.plan.packet.site.occurrence)
    (enabled : Installable registry state effect) (novel : ¬ Committed state effect.plan) :
    effect.plan.packet.site.occurrence.identity ∈ frontier registry context.state.seed root.identity limit := by
  obtain ⟨depth,small,ancestry⟩ := bound state path effect generated enabled novel
  exact bounded_enumerated ancestry small

theorem reservations_finite (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (generated : GeneralNominalSaturationState.Generated state.core.erased.current root effect.plan.packet.site.occurrence)
    (enabled : Installable registry state effect) (novel : ¬ Committed state effect.plan) :
    GeneralNominalAllocation.reserved effect.plan.packet.context.state effect.plan.packet.registry effect.plan.packet.site.occurrence.identity ⊆
      allocationPool registry context.state.seed (frontier registry context.state.seed root.identity limit) := by
  intro identity member
  obtain ⟨key,present,rfl⟩ := List.mem_map.mp member
  have seed := (plan_config path enabled).1
  simpa only [GeneralNominalAllocation.source,seed,(frame enabled).registry_eq] using
    allocation_member (seed := context.state.seed) _ (installed_parents_finite bound path generated enabled novel)
      key ((frame enabled).registry_eq ▸ present)

end Yulang.GeneralDictionaryDefaultDepth208
