import Yulang.GeneralNominalCenteredHeadStepInstallationPermutation

set_option backward.isDefEq.respectTransparency false

/-! Two-way permutation simulation for all successor actions. Refresh uses
the original core-model certificate, unchanged. -/
namespace Yulang.GeneralNominalCenteredHeadStepSimulation
open GeneralDeclarations GeneralSourceDictionaries GeneralRegistryReordering GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects GeneralNominalCenteredHeadStepKernel
open GeneralNominalCenteredHeadStepInstallationPermutation (Corresponds)
open GeneralNominalCenteredCommitment (RecordedCommitted)
variable {roles : Roles.RoleDecls}
variable {before after state left right next final : State roles} {root focus : Occurrence roles}

theorem packet_at (action : At registry before focus after)
    (member : packet ∈ before.core.erased.current.packets) : packet ∈ after.core.erased.current.packets := by
  cases action with
  | administrative _ _ action => cases action <;> exact member
  | refresh => exact member
  | merge => exact member
  | install => exact List.mem_cons_of_mem _ member

theorem recorded_at (recorded : RecordedCommitted before.core) (action : At registry before focus after) :
    RecordedCommitted after.core := by
  have retain {packet} (valid : GeneralNominalFeedbackSteps.Committed before.core.erased.current packet) :
      GeneralNominalFeedbackSteps.Committed after.core.erased.current packet :=
    ⟨fun model models => valid.1 model ((at_extends action).journal.models model models),
      fun child member => (at_extends action).journal.edges _ (valid.2 child member)⟩
  intro packet member
  cases action with
  | administrative _ _ action => apply retain; cases action <;> exact recorded packet member
  | refresh => exact retain (recorded packet member)
  | merge => exact retain (recorded packet member)
  | install plan support enabled novel =>
      rcases List.mem_cons.mp member with rfl | member
      · exact GeneralNominalCenteredCommitment.installed_committed before.core plan support
      · exact retain (recorded packet member)

theorem recorded_trace (path : B4Target.Steps (Step registry root) (initial context root) state) : RecordedCommitted state.core := by
  induction path with
  | refl => intro _ member; cases member
  | tail _ step ih => exact recorded_at ih step.choose_spec.2

def Related (first last : Registry) (left right : State roles) : Prop :=
  Corresponds first last left right ∧ RecordedCommitted left.core ∧ RecordedCommitted right.core

theorem related_symm (same : Related first last left right) : Related last first right left := by
  obtain ⟨table,rebased,recorded,core⟩ := same.1.1
  have effects := (GeneralNominalCenteredHeadStepEffectPermutation.Related.symm ⟨core,same.1.2⟩).effects
  exact ⟨⟨GeneralNominalCenteredPermutationSymmetry.corresponds_symm same.1.1,effects⟩,same.2.2,same.2.1⟩

theorem at_forward (order : Reorders first last) (roleEq : first.roles = roles)
    (same : Related first last left right) (action : At first left focus next) :
    ∃ other, At last right focus other ∧ Related first last next other := by
  obtain ⟨table,rebased,recorded,core⟩ := same.1.1
  have finish {next other} (one : At first left focus next) (two : At last right focus other)
      (cores : GeneralNominalCenteredLedgerPermutation.Related (GeneralNominalCenteredPermutationRepresentation.paired table) next.core other.core)
      (effects : GeneralNominalLedgerPermutation.All₂ GeneralNominalCenteredHeadStepEffectPermutation.EffectPair next.effects other.effects) :
      Related first last next other :=
    ⟨⟨⟨table,rebased,fun a b member => ⟨packet_at one (recorded a b member).1,packet_at two (recorded a b member).2⟩,
      cores⟩,effects⟩,recorded_at same.2.1 one,recorded_at same.2.2 two⟩
  cases action with
  | administrative focus after action =>
      obtain ⟨other,actionOther,paired⟩ := core.administrative action last
      exact ⟨administrative right other,.administrative focus other actionOther,
        finish (.administrative focus after action) (.administrative focus other actionOther) paired same.1.2⟩
  | refresh focus context certificate source member unknown known =>
      have actionOther : At last right focus (refresh right context) :=
        .refresh focus context (core.refresh_certificate certificate) source
          ((GeneralNominalMetadataEquivalence.sources core.erased.current.context.state source).mp member)
          (fun present => unknown ((GeneralNominalMetadataEquivalence.known core.erased.current.context.state source).mpr present)) known
      exact ⟨refresh right context,actionOther,
        finish (.refresh focus context certificate source member unknown known) actionOther (core.refresh context) same.1.2⟩
  | merge a b support one two inputs novel guard =>
      have models := funext (fun model => propext (core.models model))
      have actionOther : At last right a.occurrence (merge right a b support) :=
        .merge a b support ((core.sites a).mp one) ((core.sites b).mp two) (models ▸ inputs)
          (fun alias => novel ((core.erased.current.alias _ _).mpr alias)) ((core.erased.merge_guard _ _ _).mp guard)
      exact ⟨merge right a b support,actionOther,
        finish (.merge a b support one two inputs novel guard) actionOther (core.merge a b support) same.1.2⟩
  | install plan support enabled novel =>
      obtain ⟨other,nextEnabled,nextNovel,matched,paired⟩ :=
        GeneralNominalCenteredHeadStepInstallationPermutation.counterpart_enabled same.1 order roleEq same.2.1 same.2.2 enabled novel
      have one := At.install plan support enabled novel
      have two := At.install other support nextEnabled nextNovel
      exact ⟨install right other support nextEnabled,matched.packet.site ▸ two,
        paired,recorded_at same.2.1 one,recorded_at same.2.2 two⟩

theorem step_forward (order : Reorders first last) (roleEq : first.roles = roles)
    (same : Related first last left right) (step : Step first root left next) :
    ∃ other, Step last root right other ∧ Related first last next other := by
  obtain ⟨focus,generated,action⟩ := step
  obtain ⟨other,nextAction,paired⟩ := at_forward order roleEq same action
  obtain ⟨_,_,_,core⟩ := same.1.1
  exact ⟨other,⟨focus,(core.erased.current.generated root focus).mp generated,nextAction⟩,paired⟩

theorem step_backward (order : Reorders first last) (roleEq : first.roles = roles)
    (same : Related first last left right) (step : Step last root right next) :
    ∃ other, Step first root left other ∧ Related first last other next := by
  obtain ⟨other,step,paired⟩ := step_forward (GeneralRegistryChildOrder.reorders_symm order)
    (order.2.1.symm.trans roleEq) (related_symm same) step
  exact ⟨other,step,related_symm paired⟩

theorem observations (roleEq : registry.roles = roles) (same : Related first last left right) (demand frontier) :
    GeneralNominalCenteredHeadStepBoundary.Local registry left demand frontier ↔
      GeneralNominalCenteredHeadStepBoundary.Local registry right demand frontier := by
  obtain ⟨_,_,_,core⟩ := same.1.1
  exact GeneralNominalCenteredHeadStepObservationPermutation.local_iff ⟨core,same.1.2⟩ registry roleEq demand frontier

theorem steps_backward (order : Reorders first last) (roleEq : first.roles = roles)
    (same : Related first last left right) (path : B4Target.Steps (Step last root) right final) :
    ∃ result, B4Target.Steps (Step first root) left result ∧ Related first last result final := by
  induction path with
  | refl => exact ⟨left,.refl,same⟩
  | tail _ step ih =>
      obtain ⟨previous,trace,paired⟩ := ih
      obtain ⟨next,edge,nextPair⟩ := step_backward order roleEq paired step
      exact ⟨next,.tail trace edge,nextPair⟩

theorem halt_reflects (order : Reorders first last) (roleEq : first.roles = roles)
    (same : Related first last left right) (halted : ∀ next, ¬ Step last root right next) :
    ∀ next, ¬ Step first root left next := by
  intro next step
  obtain ⟨other,edge,_⟩ := step_forward order roleEq same step
  exact halted other edge

end Yulang.GeneralNominalCenteredHeadStepSimulation
