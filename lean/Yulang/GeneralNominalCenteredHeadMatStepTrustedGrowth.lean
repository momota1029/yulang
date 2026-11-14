import Yulang.GeneralNominalCenteredHeadMatStepKernel

set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralNominalCenteredHeadMatStepTrustedGrowth
open GeneralNominalCenteredHeadMatStepJournal (State)
open GeneralNominalCenteredHeadMatStepSupport
open GeneralNominalCenteredHeadMatStepObservations
variable {roles : Roles.RoleDecls} {before after : State roles}

structure Growth (before after : State roles) : Prop where
  source : after.core.erased.source = before.core.erased.source
  sourceSites : after.core.sourceSites = before.core.sourceSites
  sites : before.core.sites ⊆ after.core.sites
  plans : before.core.plans ⊆ after.core.plans
  effects : before.effects ⊆ after.effects
  rawSites : before.core.erased.current.sites ⊆ after.core.erased.current.sites
  packets : before.core.erased.current.packets ⊆ after.core.erased.current.packets
  aliases : before.core.erased.current.aliases ⊆ after.core.erased.current.aliases
  ordinary : before.core.erased.current.context.state.ordinary ⊆ after.core.erased.current.context.state.ordinary

theorem aliases (growth : Growth before after)
    (related : GeneralNominalSaturationState.Alias before.core.erased.current first last) :
    GeneralNominalSaturationState.Alias after.core.erased.current first last := by
  induction related with
  | refl => exact .refl _
  | edge member => exact .edge (growth.aliases member)
  | symm _ ih => exact .symm ih
  | trans _ _ first last => exact .trans first last

theorem discharged (growth : Growth before after)
    (done : GeneralNominalSupport.Discharged before.core.erased.current focus) :
    GeneralNominalSupport.Discharged after.core.erased.current focus := by
  induction done with
  | packet packet member children ih => exact .packet packet (growth.packets member) ih
  | alias first last one two same done ih =>
      exact .alias first last (growth.rawSites one) (growth.rawSites two) (aliases growth same) ih

theorem settled (growth : Growth before after)
    (done : GeneralNominalSettledSupport.PacketSettled before.core.erased.current packet) :
    GeneralNominalSettledSupport.PacketSettled after.core.erased.current packet :=
  ⟨growth.packets done.1,fun child member => discharged growth (done.2 child member)⟩

theorem slice_models (growth : Growth before after) : Models after facts model ↔ Models before facts model := by
  simp only [Models,growth.source,growth.sourceSites]

theorem trusted (growth : Growth before after) (proof : Trusted before facts) : Trusted after facts := by
  have sameModels : ∀ facts, Models after facts = Models before facts :=
    fun facts => funext (fun model => propext (slice_models (facts := facts) (model := model) growth))
  induction proof with
  | source => exact .source
  | input plan _ recorded readback ih =>
      exact .input plan ih (growth.plans recorded)
        (fun slot member test observation head model valid => readback slot member test observation head model
          ((slice_models growth).mp valid))
  | output effect _ recorded planRecorded input classReadback done ih =>
      apply Trusted.output effect ih (growth.effects recorded) (growth.plans planRecorded) input _ (settled growth done)
      intro site member alias
      rw [sameModels]
      exact classReadback site member alias
  | merge first last _ one two alias atoms holds same ih =>
      refine .merge first last ih (growth.sites one) (growth.sites two) (aliases growth alias)
        (fun atom member => growth.ordinary (atoms atom member))
        (fun model valid => holds model ((slice_models growth).mp valid)) ?_
      rw [sameModels]
      exact same

theorem justifies (growth : Growth before after) (given : Justifies before claim) : Justifies after claim := by
  obtain ⟨facts,proof,sound⟩ := given
  exact ⟨facts,trusted growth proof,fun model valid => sound model ((slice_models growth).mp valid)⟩

theorem cache (growth : Growth before after) (given : CacheSound before snapshot) : CacheSound after snapshot :=
  fun observation recorded => justifies growth (given observation recorded)

theorem administrative (action : GeneralNominalCenteredHeadMatStepKernel.Administrative before focus after) : Growth before after := by
  cases action with
  | enqueue linked absent =>
      exact ⟨rfl,rfl,fun _ h => h,fun _ h => h,fun _ h => h,fun _ h => List.mem_append_left _ h,
        fun _ h => h,fun _ h => h,fun _ h => h⟩
  | refresh context certificate source member unknown known =>
      exact ⟨rfl,rfl,fun _ h => h,fun _ h => h,fun _ h => h,fun _ h => h,
        fun _ h => h,fun _ h => h,fun _ h => certificate.refines.ordinary _ h⟩
  | equate first last one two equal novel =>
      exact ⟨rfl,rfl,fun _ h => h,fun _ h => h,fun _ h => h,fun _ h => h,
        fun _ h => h,fun _ h => h,fun _ h => List.mem_append_left _ h⟩
  | reobserve revision certificate improved =>
      exact ⟨rfl,rfl,fun _ h => h,fun _ h => h,fun _ h => h,fun _ h => h,
        fun _ h => h,fun _ h => h,fun _ h => h⟩

theorem at_growth (action : GeneralNominalCenteredHeadMatStepKernel.At registry before focus after) : Growth before after := by
  cases action with
  | administrative action => exact administrative action
  | refresh focus context certificate source member unknown known =>
      exact administrative (.refresh focus context certificate source member unknown known)
  | install effect enabled novel =>
      refine ⟨rfl,rfl,fun _ h => List.mem_append_left _ h,fun _ h => List.mem_cons_of_mem _ h,
        fun _ h => List.mem_cons_of_mem _ h,fun _ h => List.mem_append_left _ h,
        fun _ h => List.mem_cons_of_mem _ h,fun _ h => h,?_⟩
      have context := effect.frame.context_eq.trans (congrArg (fun state => state.erased.current.context) enabled.snapshot_eq)
      intro atom member
      have old : atom ∈ effect.plan.packet.context.state.ordinary := context.symm ▸ member
      exact List.mem_append_left _ (List.mem_append_left _ old)
  | merge first last one two same novel =>
      exact ⟨rfl,rfl,fun _ h => h,fun _ h => h,fun _ h => h,fun _ h => h,
        fun _ h => h,fun _ h => List.mem_cons_of_mem _ h,fun _ h => List.mem_append_left _ h⟩

theorem step (action : GeneralNominalCenteredHeadMatStepKernel.Step registry root before after) : Growth before after :=
  at_growth action.choose_spec.2

end Yulang.GeneralNominalCenteredHeadMatStepTrustedGrowth
