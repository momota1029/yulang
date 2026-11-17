import Yulang.GeneralNominalVersionedGrowth233
import Yulang.GeneralNominalVersionedObservations233
set_option backward.isDefEq.respectTransparency false
/-! Versioned support preservation along the actual kernel's structural growth.
Settlement follows versioned children only. Cache preservation holds for a fixed
snapshot; this does not replace Kernel232's cache eligibility interface or prove
that every newly recorded observation has a versioned trusted derivation. -/
namespace Yulang.GeneralNominalVersionedSupportGrowth233
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedSupport233
open GeneralNominalVersionedGrowth233 (Monotone)
open GeneralNominalVersionedObservations233 (CacheSound Cut)
variable {roles : Roles.RoleDecls} {before after : State roles}

theorem discharged (growth : Monotone before after) (done : Discharged before focus) : Discharged after focus := by
  induction done with
  | packet plan member children ih => exact .packet plan (growth.plans member) ih
  | alias first last one two same done ih =>
    exact .alias first last (growth.legacy.rawSites one) (growth.legacy.rawSites two)
      (GeneralNominalCenteredHeadMatStepTrustedGrowth.aliases growth.legacy same) ih

theorem settled (growth : Monotone before after) (done : PacketSettled before plan) : PacketSettled after plan :=
  ⟨growth.plans done.1,fun child member => discharged growth (done.2 child member)⟩

theorem slice_models (growth : Monotone before after) :
    SliceModels after facts model ↔ SliceModels before facts model := by
  simp only [SliceModels,growth.legacy.source,growth.legacy.sourceSites]

theorem readback (growth : Monotone before after) (given : Readback before facts plan) : Readback after facts plan :=
  fun slot member test observation head model valid =>
    given slot member test observation head model ((slice_models growth).mp valid)

theorem class_readback (growth : Monotone before after) (given : ClassReadback before facts effect) :
    ClassReadback after facts effect := by
  have same : SliceModels after facts = SliceModels before facts :=
    funext (fun model => propext (slice_models (facts := facts) (model := model) growth))
  unfold ClassReadback
  rw [same]
  exact given

theorem trusted (growth : Monotone before after) (proof : Trusted before facts) : Trusted after facts := by
  have sameModels : ∀ facts, SliceModels after facts = SliceModels before facts :=
    fun facts => funext (fun model => propext (slice_models (facts := facts) (model := model) growth))
  induction proof with
  | source => exact .source
  | input plan _ recorded reads ih => exact .input plan ih (growth.plans recorded) (readback growth reads)
  | output effect _ recorded planRecorded input reads done ih =>
    exact .output effect ih (growth.effects recorded) (growth.plans planRecorded) input
      (class_readback growth reads) (settled growth done)
  | merge first last _ one two alias atoms holds same ih =>
    refine .merge first last ih (growth.legacy.sites one) (growth.legacy.sites two)
      (GeneralNominalCenteredHeadMatStepTrustedGrowth.aliases growth.legacy alias)
      (fun atom member => growth.legacy.ordinary (atoms atom member))
      (fun model valid => holds model ((slice_models growth).mp valid)) ?_
    rw [sameModels]
    exact same

theorem justified (growth : Monotone before after) (given : HeadJustified before identity test) :
    HeadJustified after identity test := by
  obtain ⟨facts,proof,snapshot,observation,head,sound⟩ := given
  exact ⟨facts,trusted growth proof,snapshot,observation,head,
    fun model valid => sound model ((slice_models growth).mp valid)⟩

theorem cache (growth : Monotone before after) (given : CacheSound before snapshot) : CacheSound after snapshot := by
  intro observation recorded
  obtain ⟨facts,proof,sound⟩ := given observation recorded
  exact ⟨facts,trusted growth proof,fun model valid => sound model ((slice_models growth).mp valid)⟩

theorem cut_restrict (growth : Monotone before after) (given : Cut after model) : Cut before model :=
  fun facts proof => (slice_models growth).mp (given facts (trusted growth proof))

theorem step_trusted (action : GeneralNominalVersionedKernel232.Step registry root before after)
    (proof : Trusted before facts) : Trusted after facts := trusted (GeneralNominalVersionedGrowth233.step action) proof

theorem steps_trusted (path : B4Target.Steps (GeneralNominalVersionedKernel232.Step registry root) before after)
    (proof : Trusted before facts) : Trusted after facts := trusted (GeneralNominalVersionedGrowth233.steps path) proof

theorem step_cache (action : GeneralNominalVersionedKernel232.Step registry root before after)
    (given : CacheSound before snapshot) : CacheSound after snapshot := cache (GeneralNominalVersionedGrowth233.step action) given

theorem steps_cache (path : B4Target.Steps (GeneralNominalVersionedKernel232.Step registry root) before after)
    (given : CacheSound before snapshot) : CacheSound after snapshot := cache (GeneralNominalVersionedGrowth233.steps path) given

theorem steps_settled (path : B4Target.Steps (GeneralNominalVersionedKernel232.Step registry root) before after)
    (done : PacketSettled before plan) : PacketSettled after plan := settled (GeneralNominalVersionedGrowth233.steps path) done

end Yulang.GeneralNominalVersionedSupportGrowth233
