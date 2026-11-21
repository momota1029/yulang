import Yulang.GeneralWherePhysicalOldInstall319
import Yulang.GeneralWherePhysicalPointLift319

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 23000000
namespace Yulang.GeneralWherePhysicalReobserve319
open GeneralWhereOriginSingleSource318
open GeneralWherePhysicalOldInstall319 (installed old_installed_model produced)
open GeneralWherePhysicalOldModel319 (m)
open GeneralWherePhysicalPast319 (point loose loose_slots point_slots)
open GeneralWherePhysicalPointLift319 (revisionFor certificate improves)
open GeneralDictionaryJournalRefinement228Source (roles root snapshot)
open GeneralWhereVersionInstall317 (Journal Models)
open GeneralNominalCommonBridge (Assignment)
open GeneralWhereOriginSingleCells318 (hi loOld oldChild)
open GeneralDictionaryBinderLocations (sourceSlot)
open GeneralWherePhysicalPast319 (savedHi firstLo)
open GeneralNominalVersionedEffects231 (ClassEffects)

abbrev revision := revisionFor installed.mixed.core.erased.current rfl
abbrev updated : Journal roles :=
  ⟨GeneralNominalVersionedRefresh232.reobserve installed.mixed revision,installed.versionedWhere⟩

theorem old_raw : installed.mixed.core.erased.current.context.state = loose := rfl
theorem revised_raw : updated.mixed.core.erased.current.context.state = point := rfl

theorem accepted_revision :
    GeneralNominalCenteredHeadMatStepRefresh.Reobserve installed.mixed.legacy revision :=
  certificate installed.mixed.legacy rfl rfl

theorem improves_revision : GeneralNominalReobservationSteps.Improves revision :=
  improves installed.mixed.core.erased.current rfl

/-- One genuine nominal observation step of the underlying mixed kernel,
lifted over the isolated corrected old record without unrecording it. -/
theorem underlying_step :
    GeneralNominalVersionedMixedKernel234.Step registry root installed.mixed updated.mixed :=
  GeneralNominalVersionedMixedKernel234.old_step ⟨root,.root,.administrative (.reobserve root _ accepted_revision improves_revision)⟩

theorem old_records : updated.versionedWhere = installed.versionedWhere := rfl
theorem old_edges : updated.mixed.core.erased.current.edges = installed.mixed.core.erased.current.edges := rfl
theorem old_sites : updated.mixed.core.sites = installed.mixed.core.sites := rfl

theorem requests (focus : GeneralSourceDictionaries.Occurrence roles) (out : GeneralSourceState.Output) :
    out ∈ GeneralNominalCenteredHeadOutputs.requests updated.mixed.core focus ↔
      out ∈ GeneralNominalCenteredHeadOutputs.requests installed.mixed.core focus :=
  GeneralNominalVersionedRefresh232.requests_iff_of_same_lists rfl rfl

theorem models_unchanged (n : Assignment) : Models updated n ↔ Models installed n := by
  constructor
  · intro valid
    refine ⟨(GeneralNominalVersionedRefresh232.reobserve_models accepted_revision n).mp valid.1,?_⟩
    intro p found
    have prior := valid.2 p found
    exact ⟨prior.1,(GeneralNominalVersionedFrameTransport232.class_effects_iff
      (fun out => requests p.packet.site.occurrence out)).mp prior.2⟩
  · intro valid
    refine ⟨(GeneralNominalVersionedRefresh232.reobserve_models accepted_revision n).mpr valid.1,?_⟩
    intro p found
    have prior := valid.2 p found
    exact ⟨prior.1,(GeneralNominalVersionedFrameTransport232.class_effects_iff
      (fun out => requests p.packet.site.occurrence out)).mpr prior.2⟩

theorem updated_model : Models updated m := (models_unchanged m).mpr old_installed_model

theorem exact_same_slots :
    sourceSlot installed.mixed.core.erased.current.context.state.base hi = some savedHi ∧
    sourceSlot updated.mixed.core.erased.current.context.state.base hi = some savedHi ∧
    sourceSlot updated.mixed.core.erased.current.context.state.base loOld = some firstLo :=
  ⟨loose_slots.2,point_slots.2,point_slots.1⟩

end Yulang.GeneralWherePhysicalReobserve319
