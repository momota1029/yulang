import Yulang.GeneralNominalVersionedResidualFrame237
set_option backward.isDefEq.respectTransparency false
/-! Installation support excludes all previous raw constraints and unused slots.
Their semantics is supplied by the already proved support of the old journal. -/
namespace Yulang.GeneralNominalVersionedResidualSupportSteps237
open GeneralNominalVersionedJournal232 GeneralNominalVersionedInstall232
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredFrame179 (Agree)
open GeneralNominalVersionedModelSupport237 (Support)
open GeneralNominalVersionedModelSupportSteps237 (liveSources legacy_live_iff new_live_iff)
open GeneralDictionaryDefault214ActualBodyFrame (classSources)
variable {roles : Roles.RoleDecls}

noncomputable def installSources (state : State roles) (effect : Effect roles) : List Nat :=
 GeneralNominalVersionedResidualFrame237.sources effect.plan ++
 classSources effect.snapshot effect.plan.packet.site.occurrence effect.plan ++
 classSources (installCore state.core effect.plan) effect.plan.packet.site.occurrence effect.plan ++
 liveSources state (installCore state.core effect.plan)

theorem installation_forward (state : State roles) (effect : Effect roles)
 (snapshot : effect.snapshot = state.core) (supported : Support state names)
 (same : Agree (names ++ installSources state effect) first last)
 (valid : InstallationModels state effect first) : InstallationModels state effect last := by
 have old : Models state last := (supported first last (fun n h => same n (by simp [h]))).mp valid.1
 have context := effect.frame.context_eq.trans (congrArg (fun core => core.erased.current.context) snapshot)
 have rawFirst : GeneralNominalState.Models effect.plan.packet.context.state first := by rw [context]; exact valid.1.1.1
 have rawLast : GeneralNominalState.Models effect.plan.packet.context.state last := by rw [context]; exact old.1.1
 have branch := (GeneralNominalVersionedResidualFrame237.holds_iff effect.plan rawFirst rawLast
   (fun n h => same n (by simp [installSources,h]))).mp valid.2.1
 have historic := (GeneralNominalVersionedJournalFrame236.class_iff effect.snapshot
   effect.plan.packet.site.occurrence effect.plan
   (fun n h => same n (by simp [installSources,h]))).mp valid.2.2.1.2
 have current := (GeneralNominalVersionedJournalFrame236.class_iff (installCore state.core effect.plan)
   effect.plan.packet.site.occurrence effect.plan
   (fun n h => same n (by simp [installSources,h]))).mp valid.2.2.2.1
 have live : Agree (liveSources state (installCore state.core effect.plan)) first last :=
   fun n h => same n (by simp [installSources,h])
 exact ⟨old,branch,⟨GeneralNominalVersionedPlans231.head_models branch,historic⟩,current,
   (legacy_live_iff state _ live).mp valid.2.2.2.2.1,(new_live_iff state _ live).mp valid.2.2.2.2.2⟩

theorem install (snapshot : effect.snapshot = state.core) (supported : Support state names) :
 Support (GeneralNominalVersionedInstall232.install state effect) (names ++ installSources state effect) := by
 intro first last same
 rw [install_models snapshot,install_models snapshot]
 exact ⟨installation_forward state effect snapshot supported same,
   installation_forward state effect snapshot supported (fun n h => (same n h).symm)⟩
end Yulang.GeneralNominalVersionedResidualSupportSteps237
