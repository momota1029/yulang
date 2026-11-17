import Yulang.GeneralNominalVersionedModelSupport237
set_option backward.isDefEq.respectTransparency false
/-! Only newly added semantic obligations enlarge trace support. -/
namespace Yulang.GeneralNominalVersionedModelSupportSteps237
open GeneralNominalVersionedJournal232
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredFrame179 (Agree)
open GeneralNominalVersionedModelSupport237 (Support)
open GeneralDictionaryDefault214ActualBodyFrame (classSources)
variable {roles : Roles.RoleDecls} {first last : Assignment}

noncomputable def liveSources (state : State roles) (core : GeneralNominalCenteredSteps.State roles) : List Nat :=
 state.legacy.effects.flatMap (fun effect => classSources core effect.plan.packet.site.occurrence effect.plan) ++
 state.effects.flatMap (fun effect => classSources core effect.plan.packet.site.occurrence effect.plan)

theorem legacy_live_iff (state : State roles) (core : GeneralNominalCenteredSteps.State roles)
 (same : Agree (liveSources state core) first last) :
 (∀ effect ∈ state.legacy.effects, effect.Live core first) ↔
 (∀ effect ∈ state.legacy.effects, effect.Live core last) := by
 apply forall_congr'; intro effect
 apply forall_congr'; intro member
 apply GeneralDictionaryDefault214ActualBodyFrame.class_iff
 intro name present
 exact same name (List.mem_append_left _ (List.mem_flatMap.mpr ⟨effect,member,present⟩))

theorem new_live_iff (state : State roles) (core : GeneralNominalCenteredSteps.State roles)
 (same : Agree (liveSources state core) first last) :
 (∀ effect ∈ state.effects, effect.Live core first) ↔
 (∀ effect ∈ state.effects, effect.Live core last) := by
 apply forall_congr'; intro effect
 apply forall_congr'; intro member
 apply GeneralNominalVersionedJournalFrame236.class_iff
 intro name present
 exact same name (List.mem_append_right _ (List.mem_flatMap.mpr ⟨effect,member,present⟩))

noncomputable def installSources (state : State roles) (effect : Effect roles) : List Nat :=
 GeneralNominalVersionedPacketFrame236.sources effect.plan ++
 GeneralNominalVersionedJournalFrame236.effectSources (GeneralNominalVersionedInstall232.install state effect) effect ++
 liveSources state (GeneralNominalVersionedInstall232.installCore state.core effect.plan)

theorem installation_iff (state : State roles) (effect : Effect roles)
 (supported : Support state names) (same : Agree (names ++ installSources state effect) first last) :
 GeneralNominalVersionedInstall232.InstallationModels state effect first ↔
 GeneralNominalVersionedInstall232.InstallationModels state effect last := by
 have old := supported first last (fun n h => same n (by simp [h]))
 have branch := GeneralNominalVersionedPacketFrame236.holds_iff (plan := effect.plan)
   (first := first) (last := last) (fun n h => same n (by simp [installSources,h]))
 have current := GeneralNominalVersionedJournalFrame236.effect_iff
   (GeneralNominalVersionedInstall232.install state effect) effect
   (first := first) (last := last) (fun n h => same n (by simp [installSources,h]))
 have live : Agree (liveSources state (GeneralNominalVersionedInstall232.installCore state.core effect.plan)) first last :=
   fun n h => same n (by simp [installSources,h])
 have legacy := legacy_live_iff state _ live
 have prior := new_live_iff state _ live
 change (Models state first ∧ _ ∧ _ ∧ _ ∧ _ ∧ _) ↔ _
 constructor
 · rintro ⟨a,b,c,d,e,f⟩
   exact ⟨old.mp a,branch.mp b,(current.mp ⟨c,d⟩).1,(current.mp ⟨c,d⟩).2,legacy.mp e,prior.mp f⟩
 · rintro ⟨a,b,c,d,e,f⟩
   exact ⟨old.mpr a,branch.mpr b,(current.mpr ⟨c,d⟩).1,(current.mpr ⟨c,d⟩).2,legacy.mpr e,prior.mpr f⟩

theorem install (snapshot : effect.snapshot = state.core) (supported : Support state names) :
 Support (GeneralNominalVersionedInstall232.install state effect) (names ++ installSources state effect) := by
 intro first last same
 rw [GeneralNominalVersionedInstall232.install_models snapshot,
   GeneralNominalVersionedInstall232.install_models snapshot]
 exact installation_iff state effect supported same

noncomputable def mergeSources (state : State roles) (one two : GeneralNominalCenters.Site roles) : List Nat :=
 (GeneralNominalDemandMerging.outputAtoms one.observed two.observed).flatMap GeneralNominalState.atomSources ++
 liveSources state (GeneralNominalVersionedAdministrative232.merge state one two).core

theorem atoms_iff (atoms : List (PresenceNormalForm.Atom Nat))
 (same : Agree (atoms.flatMap GeneralNominalState.atomSources) first last) :
 PresenceNormalForm.All CommonNominalFullCarrier.model first atoms ↔
 PresenceNormalForm.All CommonNominalFullCarrier.model last atoms := by
 apply forall_congr'; intro atom
 apply forall_congr'; intro member
 exact GeneralNominalCenteredModelExtension.atom_same atom
   (fun n h => same n (List.mem_flatMap.mpr ⟨atom,member,h⟩))

theorem merge (state : State roles) (one two : GeneralNominalCenters.Site roles)
 (supported : Support state names) :
 Support (GeneralNominalVersionedAdministrative232.merge state one two) (names ++ mergeSources state one two) := by
 intro first last same
 rw [GeneralNominalVersionedAdministrative232.merge_models,GeneralNominalVersionedAdministrative232.merge_models]
 have old := supported first last (fun n h => same n (by simp [h]))
 have atoms := atoms_iff (GeneralNominalDemandMerging.outputAtoms one.observed two.observed)
   (first := first) (last := last) (fun n h => same n (by simp [mergeSources,h]))
 have live : Agree (liveSources state (GeneralNominalVersionedAdministrative232.merge state one two).core) first last :=
   fun n h => same n (by simp [mergeSources,h])
 exact and_congr old (and_congr atoms (and_congr (legacy_live_iff state _ live) (new_live_iff state _ live)))
end Yulang.GeneralNominalVersionedModelSupportSteps237
