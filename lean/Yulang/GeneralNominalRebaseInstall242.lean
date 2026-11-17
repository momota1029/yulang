import Yulang.GeneralNominalRebaseBatch242
import Yulang.GeneralNominalVersionedInstall232
namespace Yulang.GeneralNominalRebaseInstall242
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalRebaseGenealogy242 GeneralNominalRebaseLiveLabels241
open GeneralNominalCenteredHeadMatCompilerSemantics (algebra)
open GeneralNominalCommonBridge (Assignment)
namespace Journal
abbrev State := GeneralNominalVersionedJournal232.State
abbrev Models := @GeneralNominalVersionedJournal232.Models
abbrev Effect := GeneralNominalVersionedJournal232.Effect
end Journal

def view (state : Journal.State roles) : State roles := ⟨state.core.sites,Journal.Models state⟩

theorem retained_extension (before after : Journal.State roles)
 (retained : ∀ model, Journal.Models after model → Journal.Models before model) :
 BackExtension before.core.sites (Journal.Models before) (Journal.Models after) := by
 intro model valid
 exact ⟨model,retained model valid,fun _ _ _ => ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩⟩

theorem install_trace (state : Journal.State roles) (effect : Journal.Effect roles)
 (snapshot : effect.snapshot = state.core)
 (covered : GeneralNominalCenteredHeadWFSource.DeclarationCovered effect.plan.packet.registry.constructors
   effect.plan.packet.context.interpretation effect.plan.packet.declaration) :
 B4Target.Steps (Step effect.registry effect.plan.packet.context.state.seed
   (algebra effect.plan.packet.registry.constructors effect.plan.packet.context.interpretation))
   (view state) (view (GeneralNominalVersionedInstall232.install state effect)) := by
 have frame : GeneralNominalVersionedEvidence231.Frame effect.registry state.core effect.plan.packet.site.occurrence
     effect.plan.packet.declaration.id effect.plan := snapshot ▸ effect.frame
 exact GeneralNominalRebaseBatch242.emitted_steps (view state)
   (Journal.Models (GeneralNominalVersionedInstall232.install state effect)) effect.plan frame frame.registry_eq rfl rfl
   (frame.registry_eq ▸ frame.visible) frame.center_recorded
   (fun model valid => ((GeneralNominalVersionedInstall232.install_models snapshot).mp valid).2.1)
   covered (retained_extension _ _ (fun _ valid => GeneralNominalVersionedInstall232.step_models snapshot valid))
end Yulang.GeneralNominalRebaseInstall242
