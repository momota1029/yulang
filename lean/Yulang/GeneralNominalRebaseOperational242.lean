import Yulang.GeneralNominalRebaseInstall242
import Yulang.GeneralNominalVersionedMixedTrace235
namespace Yulang.GeneralNominalRebaseOperational242
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalRebaseGenealogy242 GeneralNominalRebaseInstall242
open GeneralNominalCenteredHeadMatCompilerSemantics (algebra)
namespace Kernel
abbrev Step := @GeneralNominalVersionedMixedKernel234.Step
abbrev Models := @GeneralNominalVersionedJournal232.Models
end Kernel
variable {roles : Roles.RoleDecls} {before after : Journal.State roles}

theorem unchanged (same : after.core.sites = before.core.sites)
 (retained : ∀ model, Kernel.Models after model → Kernel.Models before model) :
 B4Target.Steps (Step registry seed semantics) (view before) (view after) := by
 have step := Step.rebase (registry := registry) (seed := seed) (semantics := semantics)
   (view before) (Kernel.Models after) (retained_extension before after retained)
 have eq : (⟨before.core.sites,Kernel.Models after⟩ : State roles) = view after := by
   unfold view
   rw [same]
 have first : B4Target.Steps (Step registry seed semantics) (view before) ⟨before.core.sites,Kernel.Models after⟩ :=
   B4Target.Steps.tail B4Target.Steps.refl step
 rw [eq] at first
 exact first

theorem step_trace
 (recorded : GeneralNominalVersionedMixedTrace235.Registered before root)
 (covered : GeneralNominalCenteredHeadWFSource.Coverage registry before.core.erased.current.context.interpretation)
 (seed_eq : before.core.erased.current.context.state.seed = seed)
 (interpretation_eq : before.core.erased.current.context.interpretation = interpretation)
 (action : Kernel.Step registry root before after) :
 B4Target.Steps (Step registry seed (algebra registry.constructors interpretation)) (view before) (view after) := by
 have retained := fun model valid => GeneralNominalVersionedMixedKernel234.step_models action (model := model) valid
 obtain ⟨focus,generated,action⟩ := action
 cases action with
 | administrative action =>
   cases action with
   | enqueue linked absent =>
     obtain ⟨site,member,same⟩ := GeneralNominalVersionedMixedTrace235.generated_registered recorded generated
     exact False.elim (absent site member same)
   | equate | refresh | reobserve => exact unchanged rfl retained
 | refresh | merge => exact unchanged rfl retained
 | install effect enabled novel =>
   have frame : GeneralNominalVersionedEvidence231.Frame registry before.core effect.plan.packet.site.occurrence
       effect.plan.packet.declaration.id effect.plan := enabled.registry_eq ▸ enabled.snapshot_eq ▸ effect.frame
   have declarationCovered : GeneralNominalCenteredHeadWFSource.DeclarationCovered effect.plan.packet.registry.constructors
       effect.plan.packet.context.interpretation effect.plan.packet.declaration := by
     rw [frame.registry_eq,frame.context_eq]
     exact covered.1 _ frame.visible
   have result := install_trace before effect enabled.snapshot_eq declarationCovered
   have seedPlan : effect.plan.packet.context.state.seed = seed := by rw [frame.context_eq,seed_eq]
   have interpretationPlan : effect.plan.packet.context.interpretation = interpretation := by rw [frame.context_eq,interpretation_eq]
   rw [enabled.registry_eq,seedPlan,frame.registry_eq,interpretationPlan] at result
   exact result

theorem trace (context : GeneralNominalCandidates.Context)
 (covered : GeneralNominalCenteredHeadWFSource.Coverage registry context.interpretation)
 (path : B4Target.Steps (Kernel.Step registry root) (GeneralNominalVersionedJournal232.initial context root) after) :
 B4Target.Steps (Step registry context.state.seed (algebra registry.constructors context.interpretation))
   (view (GeneralNominalVersionedJournal232.initial context root)) (view after) := by
 induction path with
 | refl => exact .refl
 | @tail before after path action ih =>
   have growth := GeneralNominalVersionedMixedGrowth234.steps path
   have ready := GeneralNominalVersionedMixedTrace235.steps (GeneralNominalVersionedMixedTrace235.initial context) path
   have coverage : GeneralNominalCenteredHeadWFSource.Coverage registry before.core.erased.current.context.interpretation := by
     rw [growth.interpretation]
     exact covered
   exact GeneralNominalRebaseBatch242.compose ih (step_trace ready.1 coverage growth.seed growth.interpretation action)
end Yulang.GeneralNominalRebaseOperational242
