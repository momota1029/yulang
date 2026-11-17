import Yulang.GeneralNominalRebaseLiveLabels241
namespace Yulang.GeneralNominalRebaseBirth242
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalRebaseLiveLabels241
open GeneralNominalCenteredHeadMatCompilerSemantics (algebra)
open GeneralNominalCommonBridge (Assignment)
variable {roles : Roles.RoleDecls} {plan : Plan roles}

theorem bounded_birth
 (frame : GeneralNominalVersionedEvidence231.Frame registry state focus key plan)
 (visible : plan.packet.declaration ∈ plan.packet.registry.declarations)
 (parent : plan.input ∈ sites)
 (branch : GeneralNominalVersionedPlans231.Holds plan model)
 (covered : GeneralNominalCenteredHeadWFSource.DeclarationCovered plan.packet.registry.constructors
   plan.packet.context.interpretation plan.packet.declaration)
 (known : Bounded plan.packet.registry plan.packet.context.state.seed root budget
   (algebra plan.packet.registry.constructors plan.packet.context.interpretation) sites model)
 (clause : Clause) (member : clause ∈ plan.packet.declaration.requirements) (signature : clause.Signature roles) :
 Bounded plan.packet.registry plan.packet.context.state.seed root budget
   (algebra plan.packet.registry.constructors plan.packet.context.interpretation)
   (sites ++ [GeneralNominalVersionedFrame231.childSite plan clause signature]) model := by
 obtain ⟨depth,labels,ancestry,inputs,bound⟩ := known plan.input parent
 have nonempty : plan.packet.declaration.requirements ≠ [] := by
   intro empty
   rw [empty] at member
   cases member
 obtain ⟨capture,_,children⟩ := GeneralNominalRebaseChildProduction241.birth_bound
   frame nonempty branch inputs covered depth budget bound
 intro site registered
 rcases List.mem_append.mp registered with old | child
 · exact known site old
 · have eq := List.mem_singleton.mp child
   subst site
   exact ⟨depth+1,_,GeneralNominalRebaseChildProduction241.child_ancestry visible ancestry clause member signature,
     (children clause member signature).1,(children clause member signature).2⟩

theorem bounded_birth_models
 (frame : GeneralNominalVersionedEvidence231.Frame registry state focus key plan)
 (visible : plan.packet.declaration ∈ plan.packet.registry.declarations)
 (parent : plan.input ∈ sites)
 (branch : ∀ model, newModels model → GeneralNominalVersionedPlans231.Holds plan model)
 (covered : GeneralNominalCenteredHeadWFSource.DeclarationCovered plan.packet.registry.constructors
   plan.packet.context.interpretation plan.packet.declaration)
 (extension : BackExtension sites oldModels newModels)
 (known : ∀ model, oldModels model → Bounded plan.packet.registry plan.packet.context.state.seed root budget
   (algebra plan.packet.registry.constructors plan.packet.context.interpretation) sites model)
 (clause : Clause) (member : clause ∈ plan.packet.declaration.requirements) (signature : clause.Signature roles) :
 ∀ model, newModels model → Bounded plan.packet.registry plan.packet.context.state.seed root budget
   (algebra plan.packet.registry.constructors plan.packet.context.interpretation)
   (sites ++ [GeneralNominalVersionedFrame231.childSite plan clause signature]) model := by
 intro model valid
 exact bounded_birth frame visible parent (branch model valid) covered
   (all_models extension known model valid) clause member signature
end Yulang.GeneralNominalRebaseBirth242
