import Yulang.GeneralNominalRebaseGenealogy242
import Yulang.GeneralNominalVersionedChildren232
namespace Yulang.GeneralNominalRebaseBatch242
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalRebaseGenealogy242 GeneralNominalRebaseLiveLabels241
open GeneralNominalCenteredHeadMatCompilerSemantics (algebra)
open GeneralNominalCommonBridge (Assignment)
variable {roles : Roles.RoleDecls}

theorem compose (one : B4Target.Steps relation first middle) (two : B4Target.Steps relation middle last) :
 B4Target.Steps relation first last := by
 induction two with
 | refl => exact one
 | tail path step ih => exact .tail ih step

theorem self_extension (sites : List (Site roles)) (models : Assignment → Prop) : BackExtension sites models models := by
 intro model valid
 exact ⟨model,valid,fun _ _ _ => ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩⟩

theorem append_children (plan : Plan roles)
 (frame : GeneralNominalVersionedEvidence231.Frame registry state focus key plan)
 (sameRegistry : plan.packet.registry = registry)
 (sameSeed : plan.packet.context.state.seed = seed)
 (sameAlgebra : algebra plan.packet.registry.constructors plan.packet.context.interpretation = semantics)
 (visible : plan.packet.declaration ∈ plan.packet.registry.declarations)
 (branch : ∀ model, models model → GeneralNominalVersionedPlans231.Holds plan model)
 (covered : GeneralNominalCenteredHeadWFSource.DeclarationCovered plan.packet.registry.constructors
   plan.packet.context.interpretation plan.packet.declaration)
 (added : List (Site roles))
 (produced : ∀ child ∈ added, ∃ clause, ∃ _member : clause ∈ plan.packet.declaration.requirements,
   ∃ signature : clause.Signature roles, child = GeneralNominalVersionedFrame231.childSite plan clause signature)
 (parent : plan.input ∈ sites) :
 B4Target.Steps (Step registry seed semantics) (⟨sites,models⟩ : State roles) ⟨sites ++ added,models⟩ := by
 induction added generalizing sites with
 | nil => simpa only [List.append_nil] using (B4Target.Steps.refl (s := (⟨sites,models⟩ : State roles)))
 | cons head tail ih =>
   obtain ⟨clause,member,signature,equal⟩ := produced head (List.mem_cons_self ..)
   subst head
   have step := Step.birth (⟨sites,models⟩ : State roles) models plan state focus key frame sameRegistry sameSeed sameAlgebra
     visible parent branch covered (self_extension sites models) clause member signature
   have first := B4Target.Steps.tail B4Target.Steps.refl step
   have rest := ih (sites := sites ++ [GeneralNominalVersionedFrame231.childSite plan clause signature]) (fun child member => produced child (List.mem_cons_of_mem _ member))
     (List.mem_append_left _ parent)
   simpa only [List.append_assoc,List.singleton_append] using compose first rest

theorem emitted_steps (before : State roles) (newModels : Assignment → Prop) (plan : Plan roles)
 (frame : GeneralNominalVersionedEvidence231.Frame registry state focus key plan)
 (sameRegistry : plan.packet.registry = registry)
 (sameSeed : plan.packet.context.state.seed = seed)
 (sameAlgebra : algebra plan.packet.registry.constructors plan.packet.context.interpretation = semantics)
 (visible : plan.packet.declaration ∈ plan.packet.registry.declarations)
 (parent : plan.input ∈ before.sites)
 (branch : ∀ model, newModels model → GeneralNominalVersionedPlans231.Holds plan model)
 (covered : GeneralNominalCenteredHeadWFSource.DeclarationCovered plan.packet.registry.constructors
   plan.packet.context.interpretation plan.packet.declaration)
 (extension : BackExtension before.sites before.models newModels) :
 B4Target.Steps (Step registry seed semantics) before
   ⟨before.sites ++ GeneralNominalVersionedChildren232.emitted plan,newModels⟩ := by
 have first : B4Target.Steps (Step registry seed semantics) before ⟨before.sites,newModels⟩ :=
   B4Target.Steps.tail B4Target.Steps.refl (Step.rebase before newModels extension)
 apply compose first
 apply append_children plan frame sameRegistry sameSeed sameAlgebra visible branch covered _ ?_ parent
 intro child member
 obtain ⟨clause,_,rfl⟩ := List.mem_map.mp member
 exact ⟨clause.val,(GeneralCanonicalChildOrder.canonicalRequirements_perm _).mem_iff.mpr clause.property,_,rfl⟩
end Yulang.GeneralNominalRebaseBatch242
