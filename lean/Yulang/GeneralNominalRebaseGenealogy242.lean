import Yulang.GeneralNominalRebaseBirth242
namespace Yulang.GeneralNominalRebaseGenealogy242
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalRebaseLiveLabels241
open GeneralNominalCenteredHeadMatCompilerSemantics (algebra)
open GeneralNominalCenteredHeadMatPatternSemantics (Algebra)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalPatersonLineage (mass)

structure State (roles : Roles.RoleDecls) where
 sites : List (Site roles)
 models : Assignment → Prop

inductive Step (registry : Registry) (seed : Nat) (semantics : Algebra) : State roles → State roles → Prop
 | rebase (before : State roles) (newModels : Assignment → Prop)
   (extension : BackExtension before.sites before.models newModels) :
   Step registry seed semantics before ⟨before.sites,newModels⟩
 | birth (before : State roles) (newModels : Assignment → Prop) (plan : Plan roles)
   (state : GeneralNominalCenteredSteps.State roles) (focus : Occurrence roles) (key : Nat)
   (frame : GeneralNominalVersionedEvidence231.Frame registry state focus key plan)
   (sameRegistry : plan.packet.registry = registry)
   (sameSeed : plan.packet.context.state.seed = seed)
   (sameAlgebra : algebra plan.packet.registry.constructors plan.packet.context.interpretation = semantics)
   (visible : plan.packet.declaration ∈ plan.packet.registry.declarations)
   (parent : plan.input ∈ before.sites)
   (branch : ∀ model, newModels model → GeneralNominalVersionedPlans231.Holds plan model)
   (covered : GeneralNominalCenteredHeadWFSource.DeclarationCovered plan.packet.registry.constructors
     plan.packet.context.interpretation plan.packet.declaration)
   (extension : BackExtension before.sites before.models newModels)
   (clause : Clause) (member : clause ∈ plan.packet.declaration.requirements) (signature : clause.Signature roles) :
   Step registry seed semantics before
     ⟨before.sites ++ [GeneralNominalVersionedFrame231.childSite plan clause signature],newModels⟩

def BoundedState (registry : Registry) (seed root budget : Nat) (semantics : Algebra) (state : State roles) : Prop :=
 ∀ model, state.models model → Bounded registry seed root budget semantics state.sites model

theorem step_bounded (step : Step registry seed semantics before after)
 (known : BoundedState registry seed root budget semantics before) :
 BoundedState registry seed root budget semantics after := by
 cases step with
 | rebase newModels extension => exact all_models extension known
 | birth newModels plan state focus key frame sameRegistry sameSeed sameAlgebra visible parent branch covered extension clause member signature =>
   have old : ∀ model, before.models model → Bounded plan.packet.registry plan.packet.context.state.seed root budget
       (algebra plan.packet.registry.constructors plan.packet.context.interpretation) before.sites model := by
     rw [sameAlgebra, sameRegistry, sameSeed]
     exact known
   have result := GeneralNominalRebaseBirth242.bounded_birth_models frame visible parent branch covered extension old clause member signature
   rw [sameAlgebra, sameRegistry, sameSeed] at result
   exact result

theorem trace_bounded (path : B4Target.Steps (Step registry seed semantics) before after)
 (known : BoundedState registry seed root budget semantics before) :
 BoundedState registry seed root budget semantics after := by
 induction path with
 | refl => exact known
 | tail path step ih => exact step_bounded step ih

theorem root_bounded
 (labels : List Pattern)
 (known : ∀ model, models model → GeneralNominalCenteredHeadMatSemanticLabels.Inputs semantics model site labels) :
 BoundedState registry seed site.occurrence.identity (mass labels) semantics ⟨[site],models⟩ := by
 intro model valid found member
 have eq := List.mem_singleton.mp member
 subst found
 exact ⟨0,labels,.root,known model valid,by omega⟩

theorem enumerated
 (path : B4Target.Steps (Step registry seed semantics) before after)
 (known : BoundedState registry seed root budget semantics before)
 (inhabited : ∃ model, after.models model) :
 ∀ site ∈ after.sites, site.occurrence.identity ∈ GeneralNominalInvocationAncestry.frontier registry seed root budget := by
 obtain ⟨model,valid⟩ := inhabited
 intro site member
 obtain ⟨depth,labels,ancestry,_,bound⟩ := trace_bounded path known model valid site member
 exact GeneralNominalInvocationAncestry.bounded_enumerated ancestry (by omega)

end Yulang.GeneralNominalRebaseGenealogy242
