import Yulang.GeneralNominalVersionedChildLabels237

/-! One actual versioned birth has finite labels and strict mass descent.
A rebase trace still needs model back-extension preserving live actual centers;
original-source preservation alone does not provide that premise. -/
namespace Yulang.GeneralNominalRebaseChildProduction241
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatSemanticLabels
open GeneralNominalCenteredHeadMatCompilerSemantics (algebra)
open GeneralNominalPatersonLineage (mass)
open GeneralNominalCommonBridge (Assignment)
variable {roles : Roles.RoleDecls} {plan : Plan roles} {model : Assignment}
variable {registry : Registry} {state : GeneralNominalCenteredSteps.State roles}
variable {focus : Occurrence roles} {key : Nat} {parentLabels : List Pattern}

theorem production
 (frame : GeneralNominalVersionedEvidence231.Frame registry state focus key plan)
 (nonempty : plan.packet.declaration.requirements ≠ [])
 (branch : GeneralNominalVersionedPlans231.Holds plan model)
 (known : Inputs (algebra plan.packet.registry.constructors plan.packet.context.interpretation) model plan.input parentLabels)
 (covered : GeneralNominalCenteredHeadWFSource.DeclarationCovered plan.packet.registry.constructors
   plan.packet.context.interpretation plan.packet.declaration) :
 ∃ capture : Nat → Pattern, Captures plan model capture ∧
   ∀ clause ∈ plan.packet.declaration.requirements, ∀ signature : clause.Signature roles,
   Inputs (algebra plan.packet.registry.constructors plan.packet.context.interpretation) model
     (GeneralNominalVersionedFrame231.childSite plan clause signature) (labels capture clause) ∧
   mass (labels capture clause) < mass parentLabels := by
 obtain ⟨capture,captures,bound⟩ := GeneralNominalVersionedHeadReadback237.readback frame nonempty branch known
 refine ⟨capture,captures,?_⟩
 intro clause member signature
 exact ⟨GeneralNominalVersionedChildLabels237.child_inputs branch captures member signature (covered.2.1 clause member).1,
   bounded_label_descent plan.packet.checked member capture bound⟩

theorem birth_bound
 (frame : GeneralNominalVersionedEvidence231.Frame registry state focus key plan)
 (nonempty : plan.packet.declaration.requirements ≠ [])
 (branch : GeneralNominalVersionedPlans231.Holds plan model)
 (known : Inputs (algebra plan.packet.registry.constructors plan.packet.context.interpretation) model plan.input parentLabels)
 (covered : GeneralNominalCenteredHeadWFSource.DeclarationCovered plan.packet.registry.constructors
   plan.packet.context.interpretation plan.packet.declaration)
 (depth budget : Nat) (bounded : depth + mass parentLabels ≤ budget) :
 ∃ capture : Nat → Pattern, Captures plan model capture ∧
   ∀ clause ∈ plan.packet.declaration.requirements, ∀ signature : clause.Signature roles,
   Inputs (algebra plan.packet.registry.constructors plan.packet.context.interpretation) model
     (GeneralNominalVersionedFrame231.childSite plan clause signature) (labels capture clause) ∧
   (depth+1) + mass (labels capture clause) ≤ budget := by
 obtain ⟨capture,captures,children⟩ := production frame nonempty branch known covered
 refine ⟨capture,captures,?_⟩
 intro clause member signature
 have child := children clause member signature
 exact ⟨child.1,by omega⟩

theorem empty_children (empty : plan.packet.declaration.requirements = []) :
 GeneralNominalVersionedFrame231.children plan.packet = [] := by
 apply List.eq_nil_iff_forall_not_mem.mpr
 intro child member
 have mapped : child.identity ∈ (GeneralNominalVersionedFrame231.children plan.packet).map Occurrence.identity := List.mem_map.mpr ⟨child,member,rfl⟩
 rw [GeneralNominalVersionedFrame231.children_identity_eq] at mapped
 obtain ⟨old,present,_⟩ := List.mem_map.mp mapped
 obtain ⟨clause,required,signature,_⟩ := GeneralNominalPatersonLineage.emitted_clause plan.packet old present
 rw [empty] at required
 cases required


theorem child_successor (visible : plan.packet.declaration ∈ plan.packet.registry.declarations)
 (clause : Clause) (member : clause ∈ plan.packet.declaration.requirements) (signature : clause.Signature roles) :
 (GeneralNominalVersionedFrame231.childSite plan clause signature).occurrence.identity ∈
 GeneralNominalInvocationAncestry.successors plan.packet.registry plan.packet.context.state.seed plan.input.occurrence.identity := by
 rw [plan.input_exact]
 change (GeneralNominalFeedbackSites.clauseChild plan.packet clause signature).identity ∈ _
 exact GeneralNominalInvocationAncestry.child_identity plan.packet _
   (GeneralNominalCenteredTrace.clauseChild_mem plan.packet clause member signature) visible

theorem child_ancestry (visible : plan.packet.declaration ∈ plan.packet.registry.declarations)
 (parent : GeneralNominalInvocationAncestry.AtDepth plan.packet.registry plan.packet.context.state.seed rootIdentity depth plan.input.occurrence.identity)
 (clause : Clause) (member : clause ∈ plan.packet.declaration.requirements) (signature : clause.Signature roles) :
 GeneralNominalInvocationAncestry.AtDepth plan.packet.registry plan.packet.context.state.seed rootIdentity (depth+1)
 (GeneralNominalVersionedFrame231.childSite plan clause signature).occurrence.identity :=
 .child parent (child_successor visible clause member signature)

end Yulang.GeneralNominalRebaseChildProduction241
