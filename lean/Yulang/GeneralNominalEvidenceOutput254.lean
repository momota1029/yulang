import Yulang.GeneralNominalCapturedOutput254
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalEvidenceOutput254
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatPatternSemantics
open GeneralNominalCenteredHeadMatCompilerSemantics (algebra)
open GeneralNominalCenteredHeadMatSemanticLabels (Inputs)
open GeneralNominalVersionedFrame231 (clauseChild children)
open GeneralPatternAdditiveDepth253 (depth depths)
open CommonNominalFullCarrier (Equivalent)
variable {roles : Roles.RoleDecls} {model : GeneralNominalCommonBridge.Assignment}

def FiniteValue (semantics : Algebra) (model : GeneralNominalCommonBridge.Assignment) (target : Nat) : Prop :=
 ∃ result : Pattern, result.variables = [] ∧
 Equivalent (model target).1 (eval semantics (fun _ => .bottom) result)

def FiniteOutputs (semantics : Algebra) (model : GeneralNominalCommonBridge.Assignment) (root : Occurrence roles) : Prop :=
 ∀ output ∈ root.demand.outputs, FiniteValue semantics model output.target

theorem clause_mem (packet : GeneralNominalSaturationState.Packet roles) (clause : Clause)
 (member : clause ∈ packet.declaration.requirements) (signature : clause.Signature roles) :
 clauseChild packet clause signature ∈ children packet := by
 apply List.mem_map.mpr
 refine ⟨GeneralDeclarationDemands.emit packet.site.occurrence.identity packet.declaration clause signature
   (GeneralNominalVersionedFrame231.capture packet)
   ((GeneralNominalVersionedFrame231.frame packet).allocation packet.declaration.id clause),?_,rfl⟩
 apply (GeneralCanonicalChildOrder.canonicalEmit_perm packet.site.occurrence.identity packet.declaration
   packet.checked _ _).mem_iff.mp
 exact List.mem_map.mpr ⟨⟨clause,member⟩,List.mem_attach ..,rfl⟩

/-- A finite list of actual child-output witnesses supplies one common binder
bound. This is derived from child values, not postulated as a depth invariant. -/
theorem binder_bound (plan : Plan roles)
 (finite : ∀ child ∈ children plan.packet,
   FiniteOutputs (algebra plan.packet.registry.constructors plan.packet.context.interpretation) model child) :
 ∃ bound, GeneralNominalCapturedOutput254.BinderBound plan model bound := by
 classical
 have each (name : Nat) (member : name ∈ plan.packet.declaration.outputNames) :
   FiniteValue (algebra plan.packet.registry.constructors plan.packet.context.interpretation) model (plan.binder name) := by
   obtain ⟨clause,present,signature,request,requested,same⟩ := GeneralNominalBinderProducer254.binder_child name member
   simpa only [same] using finite _ (clause_mem plan.packet clause present signature) request requested
 let selected : Nat → Pattern := fun name => if member : name ∈ plan.packet.declaration.outputNames
   then Classical.choose (each name member) else .var name
 let pool := plan.packet.declaration.outputNames.map selected
 refine ⟨depths pool,?_⟩
 intro name member
 have facts : (selected name).variables = [] ∧
   Equivalent (model (plan.binder name)).1
   (eval (algebra plan.packet.registry.constructors plan.packet.context.interpretation) (fun _ => .bottom) (selected name)) := by
   simpa only [selected,dite_eq_left member] using Classical.choose_spec (each name member)
 exact ⟨selected name,facts.1,facts.2,
   GeneralPatternAdditiveDepth253.member_depth pool _ (List.mem_map.mpr ⟨name,member,rfl⟩)⟩

theorem local_outputs
 (certificate : GeneralNominalVersionedEvidence231.Certificate registry state model root key cs plan)
 (known : Inputs (algebra plan.packet.registry.constructors plan.packet.context.interpretation) model plan.input labels)
 (finite : ∀ child ∈ cs,
   FiniteOutputs (algebra registry.constructors state.erased.current.context.interpretation) model child) :
 FiniteOutputs (algebra registry.constructors state.erased.current.context.interpretation) model root := by
 have childrenFinite : ∀ child ∈ children plan.packet,
   FiniteOutputs (algebra plan.packet.registry.constructors plan.packet.context.interpretation) model child := by
   simpa only [certificate.children_eq,certificate.frame.registry_eq,certificate.frame.context_eq] using finite
 obtain ⟨bound,binders⟩ := binder_bound plan childrenFinite
 intro output member
 obtain ⟨body,_,result,closed,meaning,_⟩ := GeneralNominalCapturedOutput254.witness_readback
   certificate.frame certificate.packet known binders (certificate.outputs output member)
 exact ⟨result,closed,by simpa only [certificate.frame.registry_eq,certificate.frame.context_eq] using meaning⟩

/-- Existing indexed evidence is a finite proof tree. With real finite inputs
for every recorded candidate site, all requested outputs have finite ground
representatives in the same model. This does not produce evidence or prove
that a resolution run terminates. -/
theorem evidence_outputs
 (tree : Dictionary roles)
 (evidence : GeneralSourceDictionaries.Evidence (GeneralNominalVersionedEvidence231.Instance registry state model) tree)
 (inputs : ∀ (plan : Plan roles) root key,
   GeneralNominalVersionedEvidence231.Frame registry state root key plan →
   ∃ labels, Inputs (algebra plan.packet.registry.constructors plan.packet.context.interpretation) model plan.input labels) :
 FiniteOutputs (algebra registry.constructors state.erased.current.context.interpretation) model tree.root := by
 induction evidence with
 | @node occurrence key trees instanceRule allChildren ih =>
   obtain ⟨plan,certificate⟩ := instanceRule
   obtain ⟨labels,known⟩ := inputs plan occurrence key certificate.frame
   apply local_outputs certificate known
   intro child present
   obtain ⟨subtree,member,same⟩ := List.mem_map.mp present
   exact same ▸ ih subtree member

theorem payload_outputs
 (evidence : GeneralNominalVersionedEvidence231.Evidence registry state model root payload)
 (inputs : ∀ (plan : Plan roles) root key,
   GeneralNominalVersionedEvidence231.Frame registry state root key plan →
   ∃ labels, Inputs (algebra plan.packet.registry.constructors plan.packet.context.interpretation) model plan.input labels) :
 FiniteOutputs (algebra registry.constructors state.erased.current.context.interpretation) model root := by
 obtain ⟨tree,⟨rootEq,_⟩,proof⟩ := evidence
 have outputs := evidence_outputs tree proof inputs
 simpa only [rootEq] using outputs

end Yulang.GeneralNominalEvidenceOutput254
