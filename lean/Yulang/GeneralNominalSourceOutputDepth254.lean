import Yulang.GeneralNominalProducerRank254
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalSourceOutputDepth254
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 GeneralNominalVersionedMixedKernel234
open GeneralNominalCenteredHeadMatPatternSemantics
open GeneralNominalCenteredHeadMatCompilerSemantics (algebra)
open GeneralNominalCenteredHeadMatSemanticLabels (Inputs)
open GeneralNominalPatersonLineage (mass)
open GeneralPatternAdditiveDepth253 (depth)
open GeneralNominalProducerOrder254 (ceiling)
open GeneralNominalInvocationAncestry (frontier)
open GeneralNominalOutputMenu254 (budget)
open CommonNominalFullCarrier (Equivalent)
variable {roles : Roles.RoleDecls} {state : State roles} {model : GeneralNominalCommonBridge.Assignment}

/-- The bound counts the remaining identities in a source-derived finite
frontier. It does not count refreshes or use the numeric size of source IDs. -/
def bound (registry : Registry) (context : GeneralNominalCandidates.Context)
 (root : Occurrence roles) (rootLabels : List Pattern) (identity : Nat) : Nat :=
 mass rootLabels + budget registry roles root *
   GeneralNominalProducerRank254.rank (GeneralNominalProducerRank254.pool registry context root rootLabels) identity

/-- All requested outputs of an existing evidence tree have closed semantic
representatives bounded by one source-derived additive budget. This retains
the Evidence premise and says nothing about raw intermediate snapshots. -/
theorem evidence_depth
 (source : GeneralNominalSourceFormation.InitialSource registry context root)
 (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
 (ground : GeneralNominalGroundAccessibility.GroundRoots context root rootLabels)
 (coverage : GeneralNominalCenteredHeadWFSource.Coverage registry context.interpretation)
 (path : B4Target.Steps (Step registry root) (initial context root) state)
 (valid : Models state model)
 (tree : Dictionary roles)
 (evidence : GeneralSourceDictionaries.Evidence (GeneralNominalVersionedEvidence231.Instance registry state.core model) tree) :
 ∀ output ∈ tree.root.demand.outputs, ∃ result : Pattern, result.variables = [] ∧
 Equivalent (model output.target).1
   (eval (algebra registry.constructors context.interpretation) (fun _ => .bottom) result) ∧
 depth result ≤ bound registry context root rootLabels tree.root.identity := by
 have interpretation : state.core.erased.current.context.interpretation = context.interpretation :=
   (GeneralNominalVersionedMixedAncestry237.configuration_trace path).2.2
 induction evidence with
 | @node occurrence key trees instanceRule allChildren ih =>
   obtain ⟨plan,certificate⟩ := instanceRule
   have current := certificate.frame
   obtain ⟨level,labels,_,known,inputBound⟩ :=
     GeneralNominalVersionedMixedAncestry237.sites_bounded source point ground coverage path model valid plan.input current.center_recorded
   have localInputs : Inputs (algebra plan.packet.registry.constructors plan.packet.context.interpretation) model plan.input labels := by
     simpa only [current.registry_eq,current.context_eq,interpretation] using known
   let pool := GeneralNominalProducerRank254.pool registry context root rootLabels
   let levelOf := GeneralNominalProducerRank254.rank pool
   let T := budget registry roles root
   let R := mass rootLabels
   let B := R + T * (levelOf occurrence.identity - 1)
   have childBounds : ∀ child ∈ GeneralNominalVersionedFrame231.children plan.packet,
     ∀ output ∈ child.demand.outputs, ∃ result : Pattern, result.variables = [] ∧
     Equivalent (model output.target).1
       (eval (algebra plan.packet.registry.constructors plan.packet.context.interpretation) (fun _ => .bottom) result) ∧
     depth result ≤ B := by
     intro child member output requested
     have recorded : child ∈ trees.map Dictionary.root := by rw [certificate.children_eq]; exact member
     obtain ⟨subtree,present,same⟩ := List.mem_map.mp recorded
     have childResults := ih subtree present
     rw [same] at childResults
     obtain ⟨result,closed,meaning,small⟩ := childResults output requested
     have edge : GeneralNominalProducerOrder254.Edge registry state.core child.identity occurrence.identity :=
       ⟨plan,occurrence,key,current,rfl,child,member,rfl⟩
     have strict := GeneralNominalProducerRank254.edge_rank source point ground coverage path valid edge
     have rank : levelOf child.identity ≤ levelOf occurrence.identity - 1 := by
       change levelOf child.identity < levelOf occurrence.identity at strict
       omega
     have budgetBound := Nat.mul_le_mul_left T rank
     refine ⟨result,closed,?_,?_⟩
     · simpa only [current.registry_eq,current.context_eq,interpretation] using meaning
     · change depth result ≤ R + T * levelOf child.identity at small
       change depth result ≤ R + T * (levelOf occurrence.identity - 1)
       omega
   have binders : GeneralNominalCapturedOutput254.BinderBound plan model B := by
     intro name member
     apply GeneralNominalBinderProducer254.binder_readback B ?_ name member
     intro clause present signature output requested
     exact childBounds _ (GeneralNominalEvidenceOutput254.clause_mem plan.packet clause present signature) output requested
   intro output requested
   obtain ⟨body,supplied,result,closed,meaning,small⟩ :=
     GeneralNominalCapturedOutput254.witness_readback current certificate.packet localInputs binders
       (certificate.outputs output requested)
   have templateBound := GeneralNominalOutputMenu254.body_bound path current requested supplied
   have parentMember := GeneralNominalProducerRank254.frame_member source point ground coverage path valid current
   have parentPositive := GeneralNominalProducerRank254.positive parentMember
   have rankEq : levelOf occurrence.identity = (levelOf occurrence.identity - 1) + 1 := by
     change 0 < levelOf occurrence.identity at parentPositive
     omega
   refine ⟨result,closed,?_,?_⟩
   · simpa only [current.registry_eq,current.context_eq,interpretation] using meaning
   · change depth result ≤ R + T * levelOf occurrence.identity
     rw [rankEq,Nat.mul_add,Nat.mul_one]
     change GeneralNominalCapturedOutput254.bodyDepth body ≤ T at templateBound
     change level + mass labels ≤ R at inputBound
     change depth result ≤ GeneralNominalCapturedOutput254.bodyDepth body + max (mass labels) (R + T * (levelOf occurrence.identity - 1)) at small
     omega

theorem payload_depth
 (source : GeneralNominalSourceFormation.InitialSource registry context root)
 (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
 (ground : GeneralNominalGroundAccessibility.GroundRoots context root rootLabels)
 (coverage : GeneralNominalCenteredHeadWFSource.Coverage registry context.interpretation)
 (path : B4Target.Steps (Step registry root) (initial context root) state)
 (valid : Models state model)
 (evidence : GeneralNominalVersionedEvidence231.Evidence registry state.core model focus payload) :
 ∀ output ∈ focus.demand.outputs, ∃ result : Pattern, result.variables = [] ∧
 Equivalent (model output.target).1
   (eval (algebra registry.constructors context.interpretation) (fun _ => .bottom) result) ∧
 depth result ≤ bound registry context root rootLabels focus.identity := by
 obtain ⟨tree,⟨rootEq,_⟩,proof⟩ := evidence
 have result := evidence_depth source point ground coverage path valid tree proof
 simpa only [rootEq] using result

/-- One natural depth bound works for all later states and all models, while
the representative itself may depend on the model. Only evidenced outputs
are covered; intermediate unevidenced equations are not. -/
theorem mixed_uniform
 (source : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Initial sourceRegistry root start) :
 ∃ D : Nat, ∀ (state : State roles),
 B4Target.Steps ((GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Step sourceRegistry root) start state →
 ∀ model, Models state model → ∀ focus payload,
 GeneralNominalVersionedEvidence231.Evidence
   (GeneralNominalCenteredHeadAllocEncoding.registry sourceRegistry) state.core model focus payload →
 ∀ output ∈ focus.demand.outputs, ∃ result : Pattern, result.variables = [] ∧
 Equivalent (model output.target).1
   (eval (algebra (GeneralNominalCenteredHeadAllocEncoding.registry sourceRegistry).constructors
     state.core.erased.current.context.interpretation) (fun _ => .bottom) result) ∧ depth result ≤ D := by
 have compiled := GeneralNominalVersionedMixedSourceBoundary234.initial_compiled source
 obtain ⟨legacy,⟨context,labels,formed,point,ground,coverage,rfl⟩,rfl⟩ := compiled
 let registry := GeneralNominalCenteredHeadAllocEncoding.registry sourceRegistry
 refine ⟨mass labels + budget registry roles root * (GeneralNominalProducerRank254.pool registry context root labels).length,?_⟩
 intro state path model valid focus payload evidence output requested
 obtain ⟨result,closed,meaning,small⟩ := payload_depth formed point ground coverage path valid evidence output requested
 have interpretation : state.core.erased.current.context.interpretation = context.interpretation :=
   (GeneralNominalVersionedMixedAncestry237.configuration_trace path).2.2
 refine ⟨result,closed,by simpa only [interpretation] using meaning,?_⟩
 exact Nat.le_trans small (Nat.add_le_add_left
   (Nat.mul_le_mul_left _ (GeneralNominalProducerRank254.length_bound _ _)) _)

theorem point_uniform
 (source : (GeneralNominalPointSourceBoundary240.boundary roles).Initial sourceRegistry root start) :
 ∃ D : Nat, ∀ (state : State roles),
 B4Target.Steps ((GeneralNominalPointSourceBoundary240.boundary roles).Step sourceRegistry root) start state →
 ∀ model, Models state model → ∀ focus payload,
 GeneralNominalVersionedEvidence231.Evidence
   (GeneralNominalCenteredHeadAllocEncoding.registry sourceRegistry) state.core model focus payload →
 ∀ output ∈ focus.demand.outputs, ∃ result : Pattern, result.variables = [] ∧
 Equivalent (model output.target).1
   (eval (algebra (GeneralNominalCenteredHeadAllocEncoding.registry sourceRegistry).constructors
     state.core.erased.current.context.interpretation) (fun _ => .bottom) result) ∧ depth result ≤ D := by
 obtain ⟨D,bounded⟩ := mixed_uniform source
 exact ⟨D,fun state path => bounded state (GeneralNominalPointErasure240.steps_old path)⟩

end Yulang.GeneralNominalSourceOutputDepth254

