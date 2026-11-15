import Yulang.GeneralNominalCenteredHeadAllocV7Executor
import Yulang.B4SkeletonV7

/-! The twelve operational and order bridges for the V7 boundary.
Production and dictionary evidence are deliberately separate fields. -/
namespace Yulang.GeneralNominalCenteredHeadAllocV7Composition
open GeneralDeclarations GeneralSourceDictionaries CommonRoleOutermostResolver
open GeneralNominalCenteredHeadMatStepJournal (State)
open GeneralNominalCenteredHeadAllocV7Boundary
open GeneralNominalCenteredHeadAllocV7Executor (executor frontiers)

structure TwelveLaws (roles : Roles.RoleDecls) : Prop where
  progress : ∀ value, (boundary roles).Checked value → ∀ state root,
    B4TargetV7.Reachable (boundary roles) value root state →
    Acc (fun next current => Step value root current next) state
  execution : ∀ value, (boundary roles).Checked value → ∀ state root,
    B4TargetV7.Reachable (boundary roles) value root state →
    B4Target.Steps (Step value root) state ((executor roles).run value state root).1
  halted : ∀ value, (boundary roles).Checked value → ∀ state root,
    B4TargetV7.Reachable (boundary roles) value root state →
    ∀ next, ¬ Step value root ((executor roles).run value state root).1 next
  closure : ∀ value, (boundary roles).Checked value → ∀ state root,
    B4TargetV7.Reachable (boundary roles) value root state →
    (∀ next, ¬ Step value root state next) →
    Stable value state root ∧ ∀ child, (boundary roles).Generated value state root child → Stable value state child
  stepModels : ∀ value, (boundary roles).Checked value → ∀ root before after,
    B4TargetV7.Reachable (boundary roles) value root before → Step value root before after →
    ∀ model, (boundary roles).Models after model → (boundary roles).Models before model
  frontierLocal : ∀ value, (boundary roles).Checked value → ∀ state root,
    B4TargetV7.Reachable (boundary roles) value root state → ∀ demand frontier,
    (frontiers roles value state).frontier demand = frontier ↔ Local value state demand frontier
  localIdentity : ∀ value (state : State roles) root,
    B4TargetV7.Reachable (boundary roles) value root state → (frontiers roles value state).Local = Local value state
  whereAccessible : ∀ value, (boundary roles).Checked value → ∀ state root,
    B4TargetV7.Reachable (boundary roles) value root state → Acc (Child (Local value state)) root
  treeExecution : ∀ value, (boundary roles).Checked value → ∀ state root,
    B4TargetV7.Reachable (boundary roles) value root state →
    ∀ (exact : FrontierExact (frontiers roles value ((executor roles).run value state root).1))
      (accessible : Acc (Child (frontiers roles value ((executor roles).run value state root).1).Local) root),
      ((executor roles).run value state root).2 =
        resolve (frontiers roles value ((executor roles).run value state root).1) exact root accessible
  canonicalLocalOrder : GeneralNominalCenteredHeadAllocV7Executor.CanonicalLocalOrder roles
  dictionaryRefl : ∀ dictionary, (boundary roles).DictionaryEquivalent dictionary dictionary
  initialReorders : ∀ first last, (boundary roles).Reorders first last → ∀ root state,
    (boundary roles).Initial first root state → (boundary roles).Initial last root state

theorem twelveLaws (roles : Roles.RoleDecls) : TwelveLaws roles where
  progress := GeneralNominalCenteredHeadAllocV7Executor.progress
  execution := GeneralNominalCenteredHeadAllocV7Executor.execution
  halted := GeneralNominalCenteredHeadAllocV7Executor.halted
  closure := GeneralNominalCenteredHeadAllocV7Boundary.closure
  stepModels := GeneralNominalCenteredHeadAllocV7Boundary.stepModels
  frontierLocal := fun _ checked state _ _ demand frontier =>
    GeneralNominalCenteredHeadAllocV7Executor.frontierLocal checked state demand frontier
  localIdentity := fun value state _ _ => GeneralNominalCenteredHeadAllocV7Executor.localIdentity value state
  whereAccessible := fun value _ state root _ => GeneralNominalCenteredHeadAllocV7Boundary.whereAccessible value state root
  treeExecution := fun value _ state root _ => GeneralNominalCenteredHeadAllocV7Executor.treeExecution value state root
  canonicalLocalOrder := GeneralNominalCenteredHeadAllocV7Executor.canonicalLocalOrder roles
  dictionaryRefl := GeneralNominalCenteredHeadAllocV7Boundary.dictionaryRefl
  initialReorders := fun _ _ order _ _ => GeneralNominalCenteredHeadAllocV7Boundary.initialReorders order

abbrev EvidenceNode (roles : Roles.RoleDecls) : Prop :=
  B4SkeletonV7.EvidenceNode (boundary roles)

abbrev GeneratedChildren (roles : Roles.RoleDecls) : Prop :=
  B4SkeletonV7.GeneratedChildren (boundary roles)

theorem bridges (laws : TwelveLaws roles) (node : EvidenceNode roles) (generated : GeneratedChildren roles) :
    B4SkeletonV7.B4Bridges (boundary roles) (executor roles) (frontiers roles) where
  progress := laws.progress
  execution := laws.execution
  halted := laws.halted
  closure := laws.closure
  stepModels := laws.stepModels
  frontierLocal := laws.frontierLocal
  localIdentity := laws.localIdentity
  whereAccessible := laws.whereAccessible
  treeExecution := laws.treeExecution
  canonicalLocalOrder := laws.canonicalLocalOrder
  dictionaryRefl := laws.dictionaryRefl
  evidenceNode := node
  generatedChildren := generated
  initialReorders := fun first last _ _ order state root initial => laws.initialReorders first last order root state initial

theorem composition (node : EvidenceNode roles) (generated : GeneratedChildren roles) :
    B4TargetV7.Statement (boundary roles) (executor roles) :=
  B4SkeletonV7.b4_of_bridges (boundary roles) (executor roles) (frontiers roles)
    (bridges (twelveLaws roles) node generated)

theorem dictionarySound (node : EvidenceNode roles) (generated : GeneratedChildren roles) :
    B4TargetV7.DictionarySound (boundary roles) (executor roles) :=
  (composition node generated).2.2.2.1

end Yulang.GeneralNominalCenteredHeadAllocV7Composition
