import Yulang.GeneralNominalCenteredHeadAllocCompletion

/-! The twelve operational and order bridges for the repaired V6 boundary.
Production and dictionary evidence are deliberately separate fields. -/
namespace Yulang.GeneralNominalCenteredHeadAllocComposition
open GeneralDeclarations GeneralSourceDictionaries CommonRoleOutermostResolver
open GeneralNominalCenteredHeadMatStepJournal (State)
open GeneralNominalCenteredHeadAllocBoundary
open GeneralNominalCenteredHeadAllocExecutor (executor frontiers)
open GeneralNominalCenteredHeadAllocCompletion (GeneratedSelectedChildren)

structure TwelveLaws (roles : Roles.RoleDecls) : Prop where
  progress : ∀ value, (boundary roles).Checked value → ∀ state root,
    B4TargetV6.Reachable (boundary roles) value root state →
    Acc (fun next current => Step value root current next) state
  execution : ∀ value, (boundary roles).Checked value → ∀ state root,
    B4TargetV6.Reachable (boundary roles) value root state →
    B4Target.Steps (Step value root) state ((executor roles).run value state root).1
  halted : ∀ value, (boundary roles).Checked value → ∀ state root,
    B4TargetV6.Reachable (boundary roles) value root state →
    ∀ next, ¬ Step value root ((executor roles).run value state root).1 next
  closure : ∀ value, (boundary roles).Checked value → ∀ state root,
    B4TargetV6.Reachable (boundary roles) value root state →
    (∀ next, ¬ Step value root state next) →
    Stable value state root ∧ ∀ child, (boundary roles).Generated value state root child → Stable value state child
  stepModels : ∀ value, (boundary roles).Checked value → ∀ root before after,
    B4TargetV6.Reachable (boundary roles) value root before → Step value root before after →
    ∀ model, (boundary roles).Models after model → (boundary roles).Models before model
  frontierLocal : ∀ value, (boundary roles).Checked value → ∀ state root,
    B4TargetV6.Reachable (boundary roles) value root state → ∀ demand frontier,
    (frontiers roles value state).frontier demand = frontier ↔ Local value state demand frontier
  localIdentity : ∀ value (state : State roles) root,
    B4TargetV6.Reachable (boundary roles) value root state → (frontiers roles value state).Local = Local value state
  whereAccessible : ∀ value, (boundary roles).Checked value → ∀ state root,
    B4TargetV6.Reachable (boundary roles) value root state → Acc (Child (Local value state)) root
  treeExecution : ∀ value, (boundary roles).Checked value → ∀ state root,
    B4TargetV6.Reachable (boundary roles) value root state →
    ∀ (exact : FrontierExact (frontiers roles value ((executor roles).run value state root).1))
      (accessible : Acc (Child (frontiers roles value ((executor roles).run value state root).1).Local) root),
      ((executor roles).run value state root).2 =
        resolve (frontiers roles value ((executor roles).run value state root).1) exact root accessible
  canonicalLocalOrder : GeneralNominalCenteredHeadAllocExecutor.CanonicalLocalOrder roles
  dictionaryRefl : ∀ dictionary, (boundary roles).DictionaryEquivalent dictionary dictionary
  initialReorders : ∀ first last, (boundary roles).Reorders first last → ∀ root state,
    (boundary roles).Initial first root state → (boundary roles).Initial last root state

theorem twelveLaws (roles : Roles.RoleDecls) : TwelveLaws roles where
  progress := GeneralNominalCenteredHeadAllocExecutor.progress
  execution := GeneralNominalCenteredHeadAllocExecutor.execution
  halted := GeneralNominalCenteredHeadAllocExecutor.halted
  closure := GeneralNominalCenteredHeadAllocBoundary.closure
  stepModels := GeneralNominalCenteredHeadAllocBoundary.stepModels
  frontierLocal := fun _ checked state _ _ demand frontier =>
    GeneralNominalCenteredHeadAllocExecutor.frontierLocal checked state demand frontier
  localIdentity := fun value state _ _ => GeneralNominalCenteredHeadAllocExecutor.localIdentity value state
  whereAccessible := fun value _ state root _ => GeneralNominalCenteredHeadAllocBoundary.whereAccessible value state root
  treeExecution := fun value _ state root _ => GeneralNominalCenteredHeadAllocExecutor.treeExecution value state root
  canonicalLocalOrder := GeneralNominalCenteredHeadAllocExecutor.canonicalLocalOrder roles
  dictionaryRefl := GeneralNominalCenteredHeadAllocBoundary.dictionaryRefl
  initialReorders := fun _ _ order _ _ => GeneralNominalCenteredHeadAllocBoundary.initialReorders order

def EvidenceNode (roles : Roles.RoleDecls) : Prop :=
  B4SkeletonV5.EvidenceNode (B4TargetV6.prior (boundary roles))

structure WithProduction (roles : Roles.RoleDecls) : Prop extends TwelveLaws roles where
  generatedChildren : GeneratedSelectedChildren roles

theorem withProduction
    (baseline : GeneralNominalCenteredHeadAllocCompletion.HeadBaseline roles)
    (assembly : GeneralNominalCenteredHeadAllocCompletion.PacketAssembly roles)
    (choice : GeneralNominalCenteredHeadAllocCompletion.ChoiceFromCommon roles) : WithProduction roles where
  toTwelveLaws := twelveLaws roles
  generatedChildren := GeneralNominalCenteredHeadAllocCompletion.generatedSelectedChildren baseline assembly choice

end Yulang.GeneralNominalCenteredHeadAllocComposition
