import Yulang.GeneralNominalCenteredAdministrativeOrder
import Yulang.GeneralNominalCenteredAdministrativeProduction

/-! Eleven unconditional V5 fields for the administrative centered ground
boundary. Final observation confluence, evidence, and production are explicit
remaining obligations. The unrestricted centered transition is unchanged. -/
namespace Yulang.GeneralNominalCenteredAdministrativeComposition
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenteredSteps
open GeneralNominalCenteredBoundary (vocabulary)
open GeneralNominalCenteredAdministrativeLocal
open GeneralNominalCenteredGroundComposition (terminalState)
open B4TargetV5 CommonRoleOutermostResolver

variable {roles : Roles.RoleDecls}

theorem progress (registry : Registry) (checked : (boundary roles).Checked registry)
    (state : State roles) (root : Occurrence roles) (reachable : Reachable (boundary roles) registry root state) :
    Acc (fun next current => (boundary roles).Step registry root current next) state :=
  GeneralNominalCenteredGroundBoundary.progress registry checked state root reachable

theorem closure (registry : Registry) (checked : (boundary roles).Checked registry)
    (state : State roles) (root : Occurrence roles) (reachable : Reachable (boundary roles) registry root state)
    (halted : ∀ next, ¬ (boundary roles).Step registry root state next) :
    (boundary roles).Stable registry state root ∧
      ∀ child, (boundary roles).Generated registry state root child → (boundary roles).Stable registry state child :=
  GeneralNominalCenteredGroundBoundary.closure registry checked state root reachable halted

theorem stepModels (registry : Registry) (checked : (boundary roles).Checked registry)
    (root : Occurrence roles) (before after : State roles) (reachable : Reachable (boundary roles) registry root before)
    (step : (boundary roles).Step registry root before after) :
    ∀ model, (boundary roles).Models after model → (boundary roles).Models before model :=
  GeneralNominalCenteredGroundBoundary.stepModels registry checked root before after reachable step

theorem dictionaryRefl (dictionary : Dictionary) : (boundary roles).DictionaryEquivalent dictionary dictionary :=
  GeneralNominalCenteredGroundBoundary.dictionaryRefl (roles := roles) dictionary

theorem initialReorders (registry other : Registry) (checked : (boundary roles).Checked registry)
    (checkedOther : (boundary roles).Checked other) (order : (boundary roles).Reorders registry other)
    (state : State roles) (root : Occurrence roles) (given : (boundary roles).Initial registry root state) :
    (boundary roles).Initial other root state :=
  GeneralNominalCenteredGroundBoundary.initialReorders registry other checked checkedOther order state root given

noncomputable def diagnostic (registry : Registry) (state : State roles) (root : Occurrence roles) : Tree := by
  classical
  exact if exact : FrontierExact (frontiers roles registry state) then
    resolve (frontiers roles registry state) exact root
      (GeneralNominalCenteredAdministrativeWhere.boundary_where_accessible registry state root) else .pending

theorem diagnostic_exact (registry : Registry) (state : State roles) (root : Occurrence roles)
    (exact : FrontierExact (frontiers roles registry state))
    (accessible : Acc (Child (frontiers roles registry state).Local) root) :
    diagnostic registry state root = resolve (frontiers roles registry state) exact root accessible := by
  classical
  simp [diagnostic,exact]

noncomputable def executor (roles : Roles.RoleDecls) : B4TargetV3.Executor (vocabulary roles) where
  run registry state root := let final := terminalState registry state root; (final,diagnostic registry final root)

theorem execution (registry : Registry) (checked : (boundary roles).Checked registry)
    (state : State roles) (root : Occurrence roles) (reachable : Reachable (boundary roles) registry root state) :
    B4Target.Steps ((boundary roles).Step registry root) state ((executor roles).run registry state root).1 :=
  GeneralNominalCenteredGroundComposition.execution registry checked state root reachable

theorem halted (registry : Registry) (checked : (boundary roles).Checked registry)
    (state : State roles) (root : Occurrence roles) (reachable : Reachable (boundary roles) registry root state)
    (next : State roles) : ¬ (boundary roles).Step registry root ((executor roles).run registry state root).1 next :=
  GeneralNominalCenteredGroundComposition.halted registry checked state root reachable next

theorem treeExecution (registry : Registry) (_checked : (boundary roles).Checked registry)
    (state : State roles) (root : Occurrence roles) (_reachable : Reachable (boundary roles) registry root state)
    (exact : FrontierExact (frontiers roles registry ((executor roles).run registry state root).1))
    (accessible : Acc (Child (frontiers roles registry ((executor roles).run registry state root).1).Local) root) :
    ((executor roles).run registry state root).2 =
      resolve (frontiers roles registry ((executor roles).run registry state root).1) exact root accessible :=
  diagnostic_exact registry _ root exact accessible

/-- This compares just the primitive observations at a common registry. It
requires neither equality of journals nor equality of stored plans. -/
structure ObservationAgreement (registry : Registry) (first last : State roles) : Prop where
  pending : ∀ demand, (fields roles).RootPending registry first demand ↔ (fields roles).RootPending registry last demand
  root : ∀ demand, (fields roles).RootK2 registry first demand ↔ (fields roles).RootK2 registry last demand
  candidate : ∀ demand, (fields roles).CandidateK2 registry first demand ↔ (fields roles).CandidateK2 registry last demand
  inspection : ∀ demand, (fields roles).InspectionPending registry first demand ↔ (fields roles).InspectionPending registry last demand
  survivor : ∀ demand key children,
    (fields roles).Survivor registry first demand key children ↔ (fields roles).Survivor registry last demand key children

theorem observation_local (agreement : ObservationAgreement registry first last) (demand : Occurrence roles) (frontier) :
    Local registry first demand frontier ↔ Local registry last demand frontier :=
  GeneralLocalPredicateCongruence.local_iff (agreement.pending demand) (agreement.root demand)
    (agreement.candidate demand) (agreement.inspection demand) (agreement.survivor demand) frontier

/-- Only the two returned snapshots require a confluence hypothesis. -/
def FinalObservationAgreement (roles : Roles.RoleDecls) : Prop :=
  ∀ first last, (boundary roles).Checked first → (boundary roles).Checked last → (boundary roles).Reorders first last →
    ∀ state root, Reachable (boundary roles) first root state → Reachable (boundary roles) last root state →
    ObservationAgreement last (terminalState first state root) (terminalState last state root)

def CanonicalLocalOrder (roles : Roles.RoleDecls) : Prop :=
  ∀ first last, (boundary roles).Checked first → (boundary roles).Checked last → (boundary roles).Reorders first last →
    ∀ state root, Reachable (boundary roles) first root state → Reachable (boundary roles) last root state → ∀ demand frontier,
    B4TargetV3.Local (boundary roles).toSourceBoundary first ((executor roles).run first state root).1 demand frontier ↔
      B4TargetV3.Local (boundary roles).toSourceBoundary last ((executor roles).run last state root).1 demand frontier

/-- Exact residual after fixed-snapshot reordering: only final Local at the
common registry is compared. This imposes no intermediate-state confluence. -/
def FinalLocalAgreement (roles : Roles.RoleDecls) : Prop :=
  ∀ first last, (boundary roles).Checked first → (boundary roles).Checked last → (boundary roles).Reorders first last →
    ∀ state root, Reachable (boundary roles) first root state → Reachable (boundary roles) last root state → ∀ demand frontier,
    Local last (terminalState first state root) demand frontier ↔ Local last (terminalState last state root) demand frontier

theorem canonicalLocalOrder_iff_final_local_agreement : CanonicalLocalOrder roles ↔ FinalLocalAgreement roles := by
  constructor
  · intro canonical first last checked checkedLast order state root reached reachedLast demand frontier
    exact (GeneralNominalCenteredAdministrativeOrder.local_iff order checked.1 _ demand frontier).symm.trans
      ((local_correspondence first _ demand frontier).symm.trans
        ((canonical first last checked checkedLast order state root reached reachedLast demand frontier).trans
          (local_correspondence last _ demand frontier)))
  · intro agreement first last checked checkedLast order state root reached reachedLast demand frontier
    exact (local_correspondence first _ demand frontier).trans
      ((GeneralNominalCenteredAdministrativeOrder.local_iff order checked.1 _ demand frontier).trans
        ((agreement first last checked checkedLast order state root reached reachedLast demand frontier).trans
          (local_correspondence last _ demand frontier).symm))

theorem canonicalLocalOrder (agreement : FinalObservationAgreement roles) : CanonicalLocalOrder roles := by
  intro first last checked checkedLast order state root reached reachedLast demand frontier
  apply (local_correspondence first _ demand frontier).trans
  apply (GeneralNominalCenteredAdministrativeOrder.local_iff order checked.1 _ demand frontier).trans
  exact (observation_local (agreement first last checked checkedLast order state root reached reachedLast) demand frontier).trans
    (local_correspondence last _ demand frontier).symm

structure Remaining (roles : Roles.RoleDecls) : Prop where
  canonicalLocalOrder : CanonicalLocalOrder roles
  evidenceNode : B4SkeletonV5.EvidenceNode (boundary roles)
  generatedChildren : B4SkeletonV5.GeneratedChildren (boundary roles)

theorem bridges (remaining : Remaining roles) : B4SkeletonV5.B4Bridges (boundary roles) (executor roles) (frontiers roles) where
  progress := progress
  execution := execution
  halted := halted
  closure := closure
  stepModels := stepModels
  frontierLocal := frontierLocal
  localIdentity := localIdentity
  whereAccessible := GeneralNominalCenteredAdministrativeWhere.whereAccessible
  treeExecution := treeExecution
  canonicalLocalOrder := remaining.canonicalLocalOrder
  dictionaryRefl := dictionaryRefl
  evidenceNode := remaining.evidenceNode
  generatedChildren := remaining.generatedChildren
  initialReorders := initialReorders

theorem composition (remaining : Remaining roles) : B4TargetV5.Statement (boundary roles) (executor roles) :=
  B4SkeletonV5.b4_of_bridges _ _ _ (bridges remaining)

theorem composition_of_observations_and_production
    (agreement : FinalObservationAgreement roles)
    (evidence : B4SkeletonV5.EvidenceNode (GeneralNominalCenteredGroundBoundary.groundBoundary roles))
    (production : GeneralNominalCenteredAdministrativeProduction.ReachableProduction roles) :
    B4TargetV5.Statement (boundary roles) (executor roles) :=
  composition ⟨canonicalLocalOrder agreement,
    GeneralNominalCenteredAdministrativeProduction.evidenceNode_of_ground evidence,
    GeneralNominalCenteredAdministrativeProduction.generatedChildren production⟩

end Yulang.GeneralNominalCenteredAdministrativeComposition
