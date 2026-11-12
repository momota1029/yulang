import Yulang.GeneralNominalDownstreamExecutor
import Yulang.B4SkeletonV5

/-! Exact remaining V5 obligations on the concrete downstream-guarded boundary.
The six proved fields are not supplied by callers. Eight source obligations
remain: this is a conditional composition, not a general B4 implementation. -/
namespace Yulang.GeneralNominalDownstreamObligations
open CommonRoleOutermostResolver
open B4TargetV5
open B4TargetV3 (Executor Local)
open GeneralNominalDownstreamBoundary

variable (roles : Roles.RoleDecls)

/-- No rank/fuel/model evidence is inserted into the public target. These are
precisely the eight unfinished implementation/local obligations. -/
structure Remaining (e : Executor (GeneralNominalDownstreamBoundary.vocabulary roles)) : Prop where
  progress : ∀ r, (boundary roles).Checked r → ∀ s d, Reachable (boundary roles) r d s →
    Acc (fun next current => (boundary roles).Step r d current next) s
  execution : ∀ r, (boundary roles).Checked r → ∀ s d, Reachable (boundary roles) r d s →
    B4Target.Steps ((boundary roles).Step r d) s (e.run r s d).1
  halted : ∀ r, (boundary roles).Checked r → ∀ s d, Reachable (boundary roles) r d s →
    ∀ next, ¬ (boundary roles).Step r d (e.run r s d).1 next
  whereAccessible : ∀ r, (boundary roles).Checked r → ∀ s root, Reachable (boundary roles) r root s →
    Acc (Child (Local (boundary roles).toSourceBoundary r s)) root
  treeExecution : ∀ r (_checked : (boundary roles).Checked r) s d, Reachable (boundary roles) r d s →
    ∀ (exact : FrontierExact (frontiers roles r (e.run r s d).1))
    (accessible : Acc (Child (frontiers roles r (e.run r s d).1).Local) d),
    (e.run r s d).2 = resolve (frontiers roles r (e.run r s d).1) exact d accessible
  canonicalLocalOrder : ∀ r r', (boundary roles).Checked r → (boundary roles).Checked r' →
    (boundary roles).Reorders r r' → ∀ s root, Reachable (boundary roles) r root s →
    Reachable (boundary roles) r' root s → ∀ d f,
    Local (boundary roles).toSourceBoundary r (e.run r s root).1 d f ↔
      Local (boundary roles).toSourceBoundary r' (e.run r' s root).1 d f
  evidenceNode : B4SkeletonV5.EvidenceNode (boundary roles)
  generatedChildren : B4SkeletonV5.GeneratedChildren (boundary roles)

/-- The exact six concrete laws fill their named fields; callers supply only
the eight open obligations, rather than a disguised full bridge package. -/
theorem bridges_of_remaining (e : Executor (GeneralNominalDownstreamBoundary.vocabulary roles))
    (remaining : Remaining roles e) : B4SkeletonV5.B4Bridges (boundary roles) e (frontiers roles) where
  progress := remaining.progress
  execution := remaining.execution
  halted := remaining.halted
  closure := closure
  stepModels := stepModels
  frontierLocal := frontierLocal
  localIdentity := localIdentity
  whereAccessible := remaining.whereAccessible
  treeExecution := remaining.treeExecution
  canonicalLocalOrder := remaining.canonicalLocalOrder
  dictionaryRefl := dictionaryRefl
  evidenceNode := remaining.evidenceNode
  generatedChildren := remaining.generatedChildren
  initialReorders := initialReorders

theorem b4_of_remaining (e : Executor (GeneralNominalDownstreamBoundary.vocabulary roles))
    (remaining : Remaining roles e) : Statement (boundary roles) e :=
  B4SkeletonV5.b4_of_bridges (boundary roles) e (frontiers roles) (bridges_of_remaining roles e remaining)
end Yulang.GeneralNominalDownstreamObligations
