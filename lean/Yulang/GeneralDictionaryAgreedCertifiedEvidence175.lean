import Yulang.GeneralDictionaryAgreedCompletion175
import Yulang.GeneralDictionaryAgreedTable175
import Yulang.GeneralDictionaryAgreedBounded174

/-! A checked finite-table role certificate connects actual finite refining
histories to full diagnostic exactness and dictionary soundness at their halted
endpoints. The history is not assumed to be selected by the ground executor.
The diagnostic still uses noncomputable frontiers. This is not a new language
fragment restriction or general B4 proof. -/
namespace Yulang.GeneralDictionaryAgreedCertifiedEvidence175
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralDictionaryRecursiveEvidence
open GeneralNominalActualAgreedLocal
open GeneralNominalActualAgreedBoundary (boundary frontiers)
open GeneralDictionaryReadback (Payload)
open CommonRoleOutermostResolver
open GeneralDictionaryAgreedRefiningTrace174
open GeneralDictionaryAgreedTable175
open GeneralDictionaryAgreedUniform174 (roleNodes)
open GeneralDictionaryAgreedBounded174 (runFuel)
variable {roles : Roles.RoleDecls} {defer : Bool} {gap : GapPredicate roles}
variable {registry : Registry} {state : Tracked roles} {root : Occurrence roles}

noncomputable def diagnostic (defer : Bool) (gap : GapPredicate roles)
    (registry : Registry) (state : Tracked roles) (root : Occurrence roles) : Tree :=
  runFuel (frontiers defer gap registry state) ((roleNodes registry).length + 1) root

theorem endpoint_reachable (context : GeneralNominalCandidates.Context)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    B4TargetV5.Reachable (boundary defer gap) registry root state :=
  GeneralNominalActualAgreedBoundary.reachable_iff_sourceFormed.mpr
    (trace_formed_recorded (.initial context source) (initial_recorded context) path).1

theorem diagnostic_resolves
    (checked : (boundary defer gap).Checked registry)
    (passed : certifyTable registry = true)
    (reachable : B4TargetV5.Reachable (boundary defer gap) registry root state) :
    Resolves (B4TargetV3.Local (boundary defer gap).toSourceBoundary registry state) root
      (diagnostic defer gap registry state root) := by
  apply GeneralDictionaryAgreedBounded174.certified_resolves
    (certifyTable_eq registry ▸ passed)
  intro demand frontier
  exact GeneralNominalActualAgreedBoundary.frontierLocal registry checked state root reachable demand frontier

theorem diagnostic_exact
    (checked : (boundary defer gap).Checked registry)
    (passed : certifyTable registry = true)
    (reachable : B4TargetV5.Reachable (boundary defer gap) registry root state)
    (tree : Tree) :
    diagnostic defer gap registry state root = tree ↔
      Resolves (B4TargetV3.Local (boundary defer gap).toSourceBoundary registry state) root tree := by
  have exact : FrontierExact (frontiers defer gap registry state) :=
    fun demand frontier => GeneralNominalActualAgreedBoundary.frontierLocal registry checked state root reachable demand frontier
  obtain ⟨rank,stratified⟩ := certifyTable_iff.mp passed
  have accessible := GeneralDictionaryAgreedEdge174.boundary_whereAccessible
    (defer := defer) (gap := gap) (state := state) stratified root
  have eq := (resolve_tree_exact_of_frontier_exact _ exact root accessible _).mpr
    (diagnostic_resolves checked passed reachable)
  rw [← eq]
  exact resolve_tree_exact_of_frontier_exact _ exact root accessible tree

theorem completed_iff
    (checked : (boundary defer gap).Checked registry)
    (passed : certifyTable registry = true)
    (reachable : B4TargetV5.Reachable (boundary defer gap) registry root state)
    (result : CommonRoleOutermostResolver.Result) :
    B4TargetV3.Completed (diagnostic defer gap registry state root) result ↔
      B4TargetV3.Classify (boundary defer gap).toSourceBoundary registry state root result := by
  constructor
  · intro completed
    exact B4TargetV3.tree_classifies _ _ _ _ _ _
      (diagnostic_resolves checked passed reachable) completed
  · intro derived
    obtain ⟨tree,resolved,completed⟩ := B4TargetV3.classify_tree derived
    rw [(diagnostic_exact checked passed reachable tree).mpr resolved]
    exact completed

/-- Recursive child Evidence is derived, not supplied. Halted is real actual
inability to step; the certificate checks real declaration role edges. -/
theorem halted_completed_evidence
    (checked : (boundary defer gap).Checked registry)
    (passed : certifyTable registry = true)
    (context : GeneralNominalCandidates.Context)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (halted : ∀ after, ¬ GeneralNominalActualInspectionSteps.Step registry root state after)
    (policy : ∀ demand, defer = true ∨ ¬ gap registry state demand)
    (dictionary : Payload)
    (completed : B4TargetV3.Completed (diagnostic defer gap registry state root) (.selected dictionary))
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    Evidence registry state.current.context model root dictionary :=
  GeneralDictionaryAgreedCompletion175.halted_dictionary_evidence checked context source path halted policy
    model valid dictionary ((completed_iff checked passed (endpoint_reachable context source path) _).mp completed)

end Yulang.GeneralDictionaryAgreedCertifiedEvidence175
