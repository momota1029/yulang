import Yulang.GeneralDictionaryAgreedGround174
import Yulang.GeneralDictionaryAgreedEdge174

/-! Full diagnostic exactness for the explicit role-DAG ground-source fragment.
The declaration rank is not a language rule and excludes same-role recursion.
No common model, readback producer, or where-accessibility premise is supplied.
No total completed classification is claimed: a finite diagnostic may contain
pending descendants. Registry-order independence remains a separate question. -/
namespace Yulang.GeneralDictionaryAgreedExact174
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalActualAgreedLocal
open GeneralDictionaryAgreedGround174 GeneralDictionaryAgreedEdge174
open CommonRoleOutermostResolver B4TargetV5
variable {roles : Roles.RoleDecls} {defer : Bool} {gap : GapPredicate roles}
variable {registry : Registry} {state : Tracked roles} {root : Occurrence roles}

noncomputable abbrev frontiers := @GeneralNominalActualAgreedBoundary.frontiers

theorem final_reachable (checked : (boundary defer gap).Checked registry)
    (reachable : Reachable (boundary defer gap) registry root state) :
    Reachable (boundary defer gap) registry root ((executor defer gap).run registry state root).1 :=
  reachable_steps _ reachable (execution defer gap registry checked state root reachable)

theorem final_exact (checked : (boundary defer gap).Checked registry)
    (reachable : Reachable (boundary defer gap) registry root state) :
    FrontierExact (frontiers defer gap registry ((executor defer gap).run registry state root).1) := by
  intro demand frontier
  exact GeneralNominalActualAgreedBoundary.frontierLocal registry checked _ root
    (reachable_agreed (final_reachable checked reachable)) demand frontier

theorem run_resolves_iff (checked : (boundary defer gap).Checked registry)
    (stratified : RoleStratified registry rank)
    (reachable : Reachable (boundary defer gap) registry root state) (tree : Tree) :
    ((executor defer gap).run registry state root).2 = tree ↔
      Resolves (B4TargetV3.Local (boundary defer gap).toSourceBoundary registry
        ((executor defer gap).run registry state root).1) root tree := by
  have exact := final_exact checked reachable
  have accessible := boundary_whereAccessible (defer := defer) (gap := gap)
    (state := ((executor defer gap).run registry state root).1) stratified root
  rw [treeExecution defer gap registry checked state root reachable exact accessible]
  exact resolve_tree_exact_of_frontier_exact _ exact root accessible tree

theorem completed_iff (checked : (boundary defer gap).Checked registry)
    (stratified : RoleStratified registry rank)
    (reachable : Reachable (boundary defer gap) registry root state) (out : Result) :
    B4TargetV3.Completed ((executor defer gap).run registry state root).2 out ↔
      B4TargetV3.Classify (boundary defer gap).toSourceBoundary registry
        ((executor defer gap).run registry state root).1 root out := by
  constructor
  · intro done
    exact B4TargetV3.tree_classifies (boundary defer gap).toSourceBoundary registry
      ((executor defer gap).run registry state root).1 _ root out
      ((run_resolves_iff checked stratified reachable _).mp rfl) done
  · intro derived
    obtain ⟨tree,resolved,done⟩ := B4TargetV3.classify_tree derived
    rw [(run_resolves_iff checked stratified reachable tree).mpr resolved]
    exact done

theorem initial_run_resolves_iff (checked : (boundary defer gap).Checked registry)
    (stratified : RoleStratified registry rank)
    (initial : (boundary defer gap).Initial registry root state) (tree : Tree) :
    ((executor defer gap).run registry state root).2 = tree ↔
      Resolves (B4TargetV3.Local (boundary defer gap).toSourceBoundary registry
        ((executor defer gap).run registry state root).1) root tree :=
  run_resolves_iff checked stratified (reachable_initial _ initial) tree

end Yulang.GeneralDictionaryAgreedExact174
