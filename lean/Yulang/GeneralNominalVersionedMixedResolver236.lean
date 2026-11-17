import Yulang.GeneralNominalVersionedMixedWhere236
import Yulang.GeneralNominalVersionedMixedSourceFrontiers234
set_option backward.isDefEq.respectTransparency false
/-! A total, exact fixed-snapshot resolver for every actual source-reachable
state. This does not execute saturation or assert semantic dictionary soundness.
The frontier producer uses classical choice, so this is a proof-level resolver. -/
namespace Yulang.GeneralNominalVersionedMixedResolver236
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232
open GeneralNominalVersionedMixedSourceBoundary234 (Local boundary)
open GeneralNominalVersionedMixedSourceFrontiers234 (frontiers)
open CommonRoleOutermostResolver
variable {roles : Roles.RoleDecls} {registry : Registry} {state : State roles}

theorem frontier_exact (checked : (boundary roles).Checked registry) :
 FrontierExact (frontiers roles registry state) :=
 GeneralNominalVersionedMixedSourceFrontiers234.frontierLocal checked state

noncomputable def tree (checked : (boundary roles).Checked registry)
 (path : B4TargetV8.Reachable (boundary roles) registry root state) (demand : Occurrence roles) : Tree :=
 resolve (frontiers roles registry state) (frontier_exact checked) demand
   (GeneralNominalVersionedMixedWhere236.accessible path demand)

theorem tree_exact (checked : (boundary roles).Checked registry)
 (path : B4TargetV8.Reachable (boundary roles) registry root state) (demand : Occurrence roles) (result : Tree) :
 tree checked path demand = result ↔ Resolves (Local registry state) demand result :=
 resolve_tree_exact_of_frontier_exact _ _ _ _ _

theorem result_exact (checked : (boundary roles).Checked registry)
 (path : B4TargetV8.Reachable (boundary roles) registry root state) (demand : Occurrence roles) (result : Result) :
 classification (tree checked path demand) = result ↔ Classify (Local registry state) demand result :=
 resolve_exact_of_frontier_exact _ _ _ _ _

theorem proof_independent (checked : (boundary roles).Checked registry)
 (one : B4TargetV8.Reachable (boundary roles) registry root state)
 (two : B4TargetV8.Reachable (boundary roles) registry otherRoot state) (demand : Occurrence roles) :
 tree checked one demand = tree checked two demand :=
 (tree_exact checked two demand _).mpr ((tree_exact checked one demand _).mp rfl) |>.symm

theorem pending (checked : (boundary roles).Checked registry)
 (path : B4TargetV8.Reachable (boundary roles) registry root state)
 (selected : Local registry state demand .pending) : tree checked path demand = .pending :=
 (tree_exact checked path demand _).mpr (.pending selected)

theorem rejected (checked : (boundary roles).Checked registry)
 (path : B4TargetV8.Reachable (boundary roles) registry root state)
 (selected : Local registry state demand .rejected) : tree checked path demand = .rejected :=
 (tree_exact checked path demand _).mpr (.rejected selected)

theorem ambiguous (checked : (boundary roles).Checked registry)
 (path : B4TargetV8.Reachable (boundary roles) registry root state)
 (selected : Local registry state demand .ambiguous) : tree checked path demand = .ambiguous :=
 (tree_exact checked path demand _).mpr (.ambiguous selected)

end Yulang.GeneralNominalVersionedMixedResolver236
