import Yulang.GeneralDeclarativeStoppedLockstep341

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeStoppedDiagnostic341
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedSourceBoundary234 (Local)
open GeneralNominalSaturationState (Generated)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeStoppedLockstep341 (CurrentNodes Terminal)
open GeneralDeclarativeStoppedFold340 (live_children)
open CommonRoleOutermostResolver (All₂ Frontier Resolves Summarizes Tree Classify Dictionary Result)

def CurrentEdges (r : Registry) (s : State roles) (root : Occurrence roles) : Prop :=
  ∀ a, Generated s.core.erased.current root a → ∀ key children,
    Local r s a (.selected key children) →
    ∀ child ∈ children, Generated s.core.erased.current root child

theorem from_packets (t : Terminal r s root) : CurrentEdges r s root := by
  intro a live k kids selection
  obtain ⟨_,frame,fit⟩ := t.supports a live k kids selection
  exact live_children t.checked t.path selection frame fit live t.stopped

section
variable {roles : Roles.RoleDecls} {r : Registry} {s : State roles}
  {root : Occurrence roles} {names : Occurrence roles → Demand}
  {rule : Demand → Frontier Demand → Prop}
mutual
/-- Preserve the exact emitted diagnostic tree, not just the erased
dictionary. Only the positive subderivation of a successful report
needs its current source observations and generated edges. Neither
raw Evidence nor a feasible packet is required by this projection. -/
theorem exact_tree (edges : CurrentEdges r s root) (views : CurrentNodes r s root names rule)
    (atSite : Occurrence roles) (live : Generated s.core.erased.current root atSite)
    (tree : Tree) (dict : Dictionary)
    (literal : Resolves (Local r s) atSite tree) (result : Summarizes tree (.selected dict)) :
    Resolves rule (names atSite) tree := by
  cases literal with
  | pending _ => cases result
  | rejected _ => cases result
  | ambiguous _ => cases result
  | selected selection each =>
    cases result with
    | selected shown fitted =>
      cases fitted with
      | selected _ =>
        subst_vars
        exact .selected (views atSite live _ _ selection)
          (exact_forest edges views _ (edges atSite live _ _ selection) _ _ each shown)
termination_by sizeOf tree

theorem exact_forest (edges : CurrentEdges r s root) (views : CurrentNodes r s root names rule)
    (kids : List (Occurrence roles)) (live : ∀ a ∈ kids, Generated s.core.erased.current root a)
    (trees : List Tree) (dicts : List Dictionary)
    (literal : All₂ (Resolves (Local r s)) kids trees)
    (result : All₂ Summarizes trees (dicts.map Result.selected)) :
    All₂ (Resolves rule) (kids.map names) trees := by
  cases dicts with
  | nil => cases result; cases literal; exact .nil
  | cons head rest =>
    cases result with
    | cons first later =>
      cases literal with
      | cons one many =>
        exact .cons (exact_tree edges views _ (live _ List.mem_cons_self) _ head one first)
          (exact_forest edges views _ (fun _ h => live _ (List.mem_cons_of_mem _ h)) _ rest many later)
termination_by sizeOf trees
end

theorem replay_exact (edges : CurrentEdges r s root) (views : CurrentNodes r s root names rule)
    (raw : Resolves (Local r s) root tree) (summary : Summarizes tree (.selected dict)) :
    Resolves rule (names root) tree ∧ Classify rule (names root) (.selected dict) :=
  let positive := exact_tree edges views root .root tree dict raw summary
  ⟨positive,⟨tree,positive,summary⟩⟩

end
end Yulang.GeneralDeclarativeStoppedDiagnostic341
