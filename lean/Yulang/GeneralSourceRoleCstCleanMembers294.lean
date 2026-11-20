import Yulang.GeneralSourceRoleCstRunControls294

/-! The narrow role producer cannot silently hide a recovery mark in one of
its admitted declaration shapes or in discarded trivia. -/
namespace Yulang.GeneralSourceRoleCstCleanMembers294
open GeneralSourceRoleCstTree293 (Tree Kind trivia)
open GeneralSourceRoleCstShapes293 (cleanTree cleanList visible)
open GeneralSourceRoleCstRecovery293 (Plain clean_list_exact clean_tree_exact)
open GeneralSourceRoleCstTypeRules293 (IsRhs IsType type_exact)
open GeneralSourceRoleCstBody293 (Classification IsStatement)
open GeneralSourceRoleCstTrivia293 (visible_filter)

theorem each_clean (xs : List Tree) :
    cleanList xs = true ↔ ∀ t ∈ xs, cleanTree t = true := by
  rw [clean_list_exact]
  constructor
  · intro h t mem
    obtain ⟨i,bound,e⟩ := List.getElem_of_mem mem
    exact (clean_tree_exact t).mpr (h i t (List.getElem?_eq_some_iff.mpr ⟨bound,e⟩))
  · intro h i t got
    exact (clean_tree_exact t).mp (h t (List.mem_of_getElem? got))

theorem trivia_clean {t : Tree} (isTrivia : trivia t = true) : cleanTree t = true := by
  cases t with
  | node => cases isTrivia
  | token k t => cases k <;> simp_all [trivia,cleanTree]

theorem clean_full_from_visible (cs : List Tree) (h : cleanList (visible cs) = true) :
    cleanList cs = true := by
  apply (each_clean cs).mpr
  intro t inFull
  by_cases discard : trivia t = true
  · exact trivia_clean discard
  · apply (each_clean _).mp h t
    rw [visible_filter,List.mem_filter]
    exact ⟨inFull,by simp [discard]⟩

theorem node_if_clean (k : Kind) (cs : List Tree) (valid : Plain k)
    (h : cleanList (visible cs) = true) : cleanTree (.node k cs) = true := by
  change (decide (Plain k) && cleanList cs) = true
  simp [valid,clean_full_from_visible cs h]

theorem rhs_clean {t : Tree} {v : GeneralSourceRoleSyntaxBoundary292.Rhs}
    (allowed : IsRhs t v) : cleanTree t = true := by
  cases allowed with
  | binder cs name shown =>
    apply node_if_clean .head cs (by decide)
    rw [shown]
    rfl
  | named cs name shown =>
    apply node_if_clean .head cs (by decide)
    rw [shown]
    rfl

theorem declaration_clean {t : Tree} {s : GeneralSourceRoleSyntaxBoundary292.Shape}
    (allowed : IsType t s) : cleanTree t = true := by
  cases allowed with
  | required cs word name shown =>
    apply node_if_clean .typeDecl cs (by decide)
    rw [shown]
    rfl
  | defaulted cs word name equals body rhs shown inner =>
    apply node_if_clean .typeDecl cs (by decide)
    rw [shown]
    have h := rhs_clean inner
    change (true && (true && (true && (cleanTree body && true)))) = true
    simp [h]

theorem class_clean {t : Tree} {child : GeneralSourceRoleChildCoverage292.Child}
    (h : Classification t child) : cleanTree t = true := by
  cases h with
  | associated cs s allowed => exact declaration_clean ((type_exact ..).mp allowed)
  | binding cs all =>
    change (true && cleanList cs) = true
    simp [all]

theorem statement_clean {site : List Nat} {t : Tree}
    {out : List Nat × GeneralSourceRoleChildCoverage292.Child}
    (allowed : IsStatement site t out) : cleanTree t = true := by
  obtain ⟨cs,i,inner,rfl,shell,path,prepared⟩ := allowed
  apply node_if_clean .statement cs (by decide)
  rw [visible,shell]
  have valid := class_clean prepared
  change (cleanTree inner && true) = true
  simp [valid]

end Yulang.GeneralSourceRoleCstCleanMembers294
