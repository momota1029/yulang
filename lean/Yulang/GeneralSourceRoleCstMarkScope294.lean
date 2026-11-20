import Yulang.GeneralSourceRoleCstMarkSpans294

/-! Classify scope by raw path prefixes, not by proximity of byte ranges.
Ancestors are intentionally not counted as unrelated outside marks. -/
namespace Yulang.GeneralSourceRoleCstMarkScope294
open GeneralSourceRoleCstTree293 (Tree Path Kind)
open GeneralSourceRoleCstMarks294 (marks marks_exact)
open GeneralSourceRoleCstPath293 (follow follow_append)
open GeneralSourceRoleCstRecovery293 (Plain TreePlain)

inductive Zone where
  | selected | ancestor | unrelated
  deriving DecidableEq, Repr

def classify (selected path : Path) : Zone :=
  if selected.isPrefixOf path then .selected
  else if path.isPrefixOf selected then .ancestor else .unrelated

theorem selected_exact (s p : Path) :
    classify s p = .selected ↔ ∃ tail, p = s ++ tail := by
  constructor
  · intro yes
    by_cases a : s.isPrefixOf p
    · obtain ⟨tail,e⟩ := List.isPrefixOf_iff_prefix.mp a
      exact ⟨tail,e.symm⟩
    · by_cases b : p.isPrefixOf s <;> simp [classify,a,b] at yes
  · rintro ⟨tail,e⟩
    have a := List.isPrefixOf_iff_prefix.mpr (show s <+: p from ⟨tail,e.symm⟩)
    simp [classify,a]

theorem ancestor_exact (s p : Path) :
    classify s p = .ancestor ↔ (¬ s <+: p) ∧ p <+: s := by
  unfold classify
  by_cases a : s.isPrefixOf p <;> by_cases b : p.isPrefixOf s <;>
    simp [a,b,← List.isPrefixOf_iff_prefix]

theorem unrelated_exact (s p : Path) :
    classify s p = .unrelated ↔ (¬ s <+: p) ∧ ¬ p <+: s := by
  unfold classify
  by_cases a : s.isPrefixOf p <;> by_cases b : p.isPrefixOf s <;>
    simp [a,b,← List.isPrefixOf_iff_prefix]

theorem below_exact {r selected : Tree} {s : Path} (picked : follow s r = some selected)
    (tail : Path) (k : Kind) :
    (s ++ tail,k) ∈ marks r ↔ (tail,k) ∈ marks selected := by
  rw [marks_exact,marks_exact,follow_append,picked]
  rfl

theorem selected_plain_iff {r selected : Tree} {s : Path} (picked : follow s r = some selected) :
    TreePlain selected ↔ ∀ p k, (p,k) ∈ marks r → classify s p ≠ .selected := by
  constructor
  · intro valid p k found classified
    obtain ⟨tail,rfl⟩ := (selected_exact ..).mp classified
    obtain ⟨t,read,tag,bad⟩ := (marks_exact ..).mp ((below_exact picked ..).mp found)
    exact bad (tag ▸ valid tail t read)
  · intro H p t found
    by_cases plain : Plain t.kind
    · exact plain
    · exact False.elim (H (s++p) t.kind ((below_exact picked ..).mpr
        ((marks_exact ..).mpr ⟨t,found,rfl,plain⟩)) ((selected_exact ..).mpr ⟨p,rfl⟩))

end Yulang.GeneralSourceRoleCstMarkScope294
