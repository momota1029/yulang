import Yulang.CommonRoleDiagnosticDictionaries

/-! Failure-preserving diagnostic equivalence under visible-declaration reordering.
Only the order of the competing heads at an overlap node may differ. Selected
implementations, every child position and every goal remain unchanged. This is
not language-level method observational equivalence or final classification. -/
namespace Yulang.CommonRoleDiagnosticOrder
open Roles CommonRoleRecursiveDiagnostics CommonRoleDiagnosticDictionaries RoleDictionaries

/-- All diagnostic structure is retained. Child lists are compared by position,
so equal siblings remain separate occurrences. Overlap lists are permutations. -/
inductive Equivalent : Tree → Tree → Prop where
  | missing (g : Goal) : Equivalent (.missing g) (.missing g)
  | overlap (g : Goal) (heads other : List Impl) (permutation : heads.Perm other) :
      Equivalent (.overlap g heads) (.overlap g other)
  | selected (g : Goal) (i : Impl) (cs ds : List Tree)
      (length : cs.length = ds.length)
      (children : ∀ k (hc : k < cs.length) (hd : k < ds.length), Equivalent cs[k] ds[k]) :
      Equivalent (.selected g i cs) (.selected g i ds)

theorem candidates_perm {left right : List Impl}
    (same : ∀ i, i ∈ left ↔ i ∈ right) (g : Goal) :
    (candidates left g).Perm (candidates right g) := by
  apply (List.perm_ext_iff_of_nodup (candidates_nodup left g)
    (candidates_nodup right g)).mpr
  intro i
  simp only [mem_candidates,same]

/-- General recursive result, including missing and overlapping descendants.
Paterson well-formedness is checked for each visible environment independently. -/
theorem diagnose_equivalent {left right : List Impl}
    (same : ∀ i, i ∈ left ↔ i ∈ right)
    (lw : WellFormed left) (rw : WellFormed right) (g : Goal) :
    Equivalent (diagnose left lw g) (diagnose right rw g) := by
  have perm := candidates_perm same g
  cases hl : candidates left g with
  | nil =>
    have hr : candidates right g = [] := by simpa [hl] using perm.symm
    rw [diagnose_missing left lw g hl,diagnose_missing right rw g hr]
    exact .missing g
  | cons i rest =>
    cases rest with
    | nil =>
      have hr : candidates right g = [i] := by simpa [hl] using perm.symm
      rw [diagnose_selected left lw g i hl,diagnose_selected right rw g i hr]
      apply Equivalent.selected
      · simp
      · intro k hk hk'
        simp only [List.length_map] at hk hk'
        simp only [List.getElem_map]
        exact diagnose_equivalent same lw rw (i.constraints[k].subst (matchingSubst i.head g.args))
    | cons j rest =>
      cases hr : candidates right g with
      | nil => have := perm.length_eq; simp [hl,hr] at this
      | cons a more =>
        cases more with
        | nil => have := perm.length_eq; simp [hl,hr] at this
        | cons b more =>
          rw [diagnose_overlap left lw g i j rest hl,diagnose_overlap right rw g a b more hr]
          exact .overlap g _ _ (by simpa [hl,hr] using perm)
termination_by argsSize g.args
decreasing_by
  have hm := mem_candidates.mp (hl ▸ List.mem_singleton_self i)
  simpa only [Goal.subst,matched_head hm.2] using
    size_decreases (lw i hm.1) (List.getElem_mem (show k < i.constraints.length from by simpa only [List.length_map] using hk)) (matchingSubst i.head g.args)

theorem Equivalent.goal {t u : Tree} (h : Equivalent t u) : t.goal = u.goal := by
  cases h <;> rfl

/-- Compatibility status agrees at every related node, including failed roots. -/
theorem Equivalent.status_eq {t u : Tree} (h : Equivalent t u) : t.status = u.status := by
  induction h with
  | missing => rfl
  | overlap => simp only [Tree.status]
  | selected g i cs ds length children ih =>
    simp only [Tree.status]
    apply congrArg combine
    apply List.ext_getElem (by simp [length])
    intro k hk hk'
    simp only [List.getElem_map]
    exact ih k (by simpa using hk) (by simpa using hk')

/-- Full dictionary payload equality is stronger than equality of status. -/
theorem Equivalent.project_eq {t u : Tree} (h : Equivalent t u) : project t = project u := by
  induction h with
  | missing => rfl
  | overlap => simp only [project]
  | selected g i cs ds length children ih =>
    have mapped : cs.map project = ds.map project := by
      apply List.ext_getElem (by simp [length])
      intro k hk hk'
      simp only [List.getElem_map]
      exact ih k (by simpa using hk) (by simpa using hk')
    have mm := congrArg (List.mapM id) mapped
    simpa only [project,List.mapM_map,Function.comp_def,id_eq] using
      congrArg (Option.map (Plan.node i)) mm

/-- Each addressed child is retained; address existence is invariant as well. -/
theorem Equivalent.child {t u : Tree} (h : Equivalent t u) (k : Nat) :
    (t.children[k]?).isSome = (u.children[k]?).isSome ∧
      ∀ a b, t.children[k]? = some a → u.children[k]? = some b → Equivalent a b := by
  cases h with
  | missing g => simp [Tree.children]
  | overlap g hs ks perm => simp [Tree.children]
  | selected g i cs ds length children =>
    simp only [Tree.children]
    constructor
    · apply Bool.eq_iff_iff.mpr
      simp only [Option.isSome_iff_exists,List.getElem?_eq_some_iff]
      constructor
      · rintro ⟨a,ha,_⟩
        have hb : k < ds.length := by omega
        exact ⟨ds[k],hb,rfl⟩
      · rintro ⟨b,hb,_⟩
        have ha : k < cs.length := by omega
        exact ⟨cs[k],ha,rfl⟩
    · intro a b ha hb
      obtain ⟨hk,ae⟩ := List.getElem_of_getElem? ha
      obtain ⟨hk',be⟩ := List.getElem_of_getElem? hb
      rw [← ae,← be]
      exact children k hk hk'

/-- Any finite address observes the same goal, status and optional full Plan.
This does not erase failed siblings or stop traversal at a failed parent. -/
theorem Equivalent.follow {t u : Tree} (h : Equivalent t u) (path : List Nat) :
    (t.follow path).isSome = (u.follow path).isSome ∧
      ∀ a b, t.follow path = some a → u.follow path = some b → Equivalent a b := by
  induction path generalizing t u with
  | nil => simp only [Tree.follow,Option.isSome_some,true_and,Option.some.injEq]
           intro a b ha hb; subst a; subst b; exact h
  | cons k rest ih =>
    have child := h.child k
    cases ht : t.children[k]? with
    | none =>
      have hu : u.children[k]? = none := by
        have eq := child.1
        simp only [ht,Option.isSome_none] at eq
        cases hu : u.children[k]? with
        | none => rfl
        | some b => simp [hu] at eq
      simp [Tree.follow,ht,hu]
    | some a =>
      obtain ⟨b,hb⟩ := Option.isSome_iff_exists.mp (by rw [← child.1,ht]; rfl)
      simpa only [Tree.follow,ht,hb,Option.bind_some] using ih (child.2 a b ht hb)

end Yulang.CommonRoleDiagnosticOrder
