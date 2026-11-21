import Yulang.GeneralDeclarativeScopedRows322

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeNormalizeScope322
open GeneralDeclarationPatterns (Pattern WellScoped ArgsWellScoped normalize normalizeArgs merge variantRow rowPattern mergePayload)
open GeneralDeclarativeScopedRows322 (hide_scoped variant_entries row_pattern_scoped entries_scoped nonempty_after)

theorem merge_scoped {a b : Pattern} (one : WellScoped c a) (two : WellScoped c b) :
    WellScoped c (merge a b) := by
  by_cases same : a = b
  · simpa [merge,same] using one
  · cases first : variantRow a with
    | none => simpa [merge,same,first] using (show WellScoped c (.join a b) from ⟨one,two⟩)
    | some xs =>
      cases second : variantRow b with
      | none => simpa [merge,same,first,second] using (show WellScoped c (.join a b) from ⟨one,two⟩)
      | some ys =>
        simp only [merge,same,ite_false,first,second]
        have x := variant_entries a one first
        have y := variant_entries b two second
        have nonempty : xs ++ ys ≠ [] := fun empty => x.1 (List.append_eq_nil_iff.mp empty).1
        have mem : ∀ entry ∈ xs ++ ys, WellScoped c entry.2 :=
          fun e h => (List.mem_append.mp h).elim (x.2 e) (y.2 e)
        apply row_pattern_scoped
        · intro empty
          have len := (List.mergeSort_perm
            (Yulang.Variants.Merged.normalize mergePayload (xs++ys)).entries
               (fun l r => l.1 ≤ r.1)).length_eq
          rw [empty] at len
          exact nonempty_after nonempty (List.eq_nil_of_length_eq_zero len.symm)
        · intro entry found
          exact entries_scoped _ mem entry (List.mem_mergeSort.mp found)

theorem normal_length (patterns : List Pattern) : (normalizeArgs patterns).length = patterns.length := by
  induction patterns with
  | nil => rfl
  | cons h t ih => simp [normalizeArgs,ih]

mutual
 theorem checked_normal (c : GeneralDeclarationPatterns.Constructors) (p : Pattern)
    (known : WellScoped c p) : WellScoped c (normalize p) := by
  cases p with
  | var n => exact known
  | app ctor args =>
    obtain ⟨⟨decl,registered,arity⟩,typed⟩ := known
    exact ⟨⟨decl,registered,arity.trans (normal_length args).symm⟩,well_args c args typed⟩
  | record label p tail =>
    exact ⟨checked_normal c p known.1, hide_scoped label _ (checked_normal c tail known.2)⟩
  | variant tag p => exact checked_normal c p known
  | join p q => exact merge_scoped (checked_normal c p known.1) (checked_normal c q known.2)
 termination_by sizeOf p
 theorem well_args (c : GeneralDeclarationPatterns.Constructors) (ps : List Pattern)
    (known : ArgsWellScoped c ps) : ArgsWellScoped c (normalizeArgs ps) := by
  cases ps with
  | nil => trivial
  | cons p ps => exact ⟨checked_normal c p known.1,well_args c ps known.2⟩
 termination_by sizeOf ps
end

end Yulang.GeneralDeclarativeNormalizeScope322
