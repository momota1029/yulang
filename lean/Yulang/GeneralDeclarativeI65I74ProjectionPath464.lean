import Yulang.GeneralDeclarativeGraphRows321
import Yulang.GeneralDeclarativeK2Alias321

namespace Yulang.GeneralDeclarativeK2Graph321.AddAtOneSource

/-- A structural view does not classify ordinary models. This relation
says exactly where new graph observations may live; the caller must
prove it separately for actual row-plus-alias handling. -/
structure AdditionAt (before after : View) (root : Nat) : Prop where
  keep : ∀ v shape, before v shape → after v shape
  only : ∀ v shape, after v shape → v = root ∨ before v shape

theorem rooted_return_preserved_exactly {before after : View} {root : Nat}
    (changeAt : AdditionAt before after root) (start : Nat) :
    Path after start root ↔ Path before start root := by
  constructor
  · intro afterPath
    have collapse {x y : Nat} (h : Path after x y) (last : y = root) : Path before x root := by
      induction h with
      | refl a =>
        subst a
        exact .refl root
      | next step _ ih =>
        obtain ⟨head,seen,child⟩ := step
        rcases changeAt.only _ _ seen with here | old
        · rw [here]
          exact .refl _
        · exact .next ⟨head,old,child⟩ (ih last)
    exact collapse afterPath rfl
  · have lift {a b : Nat} (path : Path before a b) : Path after a b := by
      induction path with
      | refl => exact .refl _
      | next d _ ih =>
        obtain ⟨head,seen,child⟩ := d
        exact .next ⟨head,changeAt.keep _ _ seen,child⟩ ih
    exact lift

theorem an_added_root_cycle_has_exact_old_return {before after : View} {root : Nat}
    (changeAt : AdditionAt before after root) :
    OnCycle after root ↔ OnCycle before root ∨
      ∃ child, Descends after root child ∧ ¬ Descends before root child ∧
        Path before child root := by
  constructor
  · rintro ⟨child,rootEdge,returnPath⟩
    have oldReturn := (rooted_return_preserved_exactly changeAt child).mp returnPath
    by_cases old : Descends before root child
    · exact .inl ⟨child,old,oldReturn⟩
    · exact .inr ⟨child,rootEdge,old,oldReturn⟩
  · rintro (old|⟨child,edge,_,back⟩)
    · exact closed_cycle_add_edges changeAt.keep old
    · exact ⟨child,edge,(rooted_return_preserved_exactly changeAt child).mpr back⟩

theorem all_new_heads_away_from_existing_returns_preserve_root_k2 {before after : View} {root : Nat}
    (changeAt : AdditionAt before after root)
    (clean : ∀ child, Descends after root child → ¬ Descends before root child →
      ¬ Path before child root) :
    OnCycle after root ↔ OnCycle before root := by
  rw [an_added_root_cycle_has_exact_old_return changeAt]
  exact or_iff_left_of_imp fun ⟨child,edge,new,back⟩ => (clean child edge new back).elim

/-- Paths can be expressed with at most one new edge: the old prefix
before the first visit to the source, and the old suffix after the last
new edge. No assumption of acyclicity is needed for this normal form. -/
theorem exact_path_normal_form_for_one_new_source {before after : View} {root : Nat}
    (changeAt : AdditionAt before after root) {a b : Nat} :
    Path after a b ↔ Path before a b ∨
      (Path before a root ∧ ∃ next, Descends after root next ∧
        ¬ Descends before root next ∧ Path before next b) := by
  constructor
  · intro actual
    induction actual with
    | refl v => exact Or.inl (.refl v)
    | @next x y z edge _ ih =>
      by_cases old : Descends before x y
      · rcases ih with kept | ⟨preWalk,tail⟩
        · exact .inl (.next old kept)
        · exact .inr ⟨.next old preWalk,tail⟩
      · obtain ⟨shape,seen,child⟩ := edge
        have eq : x = root := (changeAt.only x shape seen).resolve_right
          (fun impossible => old ⟨shape,impossible,child⟩)
        subst x
        rcases ih with kept|⟨_,tail⟩
        · exact .inr ⟨.refl root,y,⟨shape,seen,child⟩,old,kept⟩
        · exact .inr ⟨.refl root,tail⟩
  · have lift {u v : Nat} (old : Path before u v) : Path after u v := by
      induction old with
      | refl => exact .refl _
      | next edge _ ih =>
        obtain ⟨head,seen,child⟩ := edge
        exact .next ⟨head,changeAt.keep _ _ seen,child⟩ ih
    rintro (old | ⟨preWalk,next,edge,_,rest⟩)
    · exact lift old
    · exact path_cat (lift preWalk) (.next edge (lift rest))

/-- The exact return test also excludes any fabricated cycle away from
the materialized source, not just at the source itself. -/
theorem no_old_return_for_new_edges_preserves_every_cycle {before after : View} {root : Nat}
    (changeAt : AdditionAt before after root)
    (clean : ∀ child, Descends after root child → ¬ Descends before root child →
      ¬ Path before child root) (v : Nat) :
    OnCycle after v ↔ OnCycle before v := by
  refine ⟨?_,closed_cycle_add_edges changeAt.keep⟩
  rintro ⟨c,d,ret⟩
  by_cases old : Descends before v c
  · rcases (exact_path_normal_form_for_one_new_source changeAt).mp ret with back | ⟨pre,b,e,f,tail⟩
    · exact ⟨c,old,back⟩
    · exact (clean b e f (path_cat tail (.next old pre))).elim
  · obtain ⟨shape,yes,child⟩ := d
    have eq : v = root := (changeAt.only v shape yes).resolve_right
      (fun base => old ⟨shape,base,child⟩)
    subst v
    exact (clean c ⟨shape,yes,child⟩ old ((rooted_return_preserved_exactly changeAt c).mp ret)).elim


open GeneralDeclarativeHead320 (State Equation)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeGraphRows321 (observed structural shapeOf)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeLowerKnown321 (Alias alias_symm alias_mono)

/-- An analysis of two separately supplied ordinary snapshots. This
does not authorize insertion or provide any source/issuer evidence. -/
def extendedRows (s : State) (r : Equation) : State :=
  {s with equations := s.equations ++ [r]}

theorem adding_a_non_alias_row_preserves_actual_aliases (s : State) (r : Equation)
    (notAlias : ∀ n, r.right ≠ .variable n) (a b : Nat) :
    Alias (extendedRows s r) a b ↔ Alias s a b := by
  constructor
  · intro extended
    induction extended with
    | bounds a b => exact .bounds a b
    | forward seen =>
      change _ ∈ s.equations ++ [r] at seen
      rcases List.mem_append.mp seen with old|singleton
      · exact .forward old
      · exact (notAlias _ (congrArg Equation.right (List.mem_singleton.mp singleton).symm)).elim
    | backward seen =>
      change _ ∈ s.equations ++ [r] at seen
      rcases List.mem_append.mp seen with old|singleton
      · exact .backward old
      · exact (notAlias _ (congrArg Equation.right (List.mem_singleton.mp singleton).symm)).elim
    | trans _ _ h ih => exact .trans h ih
  · apply alias_mono (s := s) (t := extendedRows s r) rfl
    exact fun _ h => List.mem_append_left _ h

theorem actual_new_observation_starts_only_at_isolated_source
    (s : State) (root : Nat) (term : Expr)
    (notAlias : ∀ n, term ≠ .variable n) (alone : ∀ a, Alias s a root → a = root) :
    AdditionAt (structural s) (structural (extendedRows s ⟨root,term⟩)) root := by
  let r : Equation := ⟨root,term⟩
  have stable := adding_a_non_alias_row_preserves_actual_aliases s r notAlias
  constructor
  · rintro src h ⟨a,auth,e,seen,shape⟩
    exact ⟨a,(stable src a).mpr auth,e,List.mem_append_left _ seen,shape⟩
  · rintro src h ⟨a,auth,e,seen,shape⟩
    change _ ∈ s.equations ++ [r] at seen
    rcases List.mem_append.mp seen with before|new
    · exact .inr ⟨a,(stable src a).mp auth,e,before,shape⟩
    · have same := congrArg Equation.left (List.mem_singleton.mp new)
      change a = root at same
      subst a
      exact .inl (alone src ((stable src root).mp auth))

/-- If a separately supplied nonalias row opens a shape only at a singleton
alias class, and no new child returns to that class in the original view,
then the exact actual AliasCycle predicate is unchanged at *every* old slot.
The proof does not require that the child be acyclic. -/
theorem singleton_single_row_alias_cycles_are_exactly_preserved
    (s : State) (root : Nat) (term : Expr)
    (notAlias : ∀ n, term ≠ .variable n) (alone : ∀ a, Alias s a root → a = root)
    (noReturn : ∀ shape, shapeOf term = some shape → ∀ child ∈ shape.children,
      ¬ Path (structural s) child root) (v : Nat) :
    AliasCycle (extendedRows s ⟨root,term⟩) (observed (extendedRows s ⟨root,term⟩)) v ↔
      AliasCycle s (observed s) v := by
  let r : Equation := ⟨root,term⟩
  have changeAt := actual_new_observation_starts_only_at_isolated_source s root term notAlias alone
  have stable := adding_a_non_alias_row_preserves_actual_aliases s r notAlias
  have lift {a b : Nat} (h : Path (structural s) a b) : Path (structural (extendedRows s r)) a b :=
    (exact_path_normal_form_for_one_new_source changeAt).mpr (.inl h)
  have clean {child : Nat} (seen : Descends (structural (extendedRows s r)) root child)
      (notOld : ¬ Descends (structural s) root child) : ¬ Path (structural s) child root := by
    obtain ⟨h,⟨a,auth,e,mem,shape⟩,take⟩ := seen
    change _ ∈ s.equations ++ [r] at mem
    rcases List.mem_append.mp mem with old|new
    · exact (notOld ⟨h,⟨a,(stable root a).mp auth,e,old,shape⟩,take⟩).elim
    · have eq : e = term := congrArg Equation.right (List.mem_singleton.mp new)
      subst e
      exact noReturn h shape child take
  constructor
  · rintro ⟨c,last,first,rest,link⟩
    have same := (stable last v).mp link
    by_cases old : Descends (structural s) v c
    · rcases (exact_path_normal_form_for_one_new_source changeAt).mp rest with original | ⟨reach,d,bigger,new,suffix⟩
      · exact ⟨c,last,old,original,same⟩
      · have edge := edge_transport same old
        exact (clean bigger new (path_cat suffix (.next edge reach))).elim
    · obtain ⟨shape,seen,child⟩ := first
      have eq : v = root := (changeAt.only v shape seen).resolve_right (fun prior => old ⟨shape,prior,child⟩)
      subst v
      have t := alone last same
      subst last
      exact (clean ⟨shape,seen,child⟩ old ((rooted_return_preserved_exactly changeAt c).mp rest)).elim
  · rintro ⟨c,last,⟨shape,first,found⟩,rest,link⟩
    exact ⟨c,last,⟨shape,changeAt.keep v shape first,found⟩,lift rest,(stable last v).mpr link⟩

end Yulang.GeneralDeclarativeK2Graph321.AddAtOneSource
