import Yulang.GeneralDeclarativeI65I74FiniteObservationCorrespondence474

set_option backward.isDefEq.respectTransparency false
namespace Yulang.QuotientObservation471.OrdinalPath483
open CommonRoleRegularGraph (Graph successors)
open CommonRoleGraphBisimulation (observe)

def followSlots (g : Graph n) (source : Fin n) : List Nat → Option (List (Fin n))
  | [] => some []
  | ix::later => do
    let child ← (successors g source)[ix]?
    let rest ← followSlots g child later
    some (child::rest)

theorem corresponding_ordinal_child_exists_and_preserves_observations
    {x : Graph n} {y : Graph m} {left : Fin n} {right : Fin m}
    (agree : Across x y left right) (ordinal : Nat) {child : Fin n}
    (leftChild : (successors x left)[ordinal]? = some child) :
    ∃ next : Fin m, (successors y right)[ordinal]? = some next ∧ Across x y child next := by
  have sameAll := across_nodes_keep_their_actual_successor_observations agree
  cases got : (successors y right)[ordinal]? with
  | none =>
    have same := congrArg (fun row => row[ordinal]?) (sameAll 0)
    simp [List.getElem?_map, leftChild, got] at same
  | some other =>
    refine ⟨other,rfl,?_⟩
    intro d
    have test := congrArg (fun row => row[ordinal]?) (sameAll d)
    simpa [List.getElem?_map,leftChild,got] using test

inductive AlignedSites (left : Graph n) (right : Graph m) : List (Fin n) → List (Fin m) → Prop where
  | nil : AlignedSites left right [] []
  | cons : Across left right a b → AlignedSites left right more rest →
      AlignedSites left right (a::more) (b::rest)

theorem exact_full_ordinal_path_lifts_at_the_same_each_child_position
    {left : Graph n} {right : Graph m} {root : Fin n} {other : Fin m}
    (agree : Across left right root other) (words : List Nat) {visited : List (Fin n)}
    (hit : followSlots left root words = some visited) :
    ∃ there, followSlots right other words = some there ∧ AlignedSites left right visited there := by
  induction words generalizing root other visited with
  | nil =>
    have tail : visited = [] := (Option.some.inj hit).symm
    subst visited
    exact ⟨[],rfl,.nil⟩
  | cons label rest ih =>
    rw [followSlots] at hit
    cases atChild : (successors left root)[label]? with
    | none => simp [atChild,bind,Option.bind] at hit
    | some first =>
      cases afterwards : followSlots left first rest with
      | none => simp [atChild,afterwards,bind,Option.bind] at hit
      | some remaining =>
        simp only [atChild,afterwards,bind,Option.bind,Option.some.injEq] at hit
        subst visited
        obtain ⟨firstAlt,whichAlt,childSame⟩ :=
          corresponding_ordinal_child_exists_and_preserves_observations agree label atChild
        obtain ⟨later,readAlt,laterSame⟩ := ih childSame afterwards
        exact ⟨firstAlt::later,by simp [followSlots,whichAlt,readAlt,bind,Option.bind],
          .cons childSame laterSame⟩

theorem corresponding_chosen_ordinal_nodes_agree_in_every_return_predicate
    {left : Graph n} {right : Graph m} {xs : List (Fin n)} {ys : List (Fin m)}
    (same : AlignedSites left right xs ys) :
    ∀ (i : Nat) a b, xs[i]? = some a → ys[i]? = some b →
      (ReturnsUpToEquality left a ↔ ReturnsUpToEquality right b) := by
  induction same with
  | nil => intro _ _ _ no; simp at no
  | cons head _ ih =>
    intro i a b x y
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at x y
      subst a; subst b
      exact quotient_nonempty_return_is_invariant_under_every_equal_regular_presentation head
    | succ i =>
      exact ih i a b (by simpa only [List.getElem?_cons_succ] using x)
        (by simpa only [List.getElem?_cons_succ] using y)

end Yulang.QuotientObservation471.OrdinalPath483
