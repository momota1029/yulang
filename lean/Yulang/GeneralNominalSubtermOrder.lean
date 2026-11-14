import Yulang.GeneralPatternNormalizedComposition

/-! A substitution-stable comparison of finite open presentations. It permits
an opaque cyclic value and one of its finite unfoldings to share a smaller
capture presentation without equating their syntax. -/
namespace Yulang.GeneralNominalSubtermOrder
open GeneralNominalOriginTerms GeneralNominalRecursiveInspection
open GeneralNominalHeadMatchMass GeneralNominalCompoundReadback GeneralNominalOpenPatternLabels

inductive Below : Expr Nat → Expr Nat → Prop
  | refl : Below term term
  | child (test : Test) (children : Fin (arity test) → Expr Nat) (index : Fin (arity test)) :
      Below term (children index) → Below term (.node test children)
  | node (test : Test) (first last : Fin (arity test) → Expr Nat) :
      (∀ index, Below (first index) (last index)) → Below (.node test first) (.node test last)
  | trans : Below first middle → Below middle last → Below first last

def weightedTree (values : Nat → Nat) (term : Expr Nat) : Nat := weighted values (quote term)

theorem weighted_bind (term : Expr Nat) (substitution : Nat → Expr Nat) (values : Nat → Nat) :
    weightedTree values (term.bind substitution) =
      weightedTree (fun name => weightedTree values (substitution name)) term := by
  induction term with
  | leaf name => simp only [Expr.bind,weightedTree,quote,weighted,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero]
  | node test children ih =>
    cases test with
    | scalar => simp only [Expr.bind,weightedTree,quote,weighted]
    | structural shape =>
      cases shape <;>
        simp only [Expr.bind,weightedTree,quote,weighted,List.map_ofFn,Function.comp_def] at * <;>
        congr 1 <;> exact congrArg (fun f => (List.ofFn f).sum) (funext ih)
    | nominal name count =>
      simp only [Expr.bind,weightedTree,quote,weighted,List.map_ofFn,Function.comp_def] at *
      congr 1
      exact congrArg (fun f => (List.ofFn f).sum) (funext ih)

theorem below_bind (below : Below first last) (substitution : Nat → Expr Nat) :
    Below (first.bind substitution) (last.bind substitution) := by
  induction below with
  | refl => exact .refl
  | child test children index below ih => exact .child test _ index ih
  | node test first last below ih => exact .node test _ _ ih
  | trans first last one two => exact .trans one two

private theorem sum_below (first last : Fin n → Nat) (below : ∀ index, first index ≤ last index) :
    (List.ofFn first).sum ≤ (List.ofFn last).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.ofFn_succ,List.sum_cons]
    exact Nat.add_le_add (below 0) (ih _ _ (fun index => below index.succ))

private theorem member_sum {values : List Nat} {value : Nat} (member : value ∈ values) : value ≤ values.sum := by
  induction values with
  | nil => cases member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with rfl | member
    · simp
    · simpa only [List.sum_cons] using Nat.le_trans (ih member) (Nat.le_add_left _ _)

theorem child_weight (test : Test) (children : Fin (arity test) → Expr Nat)
    (index : Fin (arity test)) (values : Nat → Nat) :
    weightedTree values (children index) ≤ weightedTree values (.node test children) := by
  have bound := member_sum (List.mem_ofFn.mpr ⟨index,rfl⟩ : weightedTree values (children index) ∈
    List.ofFn (fun index => weightedTree values (children index)))
  cases test with
  | scalar => exact Fin.elim0 index
  | structural shape =>
    cases shape <;> simp only [weightedTree,quote,weighted,List.map_ofFn,Function.comp_def] <;>
      exact Nat.le_trans bound (Nat.le_add_left _ _)
  | nominal name count =>
    simp only [weightedTree,quote,weighted,List.map_ofFn,Function.comp_def]
    exact Nat.le_trans bound (Nat.le_add_left _ _)

theorem weighted_below (below : Below first last) (values : Nat → Nat) :
    weightedTree values first ≤ weightedTree values last := by
  induction below with
  | refl => exact Nat.le_refl _
  | child test children index below ih => exact Nat.le_trans ih (child_weight test children index values)
  | node test first last below ih =>
    cases test with
    | scalar => exact Nat.le_refl _
    | structural shape =>
      cases shape <;> simp only [weightedTree,quote,weighted,List.map_ofFn,Function.comp_def] <;>
        exact Nat.add_le_add_left (sum_below _ _ ih) _
    | nominal name count =>
      simp only [weightedTree,quote,weighted,List.map_ofFn,Function.comp_def]
      exact Nat.add_le_add_left (sum_below _ _ ih) _
  | trans first last one two => exact Nat.le_trans one two

theorem mass_below (below : Below first last) : weight first ≤ weight last := weighted_below below (fun _ => 1)

theorem mass_after_substitution (below : Below first last) (substitution : Nat → Expr Nat) :
    weight (first.bind substitution) ≤ weight (last.bind substitution) := mass_below (below_bind below substitution)

end Yulang.GeneralNominalSubtermOrder
