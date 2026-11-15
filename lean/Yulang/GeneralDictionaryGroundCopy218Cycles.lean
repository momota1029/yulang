import Yulang.GeneralDictionaryGroundCopy218Refresh
import Yulang.GeneralNominalCenteredHeadMatPairCycles
import Yulang.GeneralNominalCenteredHeadMatHeadShape

/-! A finite semantic rank for the ground-copy candidate. The rank covers all
actual observation origins, including nominal projections; it is not a claim
about reachability or local selection of that candidate. -/
namespace Yulang.GeneralDictionaryGroundCopy218Cycles
open CommonNominalFullCarrier GeneralNominalRecursiveInspection
open GeneralDictionaryInspectionHeads215 GeneralNominalFiniteHeadInversion
open GeneralNominalOriginTerms (arity project)
open GeneralDictionaryGroundCopy218Refresh (top_no_head)
variable {model : GeneralNominalCommonBridge.Assignment} {values : List Ty}
variable {arguments : List Argument} {index : Nat}

inductive Atom where
  | bottom | top | scalar (base : Inference.Base)

def Atom.value : Atom → Ty
  | .bottom => .bottom
  | .top => .top
  | .scalar base => .base base

inductive Form where
  | atom (value : Atom)
  | variant (payload : Atom)
  | foo

def Form.value : Form → Ty
  | .atom a => a.value
  | .variant payload => CommonNominalFullCarrier.variant 0 payload.value
  | .foo => nominal 5 [.inl GeneralDictionaryLooseVariant217.first,.inl GeneralDictionaryLooseVariant217.second]

def Form.rank : Form → Nat
  | .atom _ => 0
  | .variant _ => 1
  | .foo => 2

private theorem atom_not_shape (atom : Atom) (length : values.length = shape.arity)
    (equal : Equivalent atom.value (shapeValue shape values)) : False := by
  cases atom with
  | bottom => exact GeneralNominalCenteredHeadMatHeadShape.bottom_no_head (.structural shape) ⟨values,length,equal⟩
  | top => exact top_no_head (.structural shape) ⟨values,length,equal⟩
  | scalar base =>
      have tags := tag_subtype (tagged_scalar base) (tagged_shape shape values length) equal.1
      cases shape <;> cases tags

private theorem atom_not_nominal (atom : Atom)
    (equal : Equivalent atom.value (nominal name args)) : False := by
  cases atom with
  | bottom => exact GeneralNominalCenteredHeadMatHeadShape.bottom_no_head (.nominal name args.length) ⟨args,rfl,equal⟩
  | top => exact top_no_head (.nominal name args.length) ⟨args,rfl,equal⟩
  | scalar base =>
      have tags := tag_subtype (tagged_scalar base) (tagged_nominal name args) equal.1
      cases tags

private theorem variant_not_nominal (payload : Atom)
    (equal : Equivalent (variant 0 payload.value) (nominal name args)) : False := by
  have tags := tag_subtype (show Tagged (variant 0 payload.value) (.variant 0) from by intro env; rfl)
    (tagged_nominal name args) equal.1
  cases tags

theorem equivalent_rank (a b : Form) (equal : Equivalent a.value b.value) : a.rank = b.rank := by
  cases a with
  | atom atom =>
      cases b with
      | atom => rfl
      | variant payload => exact False.elim (atom_not_shape atom (shape := .variant 0) (values := [payload.value]) rfl equal)
      | foo => exact False.elim (atom_not_nominal atom equal)
  | variant payload =>
      cases b with
      | atom atom => exact False.elim (atom_not_shape atom (shape := .variant 0) (values := [payload.value]) rfl ⟨equal.2,equal.1⟩)
      | variant => rfl
      | foo => exact False.elim (variant_not_nominal payload equal)
  | foo =>
      cases b with
      | atom atom => exact False.elim (atom_not_nominal atom ⟨equal.2,equal.1⟩)
      | variant payload => exact False.elim (variant_not_nominal payload ⟨equal.2,equal.1⟩)
      | foo => rfl

theorem structural_child (form : Form)
    (length : values.length = shape.arity) (equal : Equivalent form.value (shapeValue shape values))
    (found : values[index]? = some actual) :
    ∃ child : Form, child.rank < form.rank ∧ Equivalent actual child.value := by
  cases form with
  | atom atom => exact False.elim (atom_not_shape atom length equal)
  | foo =>
      have tags := tag_subtype (tagged_nominal 5 _) (tagged_shape shape values length) equal.1
      cases shape <;> cases tags
  | variant payload =>
      have tags := tag_subtype (show Tagged (variant 0 payload.value) (.variant 0) from by intro env; rfl)
        (tagged_shape shape values length) equal.1
      have shapeEq : shape = .variant 0 := by
        cases shape <;> cases tags <;> rfl
      subst shape
      have zero : index = 0 := by
        have bound := (List.getElem?_eq_some_iff.mp found).1
        change values.length = 1 at length
        omega
      subst index
      refine ⟨.atom payload,by change 0 < 1; decide,?_⟩
      exact GeneralNominalStructuralReadback.shape_payload (.variant 0) trivial values [payload.value]
        length rfl found rfl ⟨equal.2,equal.1⟩

theorem nominal_child (form : Form)
    (equal : Equivalent form.value (nominal name arguments))
    (found : arguments[index]? = some (.inl actual)) :
    ∃ child : Form, child.rank < form.rank ∧ Equivalent actual child.value := by
  cases form with
  | atom atom => exact False.elim (atom_not_nominal atom equal)
  | variant payload => exact False.elim (variant_not_nominal payload equal)
  | foo =>
      have invariant := (nominal_regular_invariant_exact _ _ _ _).mp equal.1
      have bound : index < 2 := by
        have bound := (List.getElem?_eq_some_iff.mp found).1
        have length := invariant.2.1
        change 2 = arguments.length at length
        omega
      have positions : index = 0 ∨ index = 1 := by omega
      rcases positions with rfl | rfl
      · have same := invariant.2.2 0 (.inl GeneralDictionaryLooseVariant217.first) (.inl actual) rfl found
        exact ⟨.variant (.scalar .int),by decide,⟨same.2,same.1⟩⟩
      · have same := invariant.2.2 1 (.inl GeneralDictionaryLooseVariant217.second) (.inl actual) rfl found
        exact ⟨.variant (.scalar .bool),by decide,⟨same.2,same.1⟩⟩

theorem observed_form (source : ∀ identity, ∃ form : Form, (model identity).1 = form.value)
    (seen : Observes model origin actual) : ∃ form : Form, Equivalent actual form.value := by
  induction seen with
  | source identity =>
      obtain ⟨form,equal⟩ := source identity
      exact ⟨form,equal ▸ ⟨subtype_refl _,subtype_refl _⟩⟩
  | nominal parent nominalHead found ih =>
      obtain ⟨form,equal⟩ := ih
      obtain ⟨child,_,meaning⟩ := nominal_child form
        ⟨subtype_trans equal.2 nominalHead.1,subtype_trans nominalHead.2 equal.1⟩ found
      exact ⟨child,meaning⟩
  | structural parent length shapeHead found ih =>
      obtain ⟨form,equal⟩ := ih
      obtain ⟨child,_,meaning⟩ := structural_child form length
        ⟨subtype_trans equal.2 shapeHead.1,subtype_trans shapeHead.2 equal.1⟩ found
      exact ⟨child,meaning⟩

theorem projected_smaller (form : Form)
    (same : ∀ value, Observes model origin value → Equivalent value form.value)
    (test : Test) (index : Fin (arity test)) (seen : Observes model (project origin test index) actual) :
    ∃ child : Form, child.rank < form.rank ∧ Equivalent actual child.value := by
  cases test with
  | scalar => exact Fin.elim0 index
  | nominal =>
      cases seen with
      | nominal parent nominalHead found =>
          have equal := same _ parent
          exact nominal_child form
            ⟨subtype_trans equal.2 nominalHead.1,subtype_trans nominalHead.2 equal.1⟩ found
  | structural shape =>
      cases seen with
      | structural parent length shapeHead found =>
          have equal := same _ parent
          exact structural_child form length
            ⟨subtype_trans equal.2 shapeHead.1,subtype_trans shapeHead.2 equal.1⟩ found

def Describes (model : GeneralNominalCommonBridge.Assignment) (origin : Origin) (form : Form) : Prop :=
  ∃ actual, Observes model origin actual ∧ Equivalent actual form.value

noncomputable def rank (model : GeneralNominalCommonBridge.Assignment) (origin : Origin) : Nat := by
  classical
  exact if found : ∃ form, Describes model origin form then (Classical.choose found).rank else 0

theorem rank_eq (meaning : Describes model origin form)
    (unique : GeneralNominalReadbackFunctionality.Unique model origin) : rank model origin = form.rank := by
  classical
  have found : ∃ form, Describes model origin form := ⟨form,meaning⟩
  rw [rank,dite_eq_left found]
  obtain ⟨first,seenFirst,equalFirst⟩ := Classical.choose_spec found
  obtain ⟨last,seenLast,equalLast⟩ := meaning
  have same := unique first last seenFirst seenLast
  exact equivalent_rank _ _
    ⟨subtype_trans equalFirst.2 (subtype_trans same.1 equalLast.1),
      subtype_trans equalLast.2 (subtype_trans same.2 equalFirst.1)⟩

theorem edge_decreases (valid : GeneralNominalCenteredHeadMatStepJournal.Models state model)
    (source : ∀ identity, ∃ form : Form, (model identity).1 = form.value)
    (edge : GeneralNominalCenteredHeadMatStepCycles.Edge state first last) : rank model last < rank model first := by
  obtain ⟨parent,test,index,_,one,two⟩ := edge
  have one := one model valid
  have two := two model valid
  obtain ⟨firstValue,seenFirst⟩ := one.1
  obtain ⟨firstForm,meaningFirst⟩ := observed_form source seenFirst
  obtain ⟨projected,seenProjected⟩ := two.1
  have parentMeaning : ∀ value, Observes model parent value → Equivalent value firstForm.value := by
    intro value observed
    have same := one.2.2 firstValue value seenFirst observed
    exact ⟨subtype_trans same.2 meaningFirst.1,subtype_trans meaningFirst.2 same.1⟩
  obtain ⟨lastForm,smaller,meaningLast⟩ := projected_smaller firstForm parentMeaning test index seenProjected
  obtain ⟨lastValue,seenLast⟩ := two.2.1
  have equalLast := two.2.2 projected lastValue seenProjected seenLast
  have lastMeaning : Equivalent lastValue lastForm.value :=
    ⟨subtype_trans equalLast.2 meaningLast.1,subtype_trans meaningLast.2 equalLast.1⟩
  have uniqueFirst : GeneralNominalReadbackFunctionality.Unique model first := by
    obtain ⟨value,seen⟩ := one.2.1
    intro a b sa sb
    exact ⟨subtype_trans (one.2.2 a value sa seen).1 (one.2.2 b value sb seen).2,
      subtype_trans (one.2.2 b value sb seen).1 (one.2.2 a value sa seen).2⟩
  have uniqueLast : GeneralNominalReadbackFunctionality.Unique model last := by
    intro a b sa sb
    exact ⟨subtype_trans (two.2.2 projected a seenProjected sa).2 (two.2.2 projected b seenProjected sb).1,
      subtype_trans (two.2.2 projected b seenProjected sb).2 (two.2.2 projected a seenProjected sa).1⟩
  rw [rank_eq ⟨firstValue,seenFirst,meaningFirst⟩ uniqueFirst,
    rank_eq ⟨lastValue,seenLast,lastMeaning⟩ uniqueLast]
  exact smaller

theorem acyclic (valid : GeneralNominalCenteredHeadMatStepJournal.Models state model)
    (source : ∀ identity, ∃ form : Form, (model identity).1 = form.value) (origin) :
    ¬ GeneralNominalCenteredHeadMatStepCycles.Cyclic state origin := by
  have paths : ∀ a b, GeneralNominalCenteredHeadMatStepCycles.Path state a b → rank model b ≤ rank model a := by
    intro a b path
    induction path with
    | nil => exact Nat.le_refl _
    | cons edge path ih => exact Nat.le_trans ih (Nat.le_of_lt (edge_decreases valid source edge))
  rintro ⟨⟨next,edge,path⟩,_⟩
  have smaller := edge_decreases valid source edge
  have larger := paths _ _ path
  omega

end Yulang.GeneralDictionaryGroundCopy218Cycles
