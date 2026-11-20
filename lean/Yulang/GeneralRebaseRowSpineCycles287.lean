import Yulang.GeneralRebaseRowChildPending287
import Yulang.GeneralDictionaryInspectionHeads215
import Yulang.GeneralNominalFiniteHeadInversion
namespace Yulang.GeneralRebaseRowSpineCycles287
open CommonNominalFullCarrier GeneralNominalRecursiveInspection
open GeneralDictionaryInspectionHeads215 GeneralNominalFiniteHeadInversion
open GeneralNominalOriginTerms (arity project)
open GeneralRebaseRowChildSource287 (R F)
variable {model : GeneralNominalCommonBridge.Assignment} {values : List Ty}
variable {arguments : List Argument} {index : Nat}
inductive Form where | scalar | row | wrap (body : Form)
def Form.value (r : Common.Row) : Form → Ty
  | .scalar => .base .int
  | .row => R r
  | .wrap body => F (body.value r)
def Form.rank : Form → Nat | .scalar | .row => 0 | .wrap body => body.rank+1
private theorem scalar_not_nominal (equal : Equivalent (.base .int) (nominal name args)) : False := by
  have tags := tag_subtype (tagged_scalar .int) (tagged_nominal name args) equal.1
  cases tags
private theorem name_diff (r : Common.Row) (body : Ty) (equal : Equivalent (R r) (F body)) : False := by
  exact (by decide : (6 : Nat) ≠ 0) ((nominal_regular_invariant_exact 6 0 _ _).mp equal.1).1
theorem equivalent_rank (r : Common.Row) (a b : Form) (equal : Equivalent (a.value r) (b.value r)) :
    a.rank = b.rank := by
  induction a generalizing b with
  | scalar =>
    cases b with
    | scalar => rfl
    | row => exact (scalar_not_nominal equal).elim
    | wrap => exact (scalar_not_nominal equal).elim
  | row =>
    cases b with
    | scalar => exact (scalar_not_nominal ⟨equal.2,equal.1⟩).elim
    | row => rfl
    | wrap body => exact (name_diff r _ equal).elim
  | wrap a ih =>
    cases b with
    | scalar => exact (scalar_not_nominal ⟨equal.2,equal.1⟩).elim
    | row => exact (name_diff r _ ⟨equal.2,equal.1⟩).elim
    | wrap b =>
      have both := (nominal_regular_invariant_exact 0 0 _ _).mp equal.1
      have args := both.2.2 0 (.inl (a.value r)) (.inl (b.value r)) rfl rfl
      exact congrArg (·+1) (ih b args)

theorem structural_child {r : Common.Row} (form : Form)
    (length : values.length = shape.arity) (equal : Equivalent (form.value r) (shapeValue shape values))
    (_found : values[index]? = some actual) :
    ∃ child : Form, child.rank < form.rank ∧ Equivalent actual (child.value r) := by
  cases form with
  | scalar =>
    have tags := tag_subtype (tagged_scalar .int) (tagged_shape shape values length) equal.1
    cases shape <;> cases tags
  | row =>
    have tags := tag_subtype (tagged_nominal 6 _) (tagged_shape shape values length) equal.1
    cases shape <;> cases tags
  | wrap =>
    have tags := tag_subtype (tagged_nominal 0 _) (tagged_shape shape values length) equal.1
    cases shape <;> cases tags
theorem nominal_child {r : Common.Row} (form : Form)
    (equal : Equivalent (form.value r) (nominal name arguments))
    (found : arguments[index]? = some (.inl actual)) :
    ∃ child : Form, child.rank < form.rank ∧ Equivalent actual (child.value r) := by
  cases form with
  | scalar => exact (scalar_not_nominal equal).elim
  | row =>
    have same := (nominal_regular_invariant_exact 6 _ _ _).mp equal.1
    have bound := (List.getElem?_eq_some_iff.mp found).1
    have len : 1 = arguments.length := same.2.1
    have zero : index = 0 := by omega
    subst index
    exact (same.2.2 0 (.inr r) (.inl actual) rfl found).elim
  | wrap body =>
    have same := (nominal_regular_invariant_exact 0 _ _ _).mp equal.1
    have bound := (List.getElem?_eq_some_iff.mp found).1
    have len : 1 = arguments.length := same.2.1
    have zero : index = 0 := by omega
    subst index
    have args := same.2.2 0 (.inl (body.value r)) (.inl actual) rfl found
    exact ⟨body,Nat.lt_succ_self _,⟨args.2,args.1⟩⟩

variable {r : Common.Row}
theorem observed_form (source : ∀ identity, ∃ form : Form, (model identity).1 = (form.value r))
    (seen : Observes model origin actual) : ∃ form : Form, Equivalent actual (form.value r) := by
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
    (same : ∀ value, Observes model origin value → Equivalent value (form.value r))
    (test : Test) (index : Fin (arity test)) (seen : Observes model (project origin test index) actual) :
    ∃ child : Form, child.rank < form.rank ∧ Equivalent actual (child.value r) := by
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

def Describes (r : Common.Row) (model : GeneralNominalCommonBridge.Assignment) (origin : Origin) (form : Form) : Prop :=
  ∃ actual, Observes model origin actual ∧ Equivalent actual (form.value r)

noncomputable def rank (r : Common.Row) (model : GeneralNominalCommonBridge.Assignment) (origin : Origin) : Nat := by
  classical
  exact if found : ∃ form, Describes r model origin form then (Classical.choose found).rank else 0

theorem rank_eq (meaning : Describes r model origin form)
    (unique : GeneralNominalReadbackFunctionality.Unique model origin) : rank r model origin = form.rank := by
  classical
  have found : ∃ form, Describes r model origin form := ⟨form,meaning⟩
  rw [rank,dite_eq_left found]
  obtain ⟨first,seenFirst,equalFirst⟩ := Classical.choose_spec found
  obtain ⟨last,seenLast,equalLast⟩ := meaning
  have same := unique first last seenFirst seenLast
  exact equivalent_rank r _ _
    ⟨subtype_trans equalFirst.2 (subtype_trans same.1 equalLast.1),
      subtype_trans equalLast.2 (subtype_trans same.2 equalFirst.1)⟩

theorem edge_decreases (valid : GeneralNominalVersionedJournal232.Models state model)
    (source : ∀ identity, ∃ form : Form, (model identity).1 = (form.value r))
    (edge : GeneralNominalVersionedCycles232.Edge state first last) : rank r model last < rank r model first := by
  obtain ⟨parent,test,index,_,one,two⟩ := edge
  have one := one model valid
  have two := two model valid
  obtain ⟨firstValue,seenFirst⟩ := one.1
  obtain ⟨firstForm,meaningFirst⟩ := observed_form source seenFirst
  obtain ⟨projected,seenProjected⟩ := two.1
  have parentMeaning : ∀ value, Observes model parent value → Equivalent value (firstForm.value r) := by
    intro value observed
    have same := one.2.2 firstValue value seenFirst observed
    exact ⟨subtype_trans same.2 meaningFirst.1,subtype_trans meaningFirst.2 same.1⟩
  obtain ⟨lastForm,smaller,meaningLast⟩ := projected_smaller firstForm parentMeaning test index seenProjected
  obtain ⟨lastValue,seenLast⟩ := two.2.1
  have equalLast := two.2.2 projected lastValue seenProjected seenLast
  have lastMeaning : Equivalent lastValue (lastForm.value r) :=
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

theorem acyclic (valid : GeneralNominalVersionedJournal232.Models state model)
    (source : ∀ identity, ∃ form : Form, (model identity).1 = (form.value r)) (origin) :
    ¬ GeneralNominalVersionedCycles232.Cyclic state origin := by
  have paths : ∀ a b, GeneralNominalVersionedCycles232.Path state a b → rank r model b ≤ rank r model a := by
    intro a b path
    induction path with
    | nil => exact Nat.le_refl _
    | cons edge path ih => exact Nat.le_trans ih (Nat.le_of_lt (edge_decreases valid source edge))
  rintro ⟨⟨next,edge,path⟩,_⟩
  have smaller := edge_decreases valid source edge
  have larger := paths _ _ path
  omega

end Yulang.GeneralRebaseRowSpineCycles287
