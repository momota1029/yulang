import Yulang.GeneralDeclarativeI65I72CompletedNativeRival406

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72
open GeneralDeclarativeI65
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeHead320 (Equation environment)
open GeneralNominalCenteredHeadMatExpressions (Expr value)
open CommonNominalFullCarrier (Equivalent nominal subtype_trans nominal_regular_invariant_exact)

/-- Semantic consistency of two retained source facts. Neither raw
row is picked by comparing fitted models. The conclusion gives
different alternatives the same denotation where required, not a
literal equality of point names or a new candidate rule. -/
theorem two_retained_unary_nominal_rows_agree_in_a_fitting_model406
    {s : State} {target leftTag rightTag leftChild rightChild : Nat}
    (first : (⟨target,.nominal leftTag [.variable leftChild]⟩ : Equation) ∈ s.core.current.ordinary.equations)
    (later : (⟨target,.nominal rightTag [.variable rightChild]⟩ : Equation) ∈ s.core.current.ordinary.equations)
    (m : Model) (fit : Fits s m) :
    leftTag = rightTag ∧ Equivalent (m.assignment leftChild).1 (m.assignment rightChild).1 := by
  have lo : Equivalent (m.assignment target).1 (nominal leftTag [.inl (m.assignment leftChild).1]) :=
    fit.1.1.2 _ first
  have hi : Equivalent (m.assignment target).1 (nominal rightTag [.inl (m.assignment rightChild).1]) :=
    fit.1.1.2 _ later
  have comparison := (nominal_regular_invariant_exact leftTag rightTag
    [.inl (m.assignment leftChild).1] [.inl (m.assignment rightChild).1]).mp (subtype_trans lo.2 hi.1)
  exact ⟨comparison.1,comparison.2.2 0 _ _ rfl rfl⟩

/-- Even when the same original lower point has two genuinely
completed and possibly different producer traces/ordinals, giving
them different nominal tags cannot survive one fitting model.
Different payload *names* can survive; only their denotations are
equivalent here. This is after election, not a test for electing. -/
theorem two_real_completed_inputs_to_the_same_lower_agree_in_model406
    {s q1 q2 d1 d2 o1 o2}
    (a : FiniteNative406 s q1 d1 o1) (b : FiniteNative406 s q2 d2 o2)
    (i : Fin q1.demand.outputs.length) (j : Fin q2.demand.outputs.length)
    {input : Capture} {head1 head2 child1 child2 : Nat}
    (atA : (o1 i).original.target = input.lower)
    (atB : (o2 j).original.target = input.lower)
    (fromA : TypedCovariantPoint404 head1 child1 (o1 i).rhs)
    (fromB : TypedCovariantPoint404 head2 child2 (o2 j).rhs)
    (m : Model) (fit : Fits s m) :
    head1 = head2 ∧ Equivalent (m.assignment child1).1 (m.assignment child2).1 := by
  have rowA := actual_typed_point_yields_literal_declared_code404 (o1 i).rhs fromA
  have rowB := actual_typed_point_yields_literal_declared_code404 (o2 j).rhs fromB
  exact two_retained_unary_nominal_rows_agree_in_a_fitting_model406
    (chosen_finite_native_output_retains_exact_nominal406 a i atA rowA.1 rowA.2)
    (chosen_finite_native_output_retains_exact_nominal406 b j atB rowB.1 rowB.2) m fit

/-- No source authorization can be forged from semantic agreement.
If the two authorized typed reads refer to one original routed
source site, the fitted model does nevertheless force their literal
payload names to agree. This is a post-choice consistency result. -/
theorem one_original_input_site_keeps_its_payload_name406 {s q row need}
    {front : UnaryHeadAt406 s q row need} (a b : OriginalPathAt406 front)
    (unique : SinglePhysical s.core front.gate.arg.center) (m : Model) (fit : Fits s m) :
    a.name = b.name := by
  have sameSlot := physical_origin_is_not_logical_equality unique a.inSource b.inSource a.routed b.routed
  have sameOriginal := same_native_slot_same_endpoint a.inSource b.inSource sameSlot m fit
  have see := a.decoded
  rw [sameOriginal,b.decoded] at see
  exact Option.some.inj see.symm

end Yulang.GeneralDeclarativeI65.I72
