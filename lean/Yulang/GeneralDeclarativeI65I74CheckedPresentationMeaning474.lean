import Yulang.GeneralDeclarativeI65I74TypedConeQuotientSound474
import Yulang.GeneralDeclarativeI65I74FiniteObservationCorrespondence474

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.ObservationAlternatives473
open RetainedFull445 (FullProblem)
open GeneralDeclarativeI65 (Model)
open G04FiniteConstructorSemantics473 (Shell body)
open CommonNominalFullCarrier (Row Ty Equivalent Subtype observeTy)
open CommonRoleRegularGraph (Graph)
open CommonRoleGraphBisimulation (Relation)
open QuotientObservation471 (Across ConeWire Wire embedded cone replayCone
  cone_replay_sound checkAcrossWitness finite_relation_witness_preserves_the_regular_observation
  exact_cones_with_a_checked_cross_relation_have_the_same_return_bit)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans eqv_symm)

theorem equivalent_typed_value_of_checked_regular_presentations_over_one_signature
    {signs : List GeneralNormalizedObservation.Shape}
    {a : Graph n} {b : Graph m}
    {ta : Fin n → Shell (Fin n)} {tb : Fin m → Shell (Fin m)}
    (ca : ∀ i, encodeShell signs (ta i) = some (a i))
    (cb : ∀ j, encodeShell signs (tb j) = some (b j))
    {start : Fin n} {last : Fin m} (agree : Across a b start last) :
    Equivalent (G04FiniteConstructorSemantics473.value ta start)
      (G04FiniteConstructorSemantics473.value tb last) := by
  have approx (d : Nat) : observeTy d (G04FiniteConstructorSemantics473.value ta start) =
      observeTy d (G04FiniteConstructorSemantics473.value tb last) := by
    change CommonNominalSyntax.observe (CommonNominalSyntax.graph Row) (d+1)
        (CommonNominalSyntax.closeBlock (body ta) start) =
      CommonNominalSyntax.observe (CommonNominalSyntax.graph Row) (d+1)
        (CommonNominalSyntax.closeBlock (body tb) last)
    rw [←typed_block_graph_embeds_exactly,←typed_block_graph_embeds_exactly,
      ←constructor_observation_decodes_to_the_finite_typed_block_approximation ca,
      ←constructor_observation_decodes_to_the_finite_typed_block_approximation cb,
      agree (d+1)]
  constructor <;> intro d <;> rw [approx d] <;> exact CommonNominalFullDemand.producerLe_refl _

theorem accepted_alternative_graph_is_actual_cone_replay
    {s : GeneralDeclarativeI65.State} {t : Positions n}
    {r : Relation n} {root : Fin n} {w : ConeWire n k} {v : Wire k l} {bit}
    (read : readAlternatives s t r root w v = some bit) :
    replayCone (graphOf s t) root w v = some bit := by
  unfold readAlternatives at read
  split at read
  · exact read
  · cases read

theorem two_checked_observations_in_one_input_agree_in_bit_and_regular_type
    {p : FullProblem} {a : Positions n} {b : Positions m}
    {left : Relation n} {right : Relation m} {outer : Fin n} {inner : Fin m}
    {wl : ConeWire n u} {wr : ConeWire m v} {pl : Wire u k} {pr : Wire v l}
    {sl sr : Bool} {relation : Relation (u+v)}
    (palettes : a.signs = b.signs)
    (readL : readAlternatives p.old.state.core a left outer wl pl = some sl)
    (readR : readAlternatives p.old.state.core b right inner wr pr = some sr)
    (compare : checkAcrossWitness (cone wl) (cone wr) wl.site wr.site relation = true) :
    sl = sr ∧
    (∀ m : Model, FitsFull p.state m →
      Equivalent (interpretedAt p.old.state.core a m.assignment outer)
        (interpretedAt p.old.state.core b m.assignment inner)) := by
  have l := accepted_alternative_graph_is_actual_cone_replay readL
  have r := accepted_alternative_graph_is_actual_cone_replay readR
  have exactL := (cone_replay_sound l).1
  have exactR := (cone_replay_sound r).1
  refine ⟨exact_cones_with_a_checked_cross_relation_have_the_same_return_bit l r compare,?_⟩
  let ta : ∀ i, TypedObservationAt p.old.state.core a (embedded wl) i :=
    fun i => Classical.choose (exact_closed_observation_supplies_a_typed_shell_at_each_actual_site exactL i)
  let tb : ∀ i, TypedObservationAt p.old.state.core b (embedded wr) i :=
    fun i => Classical.choose (exact_closed_observation_supplies_a_typed_shell_at_each_actual_site exactR i)
  have ca : ∀ i, encodeShell a.signs (typedBy ta i) = some (cone wl i) := by
    intro i
    exact Classical.choose_spec (exact_closed_observation_supplies_a_typed_shell_at_each_actual_site exactL i)
  have cb : ∀ j, encodeShell a.signs (typedBy tb j) = some (cone wr j) := by
    intro j
    rw [palettes]
    exact Classical.choose_spec (exact_closed_observation_supplies_a_typed_shell_at_each_actual_site exactR j)
  have witness := finite_relation_witness_preserves_the_regular_observation compare
  have same := equivalent_typed_value_of_checked_regular_presentations_over_one_signature ca cb witness
  intro m fit
  have aFit := same_fits_full_input_keeps_unchanged_typed_observation_graph ta m fit wl.site
  have bFit := same_fits_full_input_keeps_unchanged_typed_observation_graph tb m fit wr.site
  rw [exactL.1] at aFit
  rw [exactR.1] at bFit
  exact eqv_trans aFit (eqv_trans same (eqv_symm bFit))

end Yulang.GeneralDeclarativeI65.I72.ObservationAlternatives473
