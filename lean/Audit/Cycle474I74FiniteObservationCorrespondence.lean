import Yulang.GeneralDeclarativeI65I74FiniteObservationCorrespondence474

open Yulang.QuotientObservation471
#print axioms quotient_nonempty_return_is_invariant_under_every_equal_regular_presentation
#print axioms unrelated_unknowns_do_not_block_comparing_exact_closed_cones
#print axioms exact_observation_at_each_real_site_is_independent_of_closed_cone_presentation
#print axioms finite_relation_witness_preserves_the_regular_observation
#print axioms each_equal_pair_of_closed_presentations_has_a_finite_witness

namespace Yulang.QuotientObservation471
open CommonRoleRegularGraph

def shortFiniteShape : Graph 2 := fun i =>
  if i = 0 then .structural 10 [1] else .structural 20 [1]

def expandedFiniteShape : Graph 3 := fun i =>
  if i = 0 then .structural 10 [1] else .structural 20 [2]

def exactSmallCorrespondence : CommonRoleGraphBisimulation.Relation 5 :=
  [(0,2),(1,3),(1,4)]

/-- info: [true, true, false, false] -/
#guard_msgs in
#eval [checkAcrossWitness shortFiniteShape expandedFiniteShape 0 0 exactSmallCorrespondence,
  checkAcrossWitness shortFiniteShape expandedFiniteShape 1 1 exactSmallCorrespondence,
  checkAcrossWitness shortFiniteShape expandedFiniteShape 0 1 exactSmallCorrespondence,
  checkAcrossWitness shortFiniteShape expandedFiniteShape 0 0 [(0,2),(1,3)]]

end Yulang.QuotientObservation471

open Yulang.QuotientObservation471
#print axioms exact_cones_with_a_checked_cross_relation_have_the_same_return_bit
