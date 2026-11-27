import Yulang.GeneralDeclarativeI65I74FiniteObservationQuotient471

namespace Yulang.QuotientObservation471.Audit
open CommonRoleRegularGraph

def outerAndUnrolling : Graph 3 := #v[.structural 30 [1],.structural 40 [2],.structural 40 [2]].get

def exactWire : Wire 3 2 := ⟨#v[0,1,1],#v[.structural 30 [1],.structural 40 [1]]⟩

def notMinimal : Wire 3 3 := ⟨#v[0,1,2],#v[.structural 30 [1],.structural 40 [2],.structural 40 [2]]⟩

def nominalArg : Graph 1 := #v[.nominal 20 [0]].get
def nominalArgWire : Wire 1 1 := ⟨#v[0],#v[.nominal 20 [0]]⟩
def unresolved : Graph 1 := fun _ => .unresolved

theorem the_outer_constructor_reaches_but_is_not_on_its_own_class_cycle :
    replay outerAndUnrolling 0 exactWire = some false ∧
    replay outerAndUnrolling 1 exactWire = some true ∧
    replay outerAndUnrolling 2 exactWire = some true ∧
    replay outerAndUnrolling 1 notMinimal = none := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem explicit_nominal_argument_is_read_but_no_body_is_needed :
    replay nominalArg 0 nominalArgWire = some true ∧
    recursiveAt nominalArg 0 = false := by
  exact ⟨by decide +kernel,by decide +kernel⟩

/-- info: [some false, some true, some true, none, some true, none] -/
#guard_msgs in
#eval [replay outerAndUnrolling 0 exactWire,replay outerAndUnrolling 1 exactWire,
  replay outerAndUnrolling 2 exactWire,replay outerAndUnrolling 1 notMinimal,
  replay nominalArg 0 nominalArgWire,replay unresolved 0 ⟨#v[0],#v[.unresolved]⟩]

#print axioms partition_check_exact
#print axioms every_complete_graph_has_a_finite_partition
#print axioms quotient_cycle_iff_returns_up_to_equality
#print axioms exists_exact_finite_replay
#print axioms the_outer_constructor_reaches_but_is_not_on_its_own_class_cycle
#print axioms explicit_nominal_argument_is_read_but_no_body_is_needed
end Yulang.QuotientObservation471.Audit
