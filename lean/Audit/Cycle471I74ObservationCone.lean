import Yulang.GeneralDeclarativeI65I74ObservationCone471

namespace Yulang.QuotientObservation471.ConeAudit
open CommonRoleRegularGraph

def ambient : Graph 4 :=
  #v[.structural 30 [1],.structural 40 [2],.structural 40 [2],.unresolved].get

def impeded : Graph 4 :=
  #v[.structural 30 [1,3],.structural 40 [2],.structural 40 [2],.unresolved].get

def outerCone : ConeWire 4 3 :=
  ⟨#v[0,1,2],#v[.structural 30 [1],.structural 40 [2],.structural 40 [2]],0⟩

def fieldCone : ConeWire 4 2 :=
  ⟨#v[1,2],#v[.structural 40 [1],.structural 40 [1]],0⟩

def outerPartition : Wire 3 2 :=
  ⟨#v[0,1,1],#v[.structural 30 [1],.structural 40 [1]]⟩

def fieldPartition : Wire 2 1 := ⟨#v[0,0],#v[.structural 40 [0]]⟩

theorem unvisited_unknown_does_not_hide_real_safe_or_cyclic_results :
    replayCone ambient 0 outerCone outerPartition = some false ∧
    replayCone ambient 1 fieldCone fieldPartition = some true ∧
    replayCone impeded 0 outerCone outerPartition = none := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

/-- info: [some false, some true, none, some true, none] -/
#guard_msgs in
#eval [replayCone ambient 0 outerCone outerPartition,
  replayCone ambient 1 fieldCone fieldPartition,
  replayCone impeded 0 outerCone outerPartition,
  replayCone impeded 1 fieldCone fieldPartition,
  replayCone ambient 0 fieldCone fieldPartition]

#print axioms checked_cone_exact
#print axioms cone_cycle_iff_ambient_at_the_actual_site
#print axioms a_checked_closed_cone_requires_only_actual_reachable_closure
#print axioms exact_finite_cone_replay_exists
#print axioms unvisited_unknown_does_not_hide_real_safe_or_cyclic_results
end Yulang.QuotientObservation471.ConeAudit
