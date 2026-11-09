import Yulang.CommonRoleCorrelatedPaths

/-! Observation-independent finite ancestry carrier. Active histories at every
future state/mask are retained, without choosing a language branch policy. -/
namespace Yulang.CommonRoleCorrelatedCarrier
open CommonRoleSettledSyntax CommonRoleOpenProducer CommonRoleMaterializedDomain
open CommonRoleSourceWorklist (Node nodes nodes_complete)
open CommonRoleSettledConstraints (State)
open CommonRoleCorrelatedPaths (History Route Path start extend)
open CommonRoleSourceTemplateClosure (declarationChildren)
open CommonRoleChildTemplates (sourceWeight)

variable (registry : Registry) (root : SourceRequest n)

def children (r : Route registry root) : List (Route registry root) :=
  registry.declarations.flatMap fun d =>
    ((nodes registry root).filter fun c =>
      c.val ∈ declarationChildren d r.2.val ∧ sourceWeight c.val < sourceWeight r.2.val).map
      (extend registry root r d)

def pathsUpTo : Nat → List (Route registry root)
  | 0 => [start registry root]
  | k + 1 => start registry root :: (pathsUpTo k).flatMap (children registry root)

def carrier : List (Route registry root) := pathsUpTo registry root (sourceWeight root)

/-- Every active edge is present before any state or branch mask is supplied. -/
theorem active_child_retained
    (mask : History registry root → Node registry root → Declaration → Bool)
    (observation : State n) (r t : Route registry root)
    (member : t ∈ CommonRoleCorrelatedPaths.children registry root mask observation r) :
    t ∈ children registry root r := by
  obtain ⟨d, hd, c, _, hh, hc, rfl⟩ :=
    (CommonRoleCorrelatedPaths.children_exact registry root mask observation r t).mp member
  have dec := CommonRoleGuardedCandidates.candidate_decreases registry d hd observation r.2.val c.val
    ((CommonRoleGuardedEquations.candidate_children_exact observation r.2.val c.val d).mpr ⟨hh,hc⟩)
  refine List.mem_flatMap.mpr ⟨d, hd, List.mem_map.mpr ⟨c, ?_, rfl⟩⟩
  exact List.mem_filter.mpr ⟨nodes_complete .., by simpa using And.intro hc dec⟩

theorem pathsUpTo_retained
    (mask : History registry root → Node registry root → Declaration → Bool)
    (observation : State n) (fuel : Nat) (r : Route registry root)
    (member : r ∈ CommonRoleCorrelatedPaths.pathsUpTo registry root mask observation fuel) :
    r ∈ pathsUpTo registry root fuel := by
  induction fuel generalizing r with
  | zero => exact member
  | succ k ih =>
    rcases List.mem_cons.mp member with eq | member
    · exact List.mem_cons.mpr (Or.inl eq)
    · obtain ⟨p, hp, hr⟩ := List.mem_flatMap.mp member
      exact List.mem_cons.mpr (Or.inr (List.mem_flatMap.mpr
        ⟨p, ih p hp, active_child_retained registry root mask observation p r hr⟩))

/-- One fixed finite carrier contains independently derivable routes at every
observation and history-sensitive mask, including routes disabled previously. -/
theorem path_retained
    (mask : History registry root → Node registry root → Declaration → Bool)
    (observation : State n) (r : Route registry root)
    (path : Path registry root mask observation r) :
    r ∈ carrier registry root :=
  pathsUpTo_retained registry root mask observation _ r
    ((CommonRoleCorrelatedPaths.collect_exact registry root mask observation r).mpr path)

end Yulang.CommonRoleCorrelatedCarrier
