import Yulang.CommonRoleIntervals
import Yulang.CommonDemandSolver

/-!
# Deferred lower-head requests at an actual constraint snapshot

This adapter reuses the existing demand-driven collector. Its independent
head evidence starts at an actual lower seed and follows actual variable-flow
edges. An upper bound alone cannot manufacture a lower head. The supplied
finite head projection remains an explicit parameter of this query component;
this is not a full role-head decoder or candidate resolver.
-/

namespace Yulang.CommonRoleDeferredBounds

open LayerBoundTemplates (Problem Reaches)
open CommonRoleIntervals (Interval Fits)

universe u v
variable {Bound : Type u} {Head : Type v} {n : Nat}

def interval (evaluate : Bound → Common.Ty) (problem : Problem n Bound) (node : Fin n) :
    Interval Common.Ty :=
  (DemandBoundPropagation.lower evaluate problem node,
    DemandBoundPropagation.upper evaluate problem node)

theorem interval_exact (evaluate : Bound → Common.Ty) (problem : Problem n Bound) (node : Fin n) :
    interval evaluate problem node =
      (CommonBoundCoalescing.lower evaluate problem node,
        CommonBoundCoalescing.upper evaluate problem node) := by
  simp only [interval, DemandBoundPropagation.lower_exact, DemandBoundPropagation.upper_exact]

theorem model_fits (evaluate : Bound → Common.Ty) (problem : Problem n Bound)
    (values : Fin n → Common.Ty) (model : CommonBoundCoalescing.Models evaluate problem values)
    (node : Fin n) : Fits (interval evaluate problem node) (values node) := by
  rw [interval_exact]
  exact ⟨CommonBoundCoalescing.lower_below model node,
    CommonBoundCoalescing.upper_above model node⟩

def lowerHeads (project : Bound → Option Head) (problem : Problem n Bound) (node : Fin n) :
    List Head :=
  (DemandBoundPropagation.request problem ⟨node, .lower⟩).filterMap project

/-- This relation does not call a bound collector or a candidate filter. -/
def HasLowerHead (project : Bound → Option Head) (problem : Problem n Bound)
    (node : Fin n) (head : Head) : Prop :=
  ∃ bound source, .lower bound source ∈ problem ∧ Reaches problem source node ∧
    project bound = some head

theorem lowerHeads_exact (project : Bound → Option Head) (problem : Problem n Bound)
    (node : Fin n) (head : Head) :
    head ∈ lowerHeads project problem node ↔ HasLowerHead project problem node head := by
  simp only [lowerHeads, DemandBoundPropagation.request, List.mem_filterMap,
    DemandBoundPropagation.lowerBounds_exact]
  constructor
  · rintro ⟨bound, member, projected⟩
    obtain ⟨source, seed, path⟩ :=
      (PresenceBoundCoalescing.mem_lowerBounds problem node bound).mp member
    exact ⟨bound, source, seed, path, projected⟩
  · rintro ⟨bound, source, seed, path, projected⟩
    exact ⟨bound, (PresenceBoundCoalescing.mem_lowerBounds problem node bound).mpr
      ⟨source, seed, path⟩, projected⟩

inductive Observation (Head : Type v) where
  | pending
  | known (first : Head) (rest : List Head)
  deriving Repr

def observe (project : Bound → Option Head) (problem : Problem n Bound) (node : Fin n) :
    Observation Head :=
  match lowerHeads project problem node with
  | [] => .pending
  | first :: rest => .known first rest

theorem pending_exact (project : Bound → Option Head) (problem : Problem n Bound) (node : Fin n) :
    observe project problem node = .pending ↔ ∀ head, ¬ HasLowerHead project problem node head := by
  constructor
  · intro pending head known
    have member := (lowerHeads_exact project problem node head).mpr known
    cases found : lowerHeads project problem node with
    | nil => rw [found] at member; cases member
    | cons first rest => simp [observe, found] at pending
  · intro unknown
    cases found : lowerHeads project problem node with
    | nil => simp [observe, found]
    | cons first rest =>
        exact False.elim (unknown first ((lowerHeads_exact project problem node first).mp
          (found ▸ List.mem_cons_self)))

theorem known_exact (project : Bound → Option Head) (problem : Problem n Bound)
    (node : Fin n) (first : Head) (rest : List Head) :
    observe project problem node = .known first rest ↔ lowerHeads project problem node = first :: rest := by
  cases found : lowerHeads project problem node <;> simp [observe, found]

theorem upper_only_pending (project : Bound → Option Head) (upper : Bound) :
    observe project ([.upper 0 upper] : Problem 1 Bound) 0 = .pending := by
  rfl

theorem lower_arrives (project : Bound → Option Head) (lower upper : Bound) (head : Head)
    (projected : project lower = some head) :
    observe project ([.lower lower 0, .upper 0 upper] : Problem 1 Bound) 0 = .known head [] := by
  simp [observe, lowerHeads, DemandBoundPropagation.request,
    DemandBoundPropagation.lowerBounds_exact, LayerBoundTemplates.lowerBounds,
    LayerBoundTemplates.lowerSeeds, LayerBoundTemplates.reachable,
    FiniteWorklist.reachable, FiniteWorklist.explore,
    FiniteWorklist.scan, projected]

end Yulang.CommonRoleDeferredBounds
