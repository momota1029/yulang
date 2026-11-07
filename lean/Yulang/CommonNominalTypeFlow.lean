import Yulang.CommonNominalConstructors
import Yulang.CastGraph

/-!
# Unrestricted families for shared Common type-flow inequalities

Finite directed slot inequalities are solved by joining every predecessor's
unrestricted type parameter. Parameters range over the full new regular
carrier, including arbitrary nested nominal arguments. The static graph is
used to compute joins, never as a residual predicate on those parameters.
Constructor equations and bounds to constructed nodes are separate problems.
-/

namespace Yulang.CommonNominalTypeFlow

open CommonNominalCarrier

abbrev Edge (slots : Nat) := Fin slots × Fin slots
abbrev Problem (slots : Nat) := List (Edge slots)

def Models (problem : Problem slots) (values : Fin slots → Ty) : Prop :=
  ∀ edge ∈ problem, CommonNominalCarrier.Subtype (values edge.1) (values edge.2)

theorem bottom_below (type : Ty) : CommonNominalCarrier.Subtype .bottom type := by
  intro depth
  apply CommonNominalFinite.producerLe_iff_probe _ _ |>.mpr
  intro rank environment observation _
  exact CommonNominalFinite.probeAt_bottom rank observation

def joinTypes : List Ty → Ty
  | [] => .bottom
  | first :: rest => .union first (joinTypes rest)

theorem join_types_below (types : List Ty) (target : Ty) :
    CommonNominalCarrier.Subtype (joinTypes types) target ↔
      ∀ type ∈ types, CommonNominalCarrier.Subtype type target := by
  induction types with
  | nil => exact ⟨by simp, fun _ => bottom_below target⟩
  | cons first rest ih => simp only [joinTypes, common_union_is_join, ih, List.forall_mem_cons]

theorem member_below_join (types : List Ty) (type : Ty) (present : type ∈ types) :
    CommonNominalCarrier.Subtype type (joinTypes types) :=
  (join_types_below types (joinTypes types)).mp (subtype_refl _) type present

def predecessors (problem : Problem slots) (index : Fin slots) : List (Fin slots) :=
  (List.finRange slots).filter fun origin => CastGraph.reachable problem origin index

theorem mem_predecessors (problem : Problem slots) (origin index : Fin slots) :
    origin ∈ predecessors problem index ↔ CastGraph.Path problem origin index := by
  simp only [predecessors, List.mem_filter, List.mem_finRange, true_and, CastGraph.reachable_exact]

def instantiate (problem : Problem slots) (parameters : Fin slots → Ty) (index : Fin slots) : Ty :=
  joinTypes ((predecessors problem index).map parameters)

theorem all_parameters_models (problem : Problem slots) (parameters : Fin slots → Ty) :
    Models problem (instantiate problem parameters) := by
  intro edge present
  apply (join_types_below _ _).mpr
  intro type member
  obtain ⟨origin, before, rfl⟩ := List.mem_map.mp member
  have path := (mem_predecessors problem origin edge.1).mp before
  have after : origin ∈ predecessors problem edge.2 :=
    (mem_predecessors problem origin edge.2).mpr
      (.step path ((CastGraph.mem_adjacency problem edge.1 edge.2).mpr present))
  exact member_below_join _ _ (List.mem_map.mpr ⟨origin, after, rfl⟩)

theorem path_below (problem : Problem slots) (values : Fin slots → Ty) (models : Models problem values)
    (source target : Fin slots) (path : CastGraph.Path problem source target) :
    CommonNominalCarrier.Subtype (values source) (values target) := by
  induction path with
  | seed present =>
      have same := List.mem_singleton.mp present
      subst same
      exact subtype_refl _
  | step _ edge ih => exact subtype_trans ih (models _ ((CastGraph.mem_adjacency _ _ _).mp edge))

/-- The original assignment itself supplies parameters. Every original
shared type, at every slot, is recovered modulo the full demand equivalence. -/
theorem model_retraction (problem : Problem slots) (values : Fin slots → Ty) (models : Models problem values) :
    ∀ index, Equivalent (instantiate problem values index) (values index) := by
  intro index
  constructor
  · apply (join_types_below _ _).mpr
    intro type present
    obtain ⟨origin, member, rfl⟩ := List.mem_map.mp present
    exact path_below problem values models origin index ((mem_predecessors problem origin index).mp member)
  · apply member_below_join
    apply List.mem_map.mpr
    exact ⟨index, (mem_predecessors problem index index).mpr (.seed (by simp)), rfl⟩

theorem models_of_recovered (problem : Problem slots) (parameters values : Fin slots → Ty)
    (recovered : ∀ index, Equivalent (instantiate problem parameters index) (values index)) : Models problem values := by
  have sound := all_parameters_models problem parameters
  intro edge present
  exact subtype_trans (recovered edge.1).2 (subtype_trans (sound edge present) (recovered edge.2).1)

theorem solve_all_instances_exact (problem : Problem slots) (values : Fin slots → Ty) :
    Models problem values ↔ ∃ parameters : Fin slots → Ty,
      ∀ index, Equivalent (instantiate problem parameters index) (values index) :=
  ⟨fun models => ⟨values, model_retraction problem values models⟩,
    fun ⟨parameters, recovered⟩ => models_of_recovered problem parameters values recovered⟩

end Yulang.CommonNominalTypeFlow
