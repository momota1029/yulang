import Yulang.CommonNominalTypeFlow

/-!
# Clamped families for shared type flows with fixed lower and upper bounds

The family is finite type syntax: predecessor joins and successor meets clamp
unrestricted full Common parameters. Consistency compares only fixed bound
pairs connected by the finite graph. It is independent of all parameters.
This module proves the algebraic family theorem; a concrete bound-language
checker must discharge consistency before this becomes an executable solver.
-/

namespace Yulang.CommonNominalTypeBounds

open CommonNominalCarrier
open CommonNominalTypeFlow (Edge joinTypes join_types_below member_below_join)

structure Problem (slots : Nat) where
  edges : List (Edge slots)
  lower : List (Fin slots × Ty)
  upper : List (Fin slots × Ty)

def Models (problem : Problem slots) (values : Fin slots → Ty) : Prop :=
  CommonNominalTypeFlow.Models problem.edges values ∧
    (∀ bound ∈ problem.lower, CommonNominalCarrier.Subtype bound.2 (values bound.1)) ∧
    ∀ bound ∈ problem.upper, CommonNominalCarrier.Subtype (values bound.1) bound.2

def Consistent (problem : Problem slots) : Prop :=
  ∀ lower ∈ problem.lower, ∀ upper ∈ problem.upper,
    CastGraph.Path problem.edges lower.1 upper.1 → CommonNominalCarrier.Subtype lower.2 upper.2

theorem type_below_top (type : Ty) : CommonNominalCarrier.Subtype type .top := by
  intro depth
  change CommonNominalFinite.ProducerLe Common.rowLe (observeTy depth type) .top
  apply CommonNominalFinite.producerLe_iff_probe _ _ |>.mpr
  intro rank environment observation accepted
  cases observation
  case trivial => exact CommonNominalFinite.probeAt_trivial _ _
  all_goals cases rank <;> simp [CommonNominalFinite.ProbeAt, CommonNominalFinite.ProbeStep,
    CommonNominalFinite.MaskedProbeStep] at accepted

def meetTypes : List Ty → Ty
  | [] => .top
  | first :: rest => .inter first (meetTypes rest)

theorem below_meet_types (types : List Ty) (source : Ty) :
    CommonNominalCarrier.Subtype source (meetTypes types) ↔
      ∀ type ∈ types, CommonNominalCarrier.Subtype source type := by
  induction types with
  | nil => exact ⟨by simp, fun _ => type_below_top source⟩
  | cons first rest ih => simp only [meetTypes, common_inter_is_meet, ih, List.forall_mem_cons]

theorem meet_below_member (types : List Ty) (type : Ty) (present : type ∈ types) :
    CommonNominalCarrier.Subtype (meetTypes types) type :=
  (below_meet_types types (meetTypes types)).mp (subtype_refl _) type present

def lowerAt (problem : Problem slots) (index : Fin slots) : List Ty :=
  (problem.lower.filter fun bound => CastGraph.reachable problem.edges bound.1 index).map Prod.snd

def upperAt (problem : Problem slots) (index : Fin slots) : List Ty :=
  (problem.upper.filter fun bound => CastGraph.reachable problem.edges index bound.1).map Prod.snd

private theorem refl_path (edges : List (Edge slots)) (index : Fin slots) : CastGraph.Path edges index index :=
  .seed (by simp)

private theorem edge_path (edges : List (Edge slots)) (edge : Edge slots) (member : edge ∈ edges) :
    CastGraph.Path edges edge.1 edge.2 :=
  .step (refl_path edges edge.1) ((CastGraph.mem_adjacency _ _ _).mpr member)

theorem lower_mono (problem : Problem slots) (edge : Edge slots) (member : edge ∈ problem.edges) :
    CommonNominalCarrier.Subtype (joinTypes (lowerAt problem edge.1)) (joinTypes (lowerAt problem edge.2)) := by
  apply (join_types_below _ _).mpr
  intro type present
  obtain ⟨bound, selected, rfl⟩ := List.mem_map.mp present
  obtain ⟨original, reached⟩ := List.mem_filter.mp selected
  have next := FiniteReachability.Reach.append ((CastGraph.reachable_exact _ _ _).mp reached)
    (edge_path problem.edges edge member)
  exact member_below_join _ _ (List.mem_map.mpr ⟨bound,
    List.mem_filter.mpr ⟨original, (CastGraph.reachable_exact _ _ _).mpr next⟩, rfl⟩)

theorem upper_mono (problem : Problem slots) (edge : Edge slots) (member : edge ∈ problem.edges) :
    CommonNominalCarrier.Subtype (meetTypes (upperAt problem edge.1)) (meetTypes (upperAt problem edge.2)) := by
  apply (below_meet_types _ _).mpr
  intro type present
  obtain ⟨bound, selected, rfl⟩ := List.mem_map.mp present
  obtain ⟨original, reached⟩ := List.mem_filter.mp selected
  have before := FiniteReachability.Reach.append (edge_path problem.edges edge member)
    ((CastGraph.reachable_exact _ _ _).mp reached)
  exact meet_below_member _ _ (List.mem_map.mpr ⟨bound,
    List.mem_filter.mpr ⟨original, (CastGraph.reachable_exact _ _ _).mpr before⟩, rfl⟩)

def instantiate (problem : Problem slots) (parameters : Fin slots → Ty) (index : Fin slots) : Ty :=
  .union (joinTypes (lowerAt problem index))
    (.inter (CommonNominalTypeFlow.instantiate problem.edges parameters index) (meetTypes (upperAt problem index)))

private theorem union_left (first last : Ty) : CommonNominalCarrier.Subtype first (.union first last) :=
  (common_union_is_join _ _ _).mp (subtype_refl _) |>.1
private theorem union_right (first last : Ty) : CommonNominalCarrier.Subtype last (.union first last) :=
  (common_union_is_join _ _ _).mp (subtype_refl _) |>.2
private theorem inter_left (first last : Ty) : CommonNominalCarrier.Subtype (.inter first last) first :=
  (common_inter_is_meet _ _ _).mp (subtype_refl _) |>.1
private theorem inter_right (first last : Ty) : CommonNominalCarrier.Subtype (.inter first last) last :=
  (common_inter_is_meet _ _ _).mp (subtype_refl _) |>.2

/-- The only premise compares finite fixed bounds, never parameters. -/
theorem all_parameters_models (problem : Problem slots) (consistent : Consistent problem) (parameters : Fin slots → Ty) :
    Models problem (instantiate problem parameters) := by
  refine ⟨?_, ?_, ?_⟩
  · intro edge present
    exact common_union_mono (lower_mono problem edge present)
      (common_inter_mono (CommonNominalTypeFlow.all_parameters_models problem.edges parameters edge present)
        (upper_mono problem edge present))
  · intro bound present
    have seeded : bound.2 ∈ lowerAt problem bound.1 := List.mem_map.mpr
      ⟨bound, List.mem_filter.mpr ⟨present, (CastGraph.reachable_exact _ _ _).mpr (refl_path _ _)⟩, rfl⟩
    exact subtype_trans (member_below_join _ _ seeded) (union_left _ _)
  · intro bound present
    apply (common_union_is_join _ _ _).mpr
    constructor
    · apply (join_types_below _ _).mpr
      intro type included
      obtain ⟨lower, selected, rfl⟩ := List.mem_map.mp included
      obtain ⟨original, reached⟩ := List.mem_filter.mp selected
      exact consistent lower original bound present ((CastGraph.reachable_exact _ _ _).mp reached)
    · exact subtype_trans (inter_right _ _) (meet_below_member _ _ (List.mem_map.mpr
        ⟨bound, List.mem_filter.mpr ⟨present, (CastGraph.reachable_exact _ _ _).mpr (refl_path _ _)⟩, rfl⟩))

theorem models_consistent (problem : Problem slots) (values : Fin slots → Ty) (models : Models problem values) :
    Consistent problem := by
  intro lower lowerMember upper upperMember path
  exact subtype_trans (models.2.1 lower lowerMember)
    (subtype_trans (CommonNominalTypeFlow.path_below problem.edges values models.1 _ _ path)
      (models.2.2 upper upperMember))

theorem model_retraction (problem : Problem slots) (values : Fin slots → Ty) (models : Models problem values) :
    ∀ index, Equivalent (instantiate problem values index) (values index) := by
  intro index
  have flowSame := CommonNominalTypeFlow.model_retraction problem.edges values models.1 index
  constructor
  · apply (common_union_is_join _ _ _).mpr
    constructor
    · apply (join_types_below _ _).mpr
      intro type present
      obtain ⟨lower, selected, rfl⟩ := List.mem_map.mp present
      obtain ⟨original, reached⟩ := List.mem_filter.mp selected
      exact subtype_trans (models.2.1 lower original)
        (CommonNominalTypeFlow.path_below problem.edges values models.1 _ _ ((CastGraph.reachable_exact _ _ _).mp reached))
    · exact subtype_trans (inter_left _ _) flowSame.1
  · apply subtype_trans ((common_inter_is_meet _ _ _).mpr ⟨flowSame.2, ?_⟩) (union_right _ _)
    apply (below_meet_types _ _).mpr
    intro type present
    obtain ⟨upper, selected, rfl⟩ := List.mem_map.mp present
    obtain ⟨original, reached⟩ := List.mem_filter.mp selected
    exact subtype_trans
      (CommonNominalTypeFlow.path_below problem.edges values models.1 _ _ ((CastGraph.reachable_exact _ _ _).mp reached))
      (models.2.2 upper original)

theorem models_of_recovered (problem : Problem slots) (consistent : Consistent problem)
    (parameters values : Fin slots → Ty)
    (recovered : ∀ index, Equivalent (instantiate problem parameters index) (values index)) : Models problem values := by
  have sound := all_parameters_models problem consistent parameters
  refine ⟨?_, ?_, ?_⟩
  · intro edge present
    exact subtype_trans (recovered edge.1).2 (subtype_trans (sound.1 edge present) (recovered edge.2).1)
  · intro bound present
    exact subtype_trans (sound.2.1 bound present) (recovered bound.1).1
  · intro bound present
    exact subtype_trans (recovered bound.1).2 (sound.2.2 bound present)

end Yulang.CommonNominalTypeBounds
