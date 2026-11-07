import Yulang.CommonNominalClampedGraphFamily
import Yulang.CommonNominalFiniteRigidInspection

/-!
# Finite-observation reduction of clamped lower edges

For an arbitrary mixed pool, flexible-source edges hold outright. A rigid
source's remaining edges reduce at a fixed constructor depth to its reachable
rigid targets. The source is unchanged by this propagation. This is an
internal finite-depth lemma, not a consistency condition on free parameters.
-/

namespace Yulang.CommonNominalClampedFiniteEdges

open CommonNominalCarrier
open CommonNominalClampedGraphFamily
open CommonNominalTypeFlow (Edge joinTypes)
open CommonNominalTypeBounds (meetTypes)
open CommonNominalFiniteRigidInspection (BelowAt)

theorem path_mono {first last : List (Edge nodes)} (subset : first ⊆ last)
    (source target : Fin nodes) (path : CastGraph.Path first source target) :
    CastGraph.Path last source target := by
  apply FiniteReachability.Reach.mono (fun _ member => member) ?_ path
  intro origin destination member
  exact (CastGraph.mem_adjacency _ _ _).mpr (subset ((CastGraph.mem_adjacency _ _ _).mp member))

theorem edge_path (edges : List (Edge nodes)) (edge : Edge nodes) (member : edge ∈ edges) :
    CastGraph.Path edges edge.1 edge.2 :=
  .step (.seed (by simp)) ((CastGraph.mem_adjacency _ _ _).mpr member)

theorem meet_at_iff (depth : Nat) (source : Ty) (types : List Ty) :
    BelowAt depth source (meetTypes types) ↔ ∀ target ∈ types, BelowAt depth source target := by
  induction types with
  | nil =>
      simp only [List.not_mem_nil, false_implies, implies_true]
      exact iff_true_intro (CommonNominalTypeBounds.type_below_top source depth)
  | cons target rest ih =>
      change CommonNominalFinite.ProducerLe _ _ (.inter _ _) ↔ _
      rw [CommonNominalFinite.producerLe_inter_iff]
      change (BelowAt depth source target ∧ BelowAt depth source (meetTypes rest)) ↔ _
      simp only [List.forall_mem_cons]
      exact and_congr_right (fun _ => ih)

/-- Finite lower-edge soundness needs only same-source reachable rigid
comparisons. Its proof does not assume any full-depth rigid subtype edge. -/
theorem edge_at_of_rigid_source (depth : Nat) (pool : Pool nodes labels rows)
    (edges : List (Edge nodes)) (rowValues : Fin rows → Row) (parameters values : Fin nodes → Ty)
    (model : CommonNominalPresenceTailRegular.Models (clampedGraph pool edges rowValues parameters) values)
    (edge : Edge nodes) (member : edge ∈ edges)
    (rigidSource : ∀ target, pool.definition target ≠ none → CastGraph.Path edges edge.1 target →
      BelowAt depth (values edge.1) (values target)) :
    BelowAt depth (values edge.1) (values edge.2) := by
  cases source : pool.definition edge.1 with
  | none => exact flexible_source_below pool edges rowValues parameters values model edge member source depth
  | some sourceBody =>
      cases target : pool.definition edge.2 with
      | some targetBody => exact rigidSource edge.2 (by simp [target]) (edge_path edges edge member)
      | none =>
          have pointer : (edge.2, edge.1) ∈ lowerPointers pool edges := List.mem_map.mpr
            ⟨edge, List.mem_filter.mpr ⟨member, by simp [flexible, source, target]⟩, rfl⟩
          have bound : (edge.2, values edge.1) ∈ (bounds pool edges values).lower :=
            List.mem_map.mpr ⟨(edge.2, edge.1), pointer, rfl⟩
          have lowerIncluded : values edge.1 ∈ CommonNominalTypeBounds.lowerAt (bounds pool edges values) edge.2 :=
            List.mem_map.mpr ⟨(edge.2, values edge.1), List.mem_filter.mpr
              ⟨bound, (CastGraph.reachable_exact _ _ _).mpr (.seed (by simp))⟩, rfl⟩
          have lowerBelow : Subtype (values edge.1)
              (CommonNominalTypeBounds.instantiate (bounds pool edges values) parameters edge.2) :=
            subtype_trans (CommonNominalTypeFlow.member_below_join _ _ lowerIncluded)
              ((common_union_is_join _ _ _).mp (subtype_refl _) |>.1)
          have upperBelow : BelowAt depth (values edge.1)
              (meetTypes (CommonNominalTypeBounds.upperAt (bounds pool edges values) edge.2)) := by
            apply (meet_at_iff depth _ _).mpr
            rw [upper_at_exact]
            intro type included
            obtain ⟨targetIndex, selectedTarget, rfl⟩ := List.mem_map.mp included
            obtain ⟨upperPointer, selectedPointer, targetSame⟩ := List.mem_map.mp selectedTarget
            obtain ⟨originalPointer, reached⟩ := List.mem_filter.mp selectedPointer
            have upperEdge := (List.mem_filter.mp originalPointer).1
            have targetRigid : pool.definition upperPointer.2 ≠ none := by
              have selected := (List.mem_filter.mp originalPointer).2
              cases found : pool.definition upperPointer.2
              · simp [flexible, found] at selected
              · simp
            have flowPath := path_mono
              (fun edge present => (List.mem_filter.mp present).1 : flows pool edges ⊆ edges) _ _
              ((CastGraph.reachable_exact _ _ _).mp reached)
            have wholePath := FiniteReachability.Reach.append (edge_path edges edge member)
              (FiniteReachability.Reach.append flowPath (edge_path edges upperPointer upperEdge))
            subst targetIndex
            exact rigidSource upperPointer.2 targetRigid wholePath
          have expanded := flexible_clamped pool edges rowValues parameters values model edge.2 target
          exact CommonNominalFinite.producerLe_trans
            ((CommonNominalFinite.producerLe_inter_iff _ _ _).mpr ⟨lowerBelow depth, upperBelow⟩)
            (expanded.1 depth)

end Yulang.CommonNominalClampedFiniteEdges
