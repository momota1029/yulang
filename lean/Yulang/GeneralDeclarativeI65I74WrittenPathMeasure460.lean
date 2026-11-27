import Yulang.GeneralDeclarativeI65I74CompiledTrailDecomposition460

namespace Yulang.GeneralDeclarativeI65.I72.WrittenPattern460
open RecordTraversal455.MixedQA (MixedPath)

mutual
  def nodes : Term → Nat
    | .var _ => 1
    | .app _ as => nodesArgs as + 1
    | .record _ p t => nodes p + nodes t + 1
    | .variant _ p => nodes p + 1
    | .join a b => nodes a + nodes b + 1
  def nodesArgs : Args → Nat
    | .nil => 0
    | .cons t as => nodes t + nodesArgs as
end

theorem all_terms_have_at_least_their_root (t : Term) : 0 < nodes t := by
  cases t <;> simp [nodes]

theorem chosen_field_is_proper_source_descendant {label t next}
    (choose : FirstField label t next) : nodes next < nodes t := by
  induction choose with
  | here =>
    simp only [nodes]
    omega
  | later _ _ ih =>
    simp only [nodes]
    omega

theorem one_written_step_strictly_descends {keys t a u}
    (step : Step keys t a u) : nodes u < nodes t := by
  cases step with
  | field _ selected => exact chosen_field_is_proper_source_descendant selected
  | tag => simp [nodes]
  | pair0 _ | pair1 _ | point _ =>
    simp only [nodes,nodesArgs]
    omega

theorem every_written_walk_consumes_original_nodes {keys t path u}
    (found : Walk keys t path u) : path.length + nodes u ≤ nodes t := by
  induction found with
  | done => simp
  | next step _ ih =>
    have shrink := one_written_step_strictly_descends step
    simp only [List.length_cons]
    omega

theorem exact_graph_aligned_path_consumes_only_original_nodes {keys n t path terminal last}
    (found : CoordinateWalk keys n t path terminal last) :
    path.length + nodes last ≤ nodes t := by
  induction found with
  | stop => simp
  | down step _ ih =>
    have shrink := one_written_step_strictly_descends step
    simp only [List.length_cons]
    omega

/-- Finite path depth is bounded by the already-compiled selected source
tree, regardless of the raw graph. This is not solver termination. -/
theorem depth_is_structural_not_a_bound_on_the_raw_graph {s n t e path terminal last}
    (found : CompiledField s n t e path terminal last) :
    path.length < nodes t := by
  obtain ⟨⟨_,trace⟩,_,_⟩ := found
  have exact := exact_graph_aligned_path_consumes_only_original_nodes
    ((authored_trail_normal_form.mp trace).2.2)
  have positive := all_terms_have_at_least_their_root last
  omega

end Yulang.GeneralDeclarativeI65.I72.WrittenPattern460
