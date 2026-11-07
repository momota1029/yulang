import Yulang.CommonOptionalBoundEncoding
import Yulang.CommonBoundMap
import Yulang.CommonPresenceVariableBounds

/-!
# Finite bound-reference indices and the actual shared-pool coalescer

An index contains only a bound reference and its syntactic membership in the
fixed query inventory. Its type contains no semantic model or residual law.
The finite inventory is explicit. Variable classification and every rigid
comparison commute with encoding into the actual extended source pool,
including when two symbolic references share the same constructor term.
-/

namespace Yulang.CommonBoundRefCoalescing

open PresenceOpenTailGenerationLowering (Pool)
open CommonOptionalPool (Query extend)
open CommonSymbolicBoundInspection (BoundRef)
open CommonSymbolicBoundSupport (Supported)
open LayerBoundTemplates (Constraint Problem)

variable {m : Nat}

abbrev Index (pool : Pool m) (queries : List (Query pool)) :=
  {reference : BoundRef (Fin pool.size) // Supported queries reference}

def references (pool : Pool m) (queries : List (Query pool)) : List (BoundRef (Fin pool.size)) :=
  (List.finRange pool.size).map BoundRef.original ++ [.top, .width, .exactEmpty] ++
    queries.flatMap (fun query => [.required query.1 query.2, .optional query.1 query.2])

theorem references_member (pool : Pool m) (queries : List (Query pool))
    (reference : BoundRef (Fin pool.size)) :
    reference ∈ references pool queries ↔ Supported queries reference := by
  cases reference <;> simp [references, Supported, List.mem_flatMap, List.mem_map]

def indices (pool : Pool m) (queries : List (Query pool)) : List (Index pool queries) :=
  (references pool queries).attach.map (fun reference =>
    ⟨reference.val, (references_member pool queries reference.val).mp reference.property⟩)

theorem index_member (pool : Pool m) (queries : List (Query pool)) (index : Index pool queries) :
    index ∈ indices pool queries := by
  have member := (references_member pool queries index.val).mpr index.property
  exact List.mem_map.mpr ⟨⟨index.val, member⟩, List.mem_attach _ _, rfl⟩

theorem indices_length (pool : Pool m) (queries : List (Query pool)) :
    (indices pool queries).length = pool.size + 3 + 2 * queries.length := by
  have length (entries : List (Query pool)) :
      (entries.flatMap (fun query =>
        [BoundRef.required query.1 query.2, .optional query.1 query.2])).length = 2 * entries.length := by
    induction entries with
    | nil => rfl
    | cons query rest ih =>
        simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil, ih]
        omega
  simp only [indices, List.length_map, List.length_attach, references, List.length_append,
    List.length_finRange, List.length_cons, List.length_nil, length]

abbrev Edge (pool : Pool m) (queries : List (Query pool)) := Index pool queries × Index pool queries

def inventory (pool : Pool m) (queries : List (Query pool)) : List (Edge pool queries) :=
  (indices pool queries).flatMap fun source => (indices pool queries).map fun target => (source, target)

theorem inventory_member (pool : Pool m) (queries : List (Query pool)) (edge : Edge pool queries) :
    edge ∈ inventory pool queries :=
  List.mem_flatMap.mpr ⟨edge.1, index_member pool queries edge.1,
    List.mem_map.mpr ⟨edge.2, index_member pool queries edge.2, rfl⟩⟩

theorem inventory_length (pool : Pool m) (queries : List (Query pool)) :
    (inventory pool queries).length = (pool.size + 3 + 2 * queries.length) ^ 2 := by
  have length (entries : List (Index pool queries)) :
      (entries.flatMap fun source =>
        (indices pool queries).map fun target => (source, target)).length =
        entries.length * (indices pool queries).length := by
    induction entries with
    | nil => simp
    | cons source rest ih => simp [List.flatMap_cons, ih, Nat.add_mul, Nat.add_comm]
  simpa only [inventory, indices_length, Nat.pow_two] using length (indices pool queries)

theorem generated_inventory_bound (pool : Pool m) :
    (inventory pool (CommonOptionalPoolQueries.queries pool)).length ≤ (5 * pool.size + 3) ^ 2 := by
  have queries := CommonOptionalPoolQueries.queries_length_le pool
  have count : pool.size + 3 + 2 * (CommonOptionalPoolQueries.queries pool).length ≤ 5 * pool.size + 3 := by
    omega
  rw [inventory_length, Nat.pow_two, Nat.pow_two]
  exact Nat.mul_le_mul count count

def original (pool : Pool m) (queries : List (Query pool)) (slot : Fin pool.size) : Index pool queries :=
  ⟨.original slot, trivial⟩

def encode (pool : Pool m) (queries : List (Query pool)) (index : Index pool queries) :
    Fin (extend pool queries).size :=
  CommonOptionalBoundEncoding.encode pool queries index.val index.property

def encodeEdge (pool : Pool m) (queries : List (Query pool)) (edge : Edge pool queries) :
    Fin (extend pool queries).size × Fin (extend pool queries).size :=
  (encode pool queries edge.1, encode pool queries edge.2)

def inputAt (pool : Pool m) (queries : List (Query pool)) (index : Index pool queries) : Option (Fin m) :=
  match index.val with
  | .original slot => CommonPresenceVariableBounds.inputAt pool slot
  | _ => none

theorem inputAt_encode (pool : Pool m) (queries : List (Query pool)) (index : Index pool queries) :
    CommonPresenceVariableBounds.inputAt (extend pool queries) (encode pool queries index) =
      inputAt pool queries index := by
  rcases index with ⟨reference, supported⟩
  cases reference <;> simp only [encode, CommonPresenceVariableBounds.inputAt,
    CommonOptionalBoundEncoding.termAt_encode, CommonOptionalBoundEncoding.term, inputAt,
    CommonOptionalPool.requiredTerm, CommonOptionalPool.optionalTerm]

def classify (pool : Pool m) (queries : List (Query pool)) (edge : Edge pool queries) :
    Constraint m (Index pool queries) :=
  match inputAt pool queries edge.1, inputAt pool queries edge.2 with
  | some source, some target => .flow source target
  | none, some target => .lower edge.1 target
  | some source, none => .upper source edge.2
  | none, none => .check edge.1 edge.2

def template (pool : Pool m) (queries : List (Query pool)) (edges : List (Edge pool queries)) :
    Problem m (Index pool queries) := edges.map (classify pool queries)

theorem classify_encode (pool : Pool m) (queries : List (Query pool)) (edge : Edge pool queries) :
    CommonPresenceVariableBounds.classify (extend pool queries) (encodeEdge pool queries edge) =
      Constraint.map (encode pool queries) (classify pool queries edge) := by
  simp only [CommonPresenceVariableBounds.classify, encodeEdge, inputAt_encode, classify]
  cases inputAt pool queries edge.1 <;> cases inputAt pool queries edge.2 <;> rfl

theorem template_encode (pool : Pool m) (queries : List (Query pool)) (edges : List (Edge pool queries)) :
    CommonPresenceVariableBounds.template (extend pool queries) (edges.map (encodeEdge pool queries)) =
      LayerBoundTemplates.mapBounds (encode pool queries) (template pool queries edges) := by
  simp only [CommonPresenceVariableBounds.template, LayerBoundTemplates.mapBounds, template, List.map_map]
  congr 1
  funext edge
  exact classify_encode pool queries edge

def rigid (pool : Pool m) (queries : List (Query pool)) (edges : List (Edge pool queries)) :
    List (Edge pool queries) := CommonBoundCoalescing.rigidComparisons (template pool queries edges)

theorem rigid_encode (pool : Pool m) (queries : List (Query pool)) (edges : List (Edge pool queries)) :
    CommonBoundCoalescing.rigidComparisons
        (CommonPresenceVariableBounds.template (extend pool queries) (edges.map (encodeEdge pool queries))) =
      (rigid pool queries edges).map (encodeEdge pool queries) := by
  rw [template_encode, CommonBoundMap.rigidComparisons_map]
  rfl

/-- Shared original IDs are not changed by passing through the bounded
reference index or by variable propagation. -/
@[simp] theorem original_encode_val (pool : Pool m) (queries : List (Query pool)) (slot : Fin pool.size) :
    (encode pool queries (original pool queries slot)).val = slot.val :=
  CommonOptionalBoundEncoding.encode_original_val pool queries slot trivial

end Yulang.CommonBoundRefCoalescing
