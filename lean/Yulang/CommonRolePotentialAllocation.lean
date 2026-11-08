import Yulang.CommonRolePotentialChildClosure
import Yulang.CommonRoleOpenPropagationOrigin
import Yulang.CommonRoleOpenRecursivePass
import Yulang.CommonRoleOpenPassStability

/-! Computed syntactic-Ty slots for the all-candidate finite structural closure.
This does not identify distinct source variables represented by unknown Ty,
and is not an allocator for the not-yet-constructed narrowing/saturation graph. -/
namespace Yulang.CommonRolePotentialAllocation
open CommonRoleSettledSyntax (Ty Declaration)
open CommonRoleOpenProducer (Registry Request production)
open CommonRolePotentialChildClosure (closure Reach)
open CommonRoleOpenProducerAccess
open CommonRoleSettledConstraints (State)
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All)

def requestTypes (registry : Registry) (q : Request) : List Ty :=
  [q.lower, q.upper] ++
    (CommonRoleOpenProducer.hits (CommonRoleOpenProducer.scan q.role q.lower q.upper
      registry.declarations)).flatMap (fun hit => [hit.2.1, hit.2.2])

/-- Root endpoints guarantee a usable default slot even for an empty capture set. -/
def table (registry : Registry) (root : Request) : List Ty :=
  root.lower :: root.upper :: (closure registry root).flatMap (requestTypes registry)

theorem table_nonempty (registry : Registry) (root : Request) :
    0 < (table registry root).length := by simp [table]

def allocate (registry : Registry) (root : Request) (type : Ty) :
    Fin (table registry root).length :=
  if member : type ∈ table registry root then
    ⟨(table registry root).idxOf type, List.idxOf_lt_length_of_mem member⟩
  else ⟨0, table_nonempty registry root⟩

def decode (registry : Registry) (root : Request)
    (slot : Fin (table registry root).length) : Ty :=
  (table registry root)[slot.val]

/-- No default is used for any syntactic type actually in the computed table. -/
theorem decode_allocate (registry : Registry) (root : Request) (type : Ty)
    (member : type ∈ table registry root) :
    decode registry root (allocate registry root type) = type := by
  simp only [allocate, dite_eq_left member, decode]
  exact List.getElem_idxOf (List.idxOf_lt_length_of_mem member)

theorem allocate_injective_on_table (registry : Registry) (root : Request) (left right : Ty)
    (leftMember : left ∈ table registry root) (rightMember : right ∈ table registry root)
    (same : allocate registry root left = allocate registry root right) : left = right := by
  have decoded := congrArg (decode registry root) same
  simpa only [decode_allocate registry root left leftMember,
    decode_allocate registry root right rightMember] using decoded

theorem request_types_present (registry : Registry) (root q : Request)
    (reachable : Reach registry root q) (type : Ty) (member : type ∈ requestTypes registry q) :
    type ∈ table registry root := by
  apply List.mem_cons_of_mem
  apply List.mem_cons_of_mem
  exact List.mem_flatMap.mpr ⟨q, CommonRolePotentialChildClosure.closure_complete registry root q reachable, member⟩

theorem request_endpoints_present (registry : Registry) (root q : Request)
    (reachable : Reach registry root q) :
    q.lower ∈ table registry root ∧ q.upper ∈ table registry root := by
  constructor
  · exact request_types_present registry root q reachable _ (by simp [requestTypes])
  · exact request_types_present registry root q reachable _ (by simp [requestTypes])

/-- A hit of any filtered candidate list is a hit of the original registry. -/
theorem filtered_hit_present (registry : Registry) (visible : List Declaration)
    (subset : ∀ d ∈ visible, d ∈ registry.declarations) (q : Request)
    (d : Declaration) (lower upper : Ty)
    (hit : (d, lower, upper) ∈ CommonRoleOpenProducer.hits
      (CommonRoleOpenProducer.scan q.role q.lower q.upper visible)) :
    (d, lower, upper) ∈ CommonRoleOpenProducer.hits
      (CommonRoleOpenProducer.scan q.role q.lower q.upper registry.declarations) := by
  obtain ⟨member, same, low, high⟩ := scan_hit_origin _ _ _ _ d lower upper
    ((mem_hits _ d lower upper).mp hit)
  exact (mem_hits _ d lower upper).mpr
    (CommonRolePotentialChildClosure.scan_hit_complete _ _ _ _ d lower upper
      (subset d member) same low high)

/-- Covers the real producer for every declaration subset, not only the unfiltered head. -/
theorem production_payloads_present (registry : Registry) (visible : List Declaration)
    (subset : ∀ d ∈ visible, d ∈ registry.declarations) (root q : Request)
    (reachable : Reach registry root q) (d : Declaration) (lower upper : Ty)
    (produced : production visible q = some (d, lower, upper)) :
    lower ∈ table registry root ∧ upper ∈ table registry root := by
  have hit : (d, lower, upper) ∈ CommonRoleOpenProducer.hits
      (CommonRoleOpenProducer.scan q.role q.lower q.upper visible) := by
    unfold production at produced
    cases hs : CommonRoleOpenProducer.hits
      (CommonRoleOpenProducer.scan q.role q.lower q.upper visible) with
    | nil => simp [hs] at produced
    | cons first rest =>
      have equal : first = (d, lower, upper) := by simpa [hs] using produced
      simp [equal]
  have full := filtered_hit_present registry visible subset q d lower upper hit
  constructor
  · apply request_types_present registry root q reachable
    apply List.mem_append_right
    exact List.mem_flatMap.mpr ⟨(d, lower, upper), full, by simp⟩
  · apply request_types_present registry root q reachable
    apply List.mem_append_right
    exact List.mem_flatMap.mpr ⟨(d, lower, upper), full, by simp⟩

def assignment (registry : Registry) (root : Request) (interpret : Ty → α) :
    Fin (table registry root).length → α := fun slot => interpret (decode registry root slot)

theorem assignment_preserved (registry : Registry) (root : Request) (interpret : Ty → α)
    (type : Ty) (member : type ∈ table registry root) :
    assignment registry root interpret (allocate registry root type) = interpret type := by
  simp [assignment, decode_allocate registry root type member]

/-- Filtering can change the selected declaration without changing the allocator.
Exactness compares the original actual payload meanings, for any interpretation. -/
theorem filtered_prepare_exact (registry : Registry) (visible : List Declaration)
    (subset : ∀ d ∈ visible, d ∈ registry.declarations) (root q : Request)
    (reachable : Reach registry root q) (key : Nat) (cs : List Request)
    (selected : CommonRoleOpenProducer.Local visible q (.selected key cs))
    (s : State (table registry root).length) (interpret : Ty → Comp Common.model) :
    ∃ d lower upper,
      production visible q = some (d, lower, upper) ∧ key = d.key ∧
      cs = CommonRoleOpenProducer.children q d lower upper ∧
      (All Common.model (assignment registry root interpret)
        (CommonRoleOpenPropagation.prepare visible (allocate registry root) q s).atoms ↔
       All Common.model (assignment registry root interpret) s.atoms ∧
        (d.head.names = [] ∨ Common.Subtype (interpret lower).1 (interpret upper).1)) := by
  obtain ⟨d, lower, upper, produced, sameKey, sameChildren, exactness⟩ :=
    CommonRoleOpenPropagationOrigin.selected_prepare_exact visible
      (allocate registry root) q key cs s selected
  obtain ⟨low, up⟩ := production_payloads_present registry visible subset root q reachable
    d lower upper produced
  refine ⟨d, lower, upper, produced, sameKey, sameChildren, ?_⟩
  simpa only [assignment_preserved registry root interpret lower low,
    assignment_preserved registry root interpret upper up] using exactness (assignment registry root interpret)

/-- Every child of the actual state-gated producer over any candidate subset
retains both endpoint syntaxes in the one original finite table. -/
theorem filtered_state_child_endpoints (registry : Registry) (visible : List Declaration)
    (subset : ∀ d ∈ visible, d ∈ registry.declarations) (root q child : Request)
    (reachable : Reach registry root q) (s : State (table registry root).length)
    (member : child ∈ CommonRoleOpenPropagation.childList
      (CommonRoleOpenPropagation.produce visible (allocate registry root) q s)) :
    decode registry root (allocate registry root child.lower) = child.lower ∧
    decode registry root (allocate registry root child.upper) = child.upper := by
  have childMember := CommonRolePotentialChildClosure.filtered_children_closed
    registry visible subset root q child
    (CommonRolePotentialChildClosure.closure_complete registry root q reachable)
    (CommonRoleOpenRecursivePass.child_origin visible (allocate registry root) q s child member)
  have childReach := CommonRolePotentialChildClosure.closure_sound registry root child childMember
  obtain ⟨low, up⟩ := request_endpoints_present registry root child childReach
  exact ⟨decode_allocate registry root child.lower low,
    decode_allocate registry root child.upper up⟩

end Yulang.CommonRolePotentialAllocation
