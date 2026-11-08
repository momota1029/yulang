import Yulang.CommonRoleOpenFiniteClosure
import Yulang.CommonRoleOpenPropagationOrigin
import Yulang.CommonRoleOpenRecursivePass
import Yulang.CommonRoleOpenPassStability

/-! Computed syntactic-Ty slots for the complete finite structural closure.
This does not identify distinct source variables represented by unknown Ty,
and is not an allocator for the not-yet-constructed narrowing/saturation graph. -/
namespace Yulang.CommonRoleOpenClosureAllocation
open CommonRoleSettledSyntax (Ty Declaration)
open CommonRoleOpenProducer (Registry Request production)
open CommonRoleOpenFiniteClosure (closure Reach)
open CommonRoleSettledConstraints (State)
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All)

def requestTypes (registry : Registry) (q : Request) : List Ty :=
  [q.lower, q.upper] ++ match production registry.declarations q with
    | none => []
    | some (_, lower, upper) => [lower, upper]

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
  exact List.mem_flatMap.mpr ⟨q, CommonRoleOpenFiniteClosure.closure_complete registry root q reachable, member⟩

theorem request_endpoints_present (registry : Registry) (root q : Request)
    (reachable : Reach registry root q) :
    q.lower ∈ table registry root ∧ q.upper ∈ table registry root := by
  constructor
  · exact request_types_present registry root q reachable _ (by simp [requestTypes])
  · exact request_types_present registry root q reachable _ (by simp [requestTypes])

theorem production_payloads_present (registry : Registry) (root q : Request)
    (reachable : Reach registry root q) (d : Declaration) (lower upper : Ty)
    (produced : production registry.declarations q = some (d, lower, upper)) :
    lower ∈ table registry root ∧ upper ∈ table registry root := by
  constructor
  · exact request_types_present registry root q reachable _ (by simp [requestTypes, produced])
  · exact request_types_present registry root q reachable _ (by simp [requestTypes, produced])

/-- Both actual produced payloads retain their original syntax, not chosen representatives. -/
theorem production_payloads_preserved (registry : Registry) (root q : Request)
    (reachable : Reach registry root q) (d : Declaration) (lower upper : Ty)
    (produced : production registry.declarations q = some (d, lower, upper)) :
    decode registry root (allocate registry root lower) = lower ∧
    decode registry root (allocate registry root upper) = upper := by
  obtain ⟨low, up⟩ := production_payloads_present registry root q reachable d lower upper produced
  exact ⟨decode_allocate registry root lower low, decode_allocate registry root upper up⟩

def assignment (registry : Registry) (root : Request) (interpret : Ty → α) :
    Fin (table registry root).length → α := fun slot => interpret (decode registry root slot)

theorem assignment_preserved (registry : Registry) (root : Request) (interpret : Ty → α)
    (type : Ty) (member : type ∈ table registry root) :
    assignment registry root interpret (allocate registry root type) = interpret type := by
  simp [assignment, decode_allocate registry root type member]

/-- With the computed allocator, the real generated state has exactly the
old models plus the comparison of the original two source payload meanings.
The interpretation is arbitrary; its full nominal adequacy is not asserted. -/
theorem selected_prepare_exact (registry : Registry) (root q : Request)
    (reachable : Reach registry root q) (key : Nat) (cs : List Request)
    (selected : CommonRoleOpenProducer.Local registry.declarations q (.selected key cs))
    (s : State (table registry root).length) (interpret : Ty → Comp Common.model) :
    ∃ d lower upper,
      production registry.declarations q = some (d, lower, upper) ∧ key = d.key ∧
      cs = CommonRoleOpenProducer.children q d lower upper ∧
      (All Common.model (assignment registry root interpret)
        (CommonRoleOpenPropagation.prepare registry.declarations (allocate registry root) q s).atoms ↔
       All Common.model (assignment registry root interpret) s.atoms ∧
        (d.head.names = [] ∨ Common.Subtype (interpret lower).1 (interpret upper).1)) := by
  obtain ⟨d, lower, upper, produced, sameKey, sameChildren, exactness⟩ :=
    CommonRoleOpenPropagationOrigin.selected_prepare_exact registry.declarations
      (allocate registry root) q key cs s selected
  obtain ⟨low, up⟩ := production_payloads_present registry root q reachable d lower upper produced
  refine ⟨d, lower, upper, produced, sameKey, sameChildren, ?_⟩
  simpa only [assignment_preserved registry root interpret lower low,
    assignment_preserved registry root interpret upper up] using exactness (assignment registry root interpret)

/-- Every child produced by the actual state-gated pass remains in the computed
structural closure, for every ordinary state. State rejection can remove children
but this fixed dual-inspection pass does not create a narrowed source Request. -/
theorem state_children_closed (registry : Registry) (root q child : Request)
    (reachable : Reach registry root q)
    (s : State (table registry root).length)
    (member : child ∈ CommonRoleOpenPropagation.childList
      (CommonRoleOpenPropagation.produce registry.declarations (allocate registry root) q s)) :
    child ∈ closure registry root := by
  exact CommonRoleOpenFiniteClosure.closure_children_closed registry root q child
    (CommonRoleOpenFiniteClosure.closure_complete registry root q reachable)
    (CommonRoleOpenRecursivePass.child_origin registry.declarations (allocate registry root) q s child member)

/-- Actual recursive pass with a computed rather than caller-supplied allocator. -/
def run (registry : Registry) (root : Request) (s : State (table registry root).length) :=
  CommonRoleOpenRecursivePass.run registry (allocate registry root) root s

/-- The existing independent pass judgment, specialized to the actual computed table.
This remains one pass, not final resolution or saturation. -/
theorem run_exact (registry : Registry) (root : Request)
    (s final : State (table registry root).length) (trace : CommonRoleOpenRecursivePass.Trace) :
    run registry root s = (trace, final) ↔
      CommonRoleOpenRecursivePass.Runs registry.declarations (allocate registry root) root s trace final :=
  CommonRoleOpenRecursivePass.run_exact registry (allocate registry root) root s trace final

/-- Exact models of the actual pass with the computed allocation. No allocation
map, fuel, or frontier correctness theorem is an input. Syntactic-Ty scope remains. -/
theorem run_models_exact (registry : Registry) (root : Request)
    (s : State (table registry root).length)
    (valuation : Fin (table registry root).length → Comp Common.model) :
    All Common.model valuation (run registry root s).2.atoms ↔
      All Common.model valuation s.atoms ∧
      CommonRoleOpenPassStability.Good registry (allocate registry root) root valuation :=
  CommonRoleOpenPassStability.run_models_exact registry (allocate registry root) root s valuation

/-- One computed-allocation pass is a semantic fixed point for this structural
producer, not for a future state-narrowing producer or source-variable graph. -/
theorem run_semantically_idempotent (registry : Registry) (root : Request)
    (s : State (table registry root).length)
    (valuation : Fin (table registry root).length → Comp Common.model) :
    All Common.model valuation (run registry root (run registry root s).2).2.atoms ↔
      All Common.model valuation (run registry root s).2.atoms :=
  CommonRoleOpenPassStability.run_semantically_idempotent registry
    (allocate registry root) root s valuation

end Yulang.CommonRoleOpenClosureAllocation
