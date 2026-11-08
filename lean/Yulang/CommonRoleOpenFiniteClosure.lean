import Yulang.CommonRoleOpenProducerAccess
import Yulang.CommonRoleEndpointSlots

/-! Finite executable closure of actual structural-producer children.
No externally supplied universe, fuel, or accessibility proof is required.
This does not cover the not-yet-defined state-narrowing saturation graph. -/
namespace Yulang.CommonRoleOpenFiniteClosure
open CommonRoleOpenProducer
open CommonRoleOutermostResolver (Child)

def next (registry : Registry) (q : Request) : List Request :=
  match frontier registry.declarations q with
  | .selected _ cs => cs
  | _ => []

theorem mem_next (registry : Registry) (q child : Request) :
    child ∈ next registry q ↔ Child (Local registry.declarations) child q := by
  unfold next
  cases observed : frontier registry.declarations q with
  | pending =>
    constructor
    · simp
    · rintro ⟨key, cs, selected, _⟩
      have h := frontier_complete selected
      rw [observed] at h
      cases h
  | rejected =>
    constructor
    · simp
    · rintro ⟨key, cs, selected, _⟩
      have h := frontier_complete selected
      rw [observed] at h
      cases h
  | ambiguous =>
    constructor
    · simp
    · rintro ⟨key, cs, selected, _⟩
      have h := frontier_complete selected
      rw [observed] at h
      cases h
  | selected key cs =>
    constructor
    · intro member
      exact ⟨key, cs, observed ▸ frontier_sound registry.declarations q, member⟩
    · rintro ⟨other, rest, selected, member⟩
      have h := frontier_complete selected
      rw [observed] at h
      cases h
      exact member

def closure (registry : Registry) (q : Request) : List Request :=
  q :: (next registry q).attach.flatMap (fun child => closure registry child.val)
termination_by CommonRoleOpenDescent.weight q
decreasing_by
  exact CommonRoleOpenProducerAccess.child_decreases registry q child.val
    ((mem_next registry q child.val).mp child.property)

inductive Reach (registry : Registry) : Request → Request → Prop where
  | refl : Reach registry q q
  | step : Child (Local registry.declarations) child q →
      Reach registry child target → Reach registry q target

theorem closure_complete (registry : Registry) (q target : Request)
    (reachable : Reach registry q target) : target ∈ closure registry q := by
  induction reachable with
  | refl => rw [closure]; exact List.mem_cons_self
  | @step child q target edge _ ih =>
      rw [closure]
      apply List.mem_cons_of_mem
      exact List.mem_flatMap.mpr ⟨⟨child, (mem_next registry q child).mpr edge⟩,
        List.mem_attach _ _, ih⟩

theorem closure_sound (registry : Registry) (q target : Request)
    (member : target ∈ closure registry q) : Reach registry q target := by
  have all : ∀ measure, ∀ q : Request, CommonRoleOpenDescent.weight q = measure →
      ∀ target, target ∈ closure registry q → Reach registry q target := by
    intro measure
    induction measure using Nat.strongRecOn with
    | ind measure ih =>
      intro q size target member
      rw [closure] at member
      rcases List.mem_cons.mp member with same | below
      · subst target; exact .refl
      · obtain ⟨child, _, member⟩ := List.mem_flatMap.mp below
        have edge := (mem_next registry q child.val).mp child.property
        exact .step edge (ih _ (by rw [← size]; exact
          CommonRoleOpenProducerAccess.child_decreases registry q child.val edge)
          child.val rfl target member)
  exact all _ q rfl target member

theorem closure_exact (registry : Registry) (q target : Request) :
    target ∈ closure registry q ↔ Reach registry q target :=
  ⟨closure_sound registry q target, closure_complete registry q target⟩

theorem reach_trans (registry : Registry) (q middle target : Request)
    (first : Reach registry q middle) (second : Reach registry middle target) :
    Reach registry q target := by
  induction first with
  | refl => exact second
  | step edge _ ih => exact .step edge (ih second)

/-- The computed finite list is closed under every actual produced child. -/
theorem closure_children_closed (registry : Registry) (root q child : Request)
    (member : q ∈ closure registry root)
    (edge : Child (Local registry.declarations) child q) :
    child ∈ closure registry root := by
  apply closure_complete
  exact reach_trans registry root q child (closure_sound registry root q member)
    (.step edge .refl)

/-- Every reachable request has real lower/upper occurrence slots in the
computed endpoint table. Finiteness is derived rather than an input assumption. -/
theorem reachable_slots (registry : Registry) (root q : Request)
    (reachable : Reach registry root q) :
    ∃ index : Fin (closure registry root).length,
      CommonRoleEndpointSlots.slotEndpoint
        (CommonRoleEndpointSlots.collect (closure registry root))
        (CommonRoleEndpointSlots.allocate
          (CommonRoleEndpointSlots.collect (closure registry root))
          (CommonRoleEndpointSlots.requestSource (closure registry root) index false)) = q.lower ∧
      CommonRoleEndpointSlots.slotEndpoint
        (CommonRoleEndpointSlots.collect (closure registry root))
        (CommonRoleEndpointSlots.allocate
          (CommonRoleEndpointSlots.collect (closure registry root))
          (CommonRoleEndpointSlots.requestSource (closure registry root) index true)) = q.upper := by
  obtain ⟨i, bound, same⟩ := List.getElem_of_mem (closure_complete registry root q reachable)
  refine ⟨⟨i, bound⟩, ?_, ?_⟩
  · rw [CommonRoleEndpointSlots.request_lower_preserved, same]
  · rw [CommonRoleEndpointSlots.request_upper_preserved, same]

end Yulang.CommonRoleOpenFiniteClosure
