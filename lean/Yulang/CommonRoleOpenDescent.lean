import Yulang.CommonRoleSettledSyntax

/-! Both endpoint measures descend after actual independent inspections.
This is not a candidate-completeness theorem: propagation may narrow an
interval, so two separate inspections cannot define general applicability. -/
namespace Yulang.CommonRoleOpenDescent
open CommonRoleSettledSyntax

/-- Every original ordered where requirement decreases both endpoints.
Neither endpoints nor captured payloads are required to be equal. -/
theorem checked_child_decreases (d : Declaration) (checked : d.check = true)
    (r : Nat × Template) (member : r ∈ d.requirements)
    (lower upper lowerPayload upperPayload : Ty)
    (lowerMatched : Inspect d.head lower (.hit lowerPayload))
    (upperMatched : Inspect d.head upper (.hit upperPayload)) :
    (r.2.instantiate lowerPayload).weight + (r.2.instantiate upperPayload).weight <
      lower.weight + upper.weight :=
  Nat.add_lt_add
    (CommonRoleSettledSyntax.checked_child_decreases d checked r member lower lowerPayload lowerMatched)
    (CommonRoleSettledSyntax.checked_child_decreases d checked r member upper upperPayload upperMatched)

/-- The independent syntactic transition retains both original endpoint
captures and every actual requirement, including duplicates. -/
structure Request where
  role : Nat
  lower : Ty
  upper : Ty

inductive Step (declarations : List Declaration) : Request → Request → Prop where
  | requirement : d ∈ declarations → d.role = parent.role →
      Inspect d.head parent.lower (.hit lowerPayload) →
      Inspect d.head parent.upper (.hit upperPayload) →
      r ∈ d.requirements →
      Step declarations
        ⟨r.1, r.2.instantiate lowerPayload, r.2.instantiate upperPayload⟩ parent

def weight (q : Request) := q.lower.weight + q.upper.weight

theorem step_decreases (declarations : List Declaration)
    (checked : ∀ d ∈ declarations, d.check = true)
    (child parent : Request) (h : Step declarations child parent) : weight child < weight parent := by
  cases h with
  | requirement member _ low up req =>
    exact checked_child_decreases _ (checked _ member) _ req _ _ _ _ low up

/-- Accessibility for all requests is derived from the real declaration
check, not supplied as a request field or an assumed role rank. This relation
is only the stated inspection transition, NOT the unresolved full producer. -/
theorem accessible (declarations : List Declaration)
    (checked : ∀ d ∈ declarations, d.check = true) (q : Request) :
    Acc (Step declarations) q := by
  have all : ∀ measure, ∀ q : Request, weight q = measure → Acc (Step declarations) q := by
    intro measure
    induction measure using Nat.strongRecOn with
    | ind measure ih =>
      intro q equal
      constructor
      intro child edge
      exact ih (weight child) (by rw [← equal]; exact step_decreases declarations checked child q edge) child rfl
  exact all (weight q) q rfl

end Yulang.CommonRoleOpenDescent
