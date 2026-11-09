import Yulang.CommonRoleFeedbackSupport

/-! A checked first-hit producer can lose a child under ordinary narrowing.
This is an implementation counterexample, NOT a language counterexample:
frontier selection must be settled before candidate-specific obligations commit. -/
namespace Yulang.CommonRoleFirstHitSupportBoundary
open CommonRoleSettledSyntax CommonRoleOpenProducer
open CommonRoleMaterializedDomain CommonRoleSourceWorklist
open CommonRoleSettledConstraints (State)

def literal : Declaration := ⟨0, 0, .wrap (.nominal 0) (.atom .int), []⟩
def capture : Declaration := ⟨0, 1, .wrap (.nominal 0) (.bind 0 []), [(1, .var 0)]⟩
def registry : Registry := ⟨[literal, capture], by
  intro d member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> decide, by decide⟩

def root : SourceRequest 1 := ⟨0, .wrap (.nominal 0) (.slot 0), .wrap (.nominal 0) (.slot 0)⟩
def child : SourceRequest 1 := ⟨1, .slot 0, .slot 0⟩
def before : State 1 := .empty
def after : State 1 := CommonRoleCandidateStateFrontier.extend before 0 .int

/-- A real ordinary equality grows the atom list without deleting old evidence. -/
theorem atoms_included : before.atoms ⊆ after.atoms := by simp [before, State.empty]

/-- The actual source producer first emits a captured child, but after learning
that the shared source slot is int an earlier literal head displaces it. -/
theorem child_disappears :
    child ∈ actualNext registry before root ∧ child ∉ actualNext registry after root := by
  decide

/-- The former first hit was not a settled frontier: the earlier literal was
pending. After narrowing there are two hits, so the frontier is ambiguous. -/
theorem frontier_not_selected :
    frontier registry.declarations (root.eval before) = .pending ∧
    frontier registry.declarations (root.eval after) = .ambiguous := by
  constructor <;> rfl

/-- A caller cannot infer source-child monotonicity from atom inclusion, even
with a checked registry and a single consistent scalar equality. -/
theorem not_universal_child_monotone :
    ¬ (∀ (r : Registry) (p c : SourceRequest 1) (a b : State 1),
      a.atoms ⊆ b.atoms → c ∈ actualNext r a p → c ∈ actualNext r b p) := by
  intro h
  exact child_disappears.2 (h registry root child before after atoms_included child_disappears.1)

def childNode : Node registry root := ⟨child,
  CommonRoleSourceTemplateClosure.generated_closed registry root root child
    (CommonRoleSourceTemplateClosure.closure_complete registry root root .refl)
    (actual_next_generated registry before root child child_disappears.1)⟩

/-- The displaced child really leaves the recomputed source reachability set,
not merely a direct edge list. -/
theorem reachable_disappears :
    Reach registry root before childNode ∧ ¬ Reach registry root after childNode := by
  constructor
  · exact .step .root child_disappears.1
  · intro reached
    have onlyRoot : ∀ q : Node registry root, Reach registry root after q → q = rootNode registry root := by
      intro q h
      induction h with
      | root => rfl
      | @step parent child _ edge ih =>
        rw [ih] at edge
        have empty : actualNext registry after (rootNode registry root).val = [] := rfl
        rw [empty] at edge
        cases edge
    have equal := congrArg (fun q : Node registry root => q.val.role) (onlyRoot childNode reached)
    change 1 = 0 at equal
    omega
end Yulang.CommonRoleFirstHitSupportBoundary
