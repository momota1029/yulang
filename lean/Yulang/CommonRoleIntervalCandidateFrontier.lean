import Yulang.CommonRoleCandidateStateFrontier
import Yulang.CommonRoleEndpointSlots

/-! Preserve both original interval slots while checking each scalar candidate
against the whole ordinary state. This does not pick an interval midpoint. -/
namespace Yulang.CommonRoleIntervalCandidateFrontier
open CommonRoleSettledConstraints (State)
open Core.PresenceGeneration (Comp TyTerm)
open PresenceNormalForm (All Atom)
open CommonRoleCandidateStateFrontier (Candidate)

structure Request (n : Nat) where
  lower : Fin n
  upper : Fin n

def constraints (q : Request n) (head : Inference.Base) : List (Atom (Fin n)) :=
  [.tyLe (.var q.lower) (.base head), .tyLe (.base head) (.var q.upper)]

theorem constraints_grammar (q : Request n) (head : Inference.Base) :
    PresenceGeneratedChildGrammar.GoodAtoms (constraints q head) ∧
    PresenceGeneratedWidth.WidthAtoms (constraints q head) ∧
    PresenceSourceConstraintSupport.GoodAtoms (constraints q head) := by
  refine ⟨?_, ?_, ?_⟩
  · intro atom member; simp only [constraints, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> trivial
  · intro source target member tail needed
    simp only [constraints, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with h | h <;> cases h <;> cases needed
  · intro atom member; simp only [constraints, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> trivial

def prepare (s : State n) (q : Request n) (c : Candidate) : State n :=
  let g := constraints_grammar q c.head
  ⟨s.atoms ++ constraints q c.head, s.child.append g.1,
    s.width.append g.2.1, s.rows.append g.2.2⟩

def Fits (s : State n) (q : Request n) (c : Candidate) : Prop :=
  ∃ assignment : Fin n → Comp Common.model,
    All Common.model assignment s.atoms ∧
    Common.Subtype (assignment q.lower).1 (.base c.head) ∧
    Common.Subtype (.base c.head) (assignment q.upper).1

theorem prepare_exact (s : State n) (q : Request n) (c : Candidate)
    (assignment : Fin n → Comp Common.model) :
    All Common.model assignment (prepare s q c).atoms ↔
      All Common.model assignment s.atoms ∧
      Common.Subtype (assignment q.lower).1 (.base c.head) ∧
      Common.Subtype (.base c.head) (assignment q.upper).1 := by
  change All Common.model assignment (s.atoms ++ constraints q c.head) ↔ _
  rw [PresenceNormalForm.all_append]
  simp [All, constraints, PresenceNormalForm.Atom.Holds, TyTerm.eval, Common.model]

def accepts (s : State n) (q : Request n) (c : Candidate) : Bool :=
  CommonRoleOpenPropagation.consistent (prepare s q c)

theorem accepts_exact (s : State n) (q : Request n) (c : Candidate) :
    accepts s q c = true ↔ Fits s q c := by
  rw [accepts, CommonRoleOpenPropagation.consistent_exact]
  exact exists_congr fun assignment => prepare_exact s q c assignment

def collect (s : State n) (q : Request n) (visible : List Candidate) : List Candidate :=
  visible.filter (accepts s q)

theorem collect_exact (s : State n) (q : Request n) (visible : List Candidate) (c : Candidate) :
    c ∈ collect s q visible ↔ c ∈ visible ∧ Fits s q c := by
  simp only [collect, List.mem_filter, accepts_exact]

/-- Candidates are each checked in a private extension of the SAME old state.
The returned list contains no chosen assignment to either original slot. -/
theorem collect_antitone (before after : State n) (q : Request n) (visible : List Candidate)
    (retains : ∀ assignment : Fin n → Comp Common.model,
      All Common.model assignment after.atoms → All Common.model assignment before.atoms)
    (c : Candidate) (member : c ∈ collect after q visible) :
    c ∈ collect before q visible := by
  obtain ⟨visibleMem, assignment, models, lower, upper⟩ := (collect_exact ..).mp member
  exact (collect_exact ..).mpr ⟨visibleMem, assignment, retains assignment models, lower, upper⟩

/-- When the source identity is the same slot, the interval feasibility rule
agrees exactly with the scalar equality boundary. -/
theorem same_slot_exact (s : State n) (slot : Fin n) (c : Candidate) :
    Fits s ⟨slot, slot⟩ c ↔ CommonRoleCandidateStateFrontier.Fits s slot c := Iff.rfl

/-- Return every ordinary solution family for this candidate, never a single
chosen witness assignment. -/
def solutions (s : State n) (q : Request n) (c : Candidate) :=
  CommonRoleOpenState.solve (prepare s q c) []

theorem solutions_exact (s : State n) (q : Request n) (c : Candidate)
    (assignment : Fin n → Comp Common.model) :
    (All Common.model assignment s.atoms ∧
      Common.Subtype (assignment q.lower).1 (.base c.head) ∧
      Common.Subtype (.base c.head) (assignment q.upper).1) ↔
    ∃ scheme ∈ solutions s q c, ∃ rows : Fin n → Common.Row,
      ∃ parameters : scheme.Parameters,
        CommonDeclaredNominalSourceFamily.AssignmentEquivalent
          (scheme.instantiate rows parameters) assignment := by
  have result := CommonRoleOpenState.solve_all_instances_exact (prepare s q c) [] assignment
  simpa only [List.not_mem_nil, false_implies, forall_const, and_true,
    prepare_exact, solutions] using result

/-- Build the actual interval slot request from a finite source request list. -/
def fromSource (requests : List CommonRoleOpenDescent.Request)
    (index : Fin requests.length) : Request (2 * (CommonRoleEndpointSlots.collect requests).length) :=
  let table := CommonRoleEndpointSlots.collect requests
  ⟨CommonRoleEndpointSlots.allocate table (CommonRoleEndpointSlots.requestSource requests index false),
    CommonRoleEndpointSlots.allocate table (CommonRoleEndpointSlots.requestSource requests index true)⟩

/-- Under any given source interpretation, generated candidate constraints
retain exactly the two original endpoint meanings. This is not a proof that
that interpretation implements the full nominal source semantics. -/
theorem source_bounds_preserved (requests : List CommonRoleOpenDescent.Request)
    (index : Fin requests.length) (interpret : CommonRoleSettledSyntax.Ty → Comp Common.model)
    (s : State (2 * (CommonRoleEndpointSlots.collect requests).length)) (c : Candidate) :
    All Common.model (CommonRoleEndpointSlots.assignment
      (CommonRoleEndpointSlots.collect requests) interpret) (prepare s (fromSource requests index) c).atoms ↔
    All Common.model (CommonRoleEndpointSlots.assignment
      (CommonRoleEndpointSlots.collect requests) interpret) s.atoms ∧
      Common.Subtype (interpret requests[index.val].lower).1 (.base c.head) ∧
      Common.Subtype (.base c.head) (interpret requests[index.val].upper).1 := by
  rw [prepare_exact]
  simp only [fromSource, CommonRoleEndpointSlots.assignment,
    CommonRoleEndpointSlots.request_lower_preserved, CommonRoleEndpointSlots.request_upper_preserved]

end Yulang.CommonRoleIntervalCandidateFrontier
