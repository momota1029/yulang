import Yulang.CommonRoleOpenPropagation

/-! Candidate-local scalar constraints are solved before collecting candidates.
This is an ordinary-slot feasibility boundary, not final source resolution.
No candidate equality is committed to the shared state by this operation. -/
namespace Yulang.CommonRoleCandidateStateFrontier
open CommonRoleSettledConstraints (State)
open Core.PresenceGeneration (Comp TyTerm)
open PresenceNormalForm (All Atom)

structure Candidate where
  key : Nat
  head : Inference.Base
  deriving DecidableEq, Repr

def equality (slot : Fin n) (head : Inference.Base) : List (Atom (Fin n)) :=
  [.tyLe (.var slot) (.base head), .tyLe (.base head) (.var slot)]

theorem equality_grammar (slot : Fin n) (head : Inference.Base) :
    PresenceGeneratedChildGrammar.GoodAtoms (equality slot head) ∧
    PresenceGeneratedWidth.WidthAtoms (equality slot head) ∧
    PresenceSourceConstraintSupport.GoodAtoms (equality slot head) := by
  refine ⟨?_, ?_, ?_⟩
  · intro atom member; simp only [equality, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> trivial
  · intro source target member tail needed
    simp only [equality, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with h | h <;> cases h <;> cases needed
  · intro atom member; simp only [equality, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> trivial

def extend (s : State n) (slot : Fin n) (head : Inference.Base) : State n :=
  let g := equality_grammar slot head
  ⟨s.atoms ++ equality slot head, s.child.append g.1,
    s.width.append g.2.1, s.rows.append g.2.2⟩

def Fits (s : State n) (slot : Fin n) (c : Candidate) : Prop :=
  ∃ assignment : Fin n → Comp Common.model,
    All Common.model assignment s.atoms ∧
    Common.Equivalent (assignment slot).1 (.base c.head)

theorem extend_exact (s : State n) (slot : Fin n) (head : Inference.Base)
    (assignment : Fin n → Comp Common.model) :
    All Common.model assignment (extend s slot head).atoms ↔
      All Common.model assignment s.atoms ∧
      Common.Equivalent (assignment slot).1 (.base head) := by
  change All Common.model assignment (s.atoms ++ equality slot head) ↔ _
  rw [PresenceNormalForm.all_append]
  simp [All, equality, PresenceNormalForm.Atom.Holds, TyTerm.eval, Common.model, Common.Equivalent]

def accepts (s : State n) (slot : Fin n) (c : Candidate) : Bool :=
  CommonRoleOpenPropagation.consistent (extend s slot c.head)

theorem accepts_exact (s : State n) (slot : Fin n) (c : Candidate) :
    accepts s slot c = true ↔ Fits s slot c := by
  rw [accepts, CommonRoleOpenPropagation.consistent_exact]
  exact exists_congr fun assignment => extend_exact s slot c.head assignment

def collect (s : State n) (slot : Fin n) (visible : List Candidate) : List Candidate :=
  visible.filter (accepts s slot)

theorem collect_exact (s : State n) (slot : Fin n) (visible : List Candidate) (c : Candidate) :
    c ∈ collect s slot visible ↔ c ∈ visible ∧ Fits s slot c := by
  simp only [collect, List.mem_filter, accepts_exact]

/-- Stronger shared states can only remove feasible candidates. -/
theorem collect_antitone (before after : State n) (slot : Fin n) (visible : List Candidate)
    (retains : ∀ assignment : Fin n → Comp Common.model,
      All Common.model assignment after.atoms → All Common.model assignment before.atoms)
    (c : Candidate) (member : c ∈ collect after slot visible) :
    c ∈ collect before slot visible := by
  obtain ⟨visibleMem, assignment, models, fits⟩ := (collect_exact ..).mp member
  exact (collect_exact ..).mpr ⟨visibleMem, assignment, retains assignment models, fits⟩

/-- A separate associated equation can narrow feasible candidates, without
committing the hypothesis of any candidate to the original state. -/
theorem fits_after_equation (s : State n) (slot : Fin n) (head : Inference.Base)
    (c : Candidate) :
    Fits (extend s slot head) slot c ↔ Fits s slot c ∧ head = c.head := by
  constructor
  · rintro ⟨assignment, models, fits⟩
    obtain ⟨old, equation⟩ := (extend_exact ..).mp models
    have equal := Common.equivalent_trans (Common.equivalent_symm equation) fits
    exact ⟨⟨assignment, old, fits⟩, (CommonRigidHeadInspection.base_iff _ _).mp equal.1⟩
  · rintro ⟨⟨assignment, old, fits⟩, same⟩
    subst head
    exact ⟨assignment, (extend_exact ..).mpr ⟨old, fits⟩, fits⟩

theorem collect_after_equation (s : State n) (slot : Fin n) (head : Inference.Base)
    (visible : List Candidate) (c : Candidate) :
    c ∈ collect (extend s slot head) slot visible ↔
      c ∈ collect s slot visible ∧ head = c.head := by
  simp only [collect_exact, fits_after_equation, and_assoc]

theorem empty_fits (slot : Fin n) (c : Candidate) : Fits State.empty slot c := by
  exact ⟨fun _ => Comp.pure Common.model (.base c.head),
    PresenceNormalForm.all_nil _ _, Common.equivalent_refl _⟩

/-- Visibility of a single implementation does not modify the input state:
the output consists only of feasible candidates, not a chosen assignment. -/
theorem singleton_remains_feasible (slot : Fin n) (c : Candidate) :
    collect State.empty slot [c] = [c] := by
  have yes := (accepts_exact State.empty slot c).mpr (empty_fits slot c)
  simp [collect, yes]

def leftInt : Candidate := ⟨10, .int⟩
def leftStr : Candidate := ⟨11, .str⟩

theorem before_associated_equation :
    leftInt ∈ collect State.empty (0 : Fin 1) [leftInt, leftStr] ∧
    leftStr ∈ collect State.empty (0 : Fin 1) [leftInt, leftStr] := by
  constructor <;> apply (collect_exact ..).mpr
  · exact ⟨by simp, empty_fits _ _⟩
  · exact ⟨by simp, empty_fits _ _⟩

theorem after_associated_equation :
    leftInt ∈ collect (extend State.empty (0 : Fin 1) .int) 0 [leftInt, leftStr] ∧
    leftStr ∉ collect (extend State.empty (0 : Fin 1) .int) 0 [leftInt, leftStr] := by
  constructor
  · exact (collect_after_equation ..).mpr ⟨before_associated_equation.1, rfl⟩
  · intro h
    have wrong := ((collect_after_equation ..).mp h).2
    cases wrong

end Yulang.CommonRoleCandidateStateFrontier
