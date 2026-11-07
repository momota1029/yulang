import Yulang.CommonCanonicalRowTests
import Yulang.CommonCanonicalRowGeometry
import Yulang.CanonicalRegisterMachine

/-!
# Finite signed-row equations for counter-program invariants

Each control state has two unrestricted row parameters, intended as an
invariant and its complement inside the finitely described natural grid.
Only ordinary finite row expressions enter the compiled tests.
-/

namespace Yulang.CommonCanonicalCounterConstraints

open CommonCanonicalRowSyntax
open CommonCanonicalRowTests
open CommonCanonicalRowGeometry
open CanonicalRegisterMachine (Program Instruction State)

def inputValues (registers input : Nat) : Fin (registers + 1) → Nat :=
  fun register => if register = 0 then input else 0

def seed (registers : Nat) : Nat → Row (registers + 1) parameters
  | 0 => .head 0
  | input + 1 => .protect 0 (.only []) (seed registers input)

/-- The seed is finite head/protect syntax. Its length may grow with the
numeric input, but its meaning is exactly one initial counter vector. -/
theorem seed_exact (registers input : Nat) (assignment : Fin parameters → Common.Row)
    (occurrence : Common.Occurrence) :
    rowEval assignment (seed registers input) occurrence ↔
      commonPoint (inputValues registers input) = occurrence := by
  have zero : point (inputValues registers 0) = Directed.raw 0 := by
    apply Directed.Occurrence.ext
    · rfl
    intro coordinate
    simp [point, inputValues, Directed.raw]
  have advance (input : Nat) :
      CommonSignedRows.shiftOccurrence 0 Directed.allowNone 1
        (commonPoint (inputValues registers input)) =
      commonPoint (inputValues registers (input + 1)) := by
    have changed : write (inputValues registers input) 0 (inputValues registers input 0 + 1) =
        inputValues registers (input + 1) := by
      funext coordinate
      by_cases same : coordinate = 0 <;> simp [write, inputValues, same]
    exact (counter_transport_exact 0 (inputValues registers input)).1.trans (congrArg commonPoint changed)
  induction input generalizing occurrence with
  | zero =>
      change CommonSignedRows.embedRow [Directed.raw 0] occurrence ↔ _
      rw [commonPoint, zero]
      simp [CommonSignedRows.embedRow]
  | succ input ih =>
      change CommonSignedRows.commonProtect 0 Directed.allowNone
        (rowEval assignment (seed registers input)) occurrence ↔ _
      rw [CommonSignedRows.commonProtect, CommonSignedRows.transport_member_iff]
      constructor
      · rintro ⟨source, present, moved⟩
        have same := (ih source).mp present
        subst source
        exact (advance input).symm.trans moved
      · intro same
        exact ⟨commonPoint (inputValues registers input), (ih _).mpr rfl, (advance input).trans same⟩

def gridRow : Row scopes parameters := .var (.inr (gridUniverse scopes))

def zeroRow (scope : Fin scopes) : Row scopes parameters := .var (.inr (zeroAt scope))

def positiveRow (scope : Fin scopes) : Row scopes parameters :=
  .protect scope (.only []) gridRow

def reachRow (pc : Fin states) : Row scopes (states + states) :=
  .var (.inl (pc.castAdd states))

def complementRow (pc : Fin states) : Row scopes (states + states) :=
  .var (.inl (pc.natAdd states))

def forbidden (first : Row scopes parameters) (rest : List (Row scopes parameters)) : Test scopes parameters :=
  ⟨first, rest, .empty⟩

def partitionTests (registers : Nat) (pc : Fin states) : List (Test (registers + 1) (states + states)) :=
  [⟨.union (reachRow pc) (complementRow pc), [], gridRow⟩,
    forbidden (reachRow pc) [complementRow pc]]

def instructionTests (pc : Fin states) : Instruction registers states →
    List (Test (registers + 1) (states + states))
  | .halt => [forbidden (reachRow pc) []]
  | .increment register next =>
      [forbidden (.protect register (.only []) (reachRow pc)) [complementRow next]]
  | .decrement register zero positive =>
      [forbidden (reachRow pc) [zeroRow register, complementRow zero],
        forbidden (.release register (.only []) (reachRow pc))
          [.release register (.only []) (positiveRow register), complementRow positive]]
  | .goto next => [forbidden (reachRow pc) [complementRow next]]

def instructionAt (program : Program) (pc : Fin program.states) :
    Instruction program.registers program.states := program.code[pc.val]?.getD .halt

def constraints (program : Program) (input : Nat) :
    List (Test (program.registers + 1) (program.states + program.states)) :=
  forbidden (seed program.registers input) [complementRow program.entry] ::
    (List.finRange program.states).flatMap (fun pc =>
      partitionTests program.registers pc ++ instructionTests pc (instructionAt program pc))

/-- The finite compiler emits the initial fact, both partition equations
for every declared control state, and every instruction's closure equations.
Missing table entries are handled by the same default halt as machine step. -/
theorem constraints_split (program : Program) (input : Nat)
    (assignment : Fin (program.states + program.states) → Common.Row) :
    ProblemHolds (constraints program input) assignment ↔
      (forbidden (seed program.registers input) [complementRow program.entry]).Holds assignment ∧
      ∀ pc : Fin program.states,
        ProblemHolds (partitionTests program.registers pc) assignment ∧
        ProblemHolds (instructionTests pc (instructionAt program pc)) assignment := by
  constructor
  · intro all
    refine ⟨all _ List.mem_cons_self, ?_⟩
    intro pc
    constructor <;> intro test member <;> apply all test <;> apply List.mem_cons_of_mem
    · exact List.mem_flatMap.mpr ⟨pc, List.mem_finRange pc, List.mem_append.mpr (Or.inl member)⟩
    · exact List.mem_flatMap.mpr ⟨pc, List.mem_finRange pc, List.mem_append.mpr (Or.inr member)⟩
  · rintro ⟨initial, all⟩ test member
    rcases List.mem_cons.mp member with rfl | member
    · exact initial
    · obtain ⟨pc, _, included⟩ := List.mem_flatMap.mp member
      exact (List.mem_append.mp included).elim ((all pc).1 test) ((all pc).2 test)

end Yulang.CommonCanonicalCounterConstraints
