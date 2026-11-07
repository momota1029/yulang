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

theorem forbidden_exact (first : Row scopes parameters) (rest : List (Row scopes parameters))
    (assignment : Fin parameters → Common.Row) :
    (forbidden first rest).Holds assignment ↔
      ∀ occurrence, ¬ meetEval assignment first rest occurrence := by
  change meetEval assignment first rest = Common.rowEmpty ↔ _
  constructor
  · intro empty occurrence member
    have impossible : Common.rowEmpty occurrence := empty ▸ member
    exact impossible
  · intro absent
    funext occurrence
    exact propext ⟨absent occurrence, False.elim⟩

def reached (assignment : Fin (states + states) → Common.Row) (pc : Fin states) : Common.Row :=
  assignment (pc.castAdd states)

def excluded (assignment : Fin (states + states) → Common.Row) (pc : Fin states) : Common.Row :=
  assignment (pc.natAdd states)

theorem partition_exact (registers : Nat) (pc : Fin states)
    (assignment : Fin (states + states) → Common.Row) :
    ProblemHolds (partitionTests registers pc) assignment ↔
      Common.rowJoin (reached assignment pc) (excluded assignment pc) = (gridUniverse (registers + 1)).meaning ∧
      ∀ occurrence, reached assignment pc occurrence → excluded assignment pc occurrence → False := by
  simp only [ProblemHolds, partitionTests, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  change (Common.rowJoin (reached assignment pc) (excluded assignment pc) =
      (gridUniverse (registers + 1)).meaning ∧
    (forbidden (reachRow pc) [complementRow pc]).Holds assignment) ↔ _
  rw [forbidden_exact]
  constructor
  · rintro ⟨cover, apart⟩
    exact ⟨cover, fun occurrence present absent => apart occurrence ⟨absent, present⟩⟩
  · rintro ⟨cover, apart⟩
    exact ⟨cover, fun occurrence member => apart occurrence member.2 member.1⟩

/-- Every solution of the concrete finite row problem yields an actual
nonterminal-step invariant of the counter program. -/
theorem constraints_imply_invariant (program : Program) (input : Nat)
    (assignment : Fin (program.states + program.states) → Common.Row)
    (satisfied : ProblemHolds (constraints program input) assignment) :
    CanonicalRegisterMachine.Invariant program input
      (fun state => reached assignment state.pc (commonPoint state.values)) := by
  obtain ⟨initial, all⟩ := (constraints_split program input assignment).mp satisfied
  have partitions (pc : Fin program.states) := (partition_exact program.registers pc assignment).mp (all pc).1
  have recover (pc : Fin program.states) (values : Fin (program.registers + 1) → Nat)
      (notExcluded : ¬ excluded assignment pc (commonPoint values)) :
      reached assignment pc (commonPoint values) := by
    have covered : Common.rowJoin (reached assignment pc) (excluded assignment pc) (commonPoint values) :=
      (partitions pc).1.symm ▸ (universe_exact _).mpr ⟨values, rfl⟩
    exact covered.elim id (fun excluded => False.elim (notExcluded excluded))
  constructor
  · apply recover program.entry (inputValues program.registers input)
    intro opposite
    exact (forbidden_exact _ _ assignment).mp initial _
      ⟨opposite, (seed_exact program.registers input assignment _).mpr rfl⟩
  · intro state present
    have rules := (all state.pc).2
    cases instruction : instructionAt program state.pc with
    | halt =>
        have forbiddenHead : (forbidden (reachRow state.pc) []).Holds assignment :=
          rules _ (by simp [instruction, instructionTests])
        have impossible := (forbidden_exact _ _ assignment).mp forbiddenHead (commonPoint state.values) present
        exact False.elim impossible
    | goto next =>
        have forbiddenHead : (forbidden (reachRow state.pc) [complementRow next]).Holds assignment :=
          rules _ (by simp [instruction, instructionTests])
        have result : reached assignment next (commonPoint state.values) := by
          apply recover
          intro opposite
          exact (forbidden_exact _ _ assignment).mp forbiddenHead _ ⟨opposite, present⟩
        have current : program.code[state.pc.val]?.getD .halt = .goto next := instruction
        simpa only [CanonicalRegisterMachine.step, current] using result
    | increment register next =>
        have forbiddenHead : (forbidden (.protect register (.only []) (reachRow state.pc))
            [complementRow next]).Holds assignment := rules _ (by simp [instruction, instructionTests])
        let values := CanonicalRegisterMachine.write state.values register (state.values register + 1)
        have transported : CommonSignedRows.commonProtect register.val Directed.allowNone
            (reached assignment state.pc) (commonPoint values) :=
          (CommonSignedRows.transport_member_iff _ _ _ _ _).mpr
            ⟨commonPoint state.values, present, (counter_transport_exact register state.values).1⟩
        have result : reached assignment next (commonPoint values) := by
          apply recover
          intro opposite
          exact (forbidden_exact _ _ assignment).mp forbiddenHead _ ⟨opposite, transported⟩
        have current : program.code[state.pc.val]?.getD .halt = .increment register next := instruction
        simpa only [CanonicalRegisterMachine.step, current] using result
    | decrement register zero positive =>
        have zeroTest : (forbidden (reachRow state.pc) [zeroRow register, complementRow zero]).Holds assignment :=
          rules _ (by simp [instruction, instructionTests])
        have positiveTest : (forbidden (.release register (.only []) (reachRow state.pc))
            [.release register (.only []) (positiveRow register), complementRow positive]).Holds assignment :=
          rules _ (by simp [instruction, instructionTests])
        have current : program.code[state.pc.val]?.getD .halt = .decrement register zero positive := instruction
        by_cases empty : state.values register = 0
        · have result : reached assignment zero (commonPoint state.values) := by
            apply recover
            intro opposite
            exact (forbidden_exact _ _ assignment).mp zeroTest _
              ⟨(zeroAt_point register state.values).mpr empty, opposite, present⟩
          simpa only [CanonicalRegisterMachine.step, current, empty, ↓reduceIte] using result
        · have nonzero : 0 < state.values register := by omega
          let values := CanonicalRegisterMachine.write state.values register (state.values register - 1)
          have moved := (counter_transport_exact register state.values).2 nonzero
          have transported : CommonSignedRows.commonRelease register.val Directed.allowNone
              (reached assignment state.pc) (commonPoint values) :=
            (CommonSignedRows.transport_member_iff _ _ _ _ _).mpr ⟨commonPoint state.values, present, moved⟩
          have guard : CommonSignedRows.commonRelease register.val Directed.allowNone
              (CommonSignedRows.commonProtect register.val Directed.allowNone
                (gridUniverse (program.registers + 1)).meaning) (commonPoint values) :=
            (CommonSignedRows.transport_member_iff _ _ _ _ _).mpr
              ⟨commonPoint state.values, (positiveAt_point register state.values).mpr nonzero, moved⟩
          have result : reached assignment positive (commonPoint values) := by
            apply recover
            intro opposite
            exact (forbidden_exact _ _ assignment).mp positiveTest _ ⟨guard, opposite, transported⟩
          simpa only [CanonicalRegisterMachine.step, current, empty, ↓reduceIte] using result

/-- Every counter invariant supplies unrestricted row parameters satisfying
the actual finite compilation, including complement and all branch tests. -/
theorem invariant_has_constraints (program : Program) (input : Nat)
    (safe : State program.registers program.states → Prop)
    (invariant : CanonicalRegisterMachine.Invariant program input safe) :
    ∃ assignment : Fin (program.states + program.states) → Common.Row,
      ProblemHolds (constraints program input) assignment := by
  classical
  let positive (pc : Fin program.states) : Common.Row := fun occurrence =>
    ∃ values : Fin (program.registers + 1) → Nat, commonPoint values = occurrence ∧ safe ⟨pc, values⟩
  let negative (pc : Fin program.states) : Common.Row := fun occurrence =>
    (gridUniverse (program.registers + 1)).meaning occurrence ∧ ¬ positive pc occurrence
  let assignment : Fin (program.states + program.states) → Common.Row := Fin.addCases positive negative
  have reachedValue (pc : Fin program.states) : reached assignment pc = positive pc := by
    simp [reached, assignment]
  have excludedValue (pc : Fin program.states) : excluded assignment pc = negative pc := by
    exact Fin.addCases_right (motive := fun _ => Common.Row) (left := positive) (right := negative) pc
  have reachEval (pc : Fin program.states) :
      rowEval (scopes := program.registers + 1) assignment (reachRow pc) = positive pc := reachedValue pc
  have complementEval (pc : Fin program.states) :
      rowEval (scopes := program.registers + 1) assignment (complementRow pc) = negative pc := excludedValue pc
  have protectEval (scope : Fin (program.registers + 1))
      (row : Row (program.registers + 1) (program.states + program.states)) :
      rowEval assignment (.protect scope (.only []) row) =
        CommonSignedRows.commonProtect scope.val Directed.allowNone (rowEval assignment row) := rfl
  have releaseEval (scope : Fin (program.registers + 1))
      (row : Row (program.registers + 1) (program.states + program.states)) :
      rowEval assignment (.release scope (.only []) row) =
        CommonSignedRows.commonRelease scope.val Directed.allowNone (rowEval assignment row) := rfl
  refine ⟨assignment, (constraints_split program input assignment).mpr ?_⟩
  constructor
  · apply (forbidden_exact _ _ assignment).mpr
    intro occurrence member
    change rowEval assignment (complementRow program.entry) occurrence ∧
      rowEval assignment (seed program.registers input) occurrence at member
    rw [complementEval] at member
    exact member.1.2 ⟨inputValues program.registers input,
      (seed_exact program.registers input assignment occurrence).mp member.2, invariant.1⟩
  · intro pc
    constructor
    · apply (partition_exact program.registers pc assignment).mpr
      rw [reachedValue, excludedValue]
      constructor
      · funext occurrence
        apply propext
        constructor
        · rintro (⟨values, same, _⟩ | absent)
          · exact (universe_exact occurrence).mpr ⟨values, same⟩
          · exact absent.1
        · intro member
          by_cases present : positive pc occurrence
          · exact Or.inl present
          · exact Or.inr ⟨member, present⟩
      · intro occurrence present absent
        exact absent.2 present
    · cases instruction : instructionAt program pc with
      | halt =>
          simp only [instructionTests, ProblemHolds, List.mem_singleton, forall_eq]
          apply (forbidden_exact _ _ assignment).mpr
          simp only [meetEval, reachEval]
          rintro occurrence ⟨values, _, present⟩
          have current : program.code[pc.val]?.getD .halt = .halt := instruction
          have impossible := invariant.2 ⟨pc, values⟩ present
          simp only [CanonicalRegisterMachine.step, current] at impossible
      | goto next =>
          simp only [instructionTests, ProblemHolds, List.mem_singleton, forall_eq]
          apply (forbidden_exact _ _ assignment).mpr
          simp only [meetEval, reachEval, complementEval]
          rintro occurrence ⟨absent, values, same, present⟩
          apply absent.2
          refine ⟨values, same, ?_⟩
          have current : program.code[pc.val]?.getD .halt = .goto next := instruction
          have continued := invariant.2 ⟨pc, values⟩ present
          simpa only [CanonicalRegisterMachine.step, current] using continued
      | increment register next =>
          simp only [instructionTests, ProblemHolds, List.mem_singleton, forall_eq]
          apply (forbidden_exact _ _ assignment).mpr
          simp only [meetEval, protectEval, reachEval, complementEval]
          rintro occurrence ⟨absent, transported⟩
          obtain ⟨source, ⟨values, rfl, present⟩, moved⟩ :=
            (CommonSignedRows.transport_member_iff _ _ _ _ _).mp transported
          apply absent.2
          refine ⟨CanonicalRegisterMachine.write values register (values register + 1),
            (counter_transport_exact register values).1.symm.trans moved, ?_⟩
          have current : program.code[pc.val]?.getD .halt = .increment register next := instruction
          have continued := invariant.2 ⟨pc, values⟩ present
          simpa only [CanonicalRegisterMachine.step, current] using continued
      | decrement register zero positiveNext =>
          simp only [instructionTests, ProblemHolds, List.mem_cons, List.not_mem_nil, or_false,
            forall_eq_or_imp, forall_eq]
          have current : program.code[pc.val]?.getD .halt = .decrement register zero positiveNext := instruction
          constructor
          · apply (forbidden_exact _ _ assignment).mpr
            simp only [meetEval, reachEval, complementEval]
            rintro occurrence ⟨guard, absent, values, rfl, present⟩
            have empty := (zeroAt_point register values).mp guard
            apply absent.2
            refine ⟨values, rfl, ?_⟩
            have continued := invariant.2 ⟨pc, values⟩ present
            simpa only [CanonicalRegisterMachine.step, current, empty, ↓reduceIte] using continued
          · apply (forbidden_exact _ _ assignment).mpr
            simp only [meetEval, releaseEval, reachEval, complementEval]
            rintro occurrence ⟨guard, absent, transported⟩
            obtain ⟨source, ⟨values, rfl, present⟩, moved⟩ :=
              (CommonSignedRows.transport_member_iff _ _ _ _ _).mp transported
            have back : CommonSignedRows.shiftOccurrence register.val Directed.allowNone 1 occurrence =
                commonPoint values :=
              (congrArg (CommonSignedRows.shiftOccurrence register.val Directed.allowNone 1) moved.symm).trans
                (by simpa using CommonSignedRows.shiftOccurrence_inverse register.val Directed.allowNone (-1) (commonPoint values))
            change CommonSignedRows.commonProtect register.val Directed.allowNone
              (gridUniverse (program.registers + 1)).meaning
              (CommonSignedRows.shiftOccurrence register.val Directed.allowNone 1 occurrence) at guard
            rw [back] at guard
            have nonzero := (positiveAt_point register values).mp guard
            have notEmpty : values register ≠ 0 := by omega
            apply absent.2
            refine ⟨CanonicalRegisterMachine.write values register (values register - 1),
              ((counter_transport_exact register values).2 nonzero).symm.trans moved, ?_⟩
            have continued := invariant.2 ⟨pc, values⟩ present
            simpa only [CanonicalRegisterMachine.step, current, notEmpty, ↓reduceIte] using continued

/-- The generated finite equations are satisfiable exactly for nonhalting
program inputs. There is no row-support, successful-solver, or invariant
premise in this theorem. -/
theorem constraints_iff_nonhalting (program : Program) (input : Nat) :
    (∃ assignment : Fin (program.states + program.states) → Common.Row,
      ProblemHolds (constraints program input) assignment) ↔
    ¬ CanonicalRegisterMachine.Halts program input := by
  constructor
  · rintro ⟨assignment, satisfied⟩
    exact (CanonicalRegisterMachine.invariant_iff_nonhalting program input).mp
      ⟨_, constraints_imply_invariant program input assignment satisfied⟩
  · intro nonhalting
    obtain ⟨safe, invariant⟩ := (CanonicalRegisterMachine.invariant_iff_nonhalting program input).mpr nonhalting
    exact invariant_has_constraints program input safe invariant

/-- A direct reduction to equality of the existing public-instance meaning.
Both interface inputs are finite symbolic syntax computed from the finite
counter program and the natural input. No EOF or role-resolution semantics
is used in this reduction. -/
theorem public_instances_iff_nonhalting (program : Program) (input : Nat) :
    (∀ theory : RoleConstraints.Theory model, ∀ target : Inference.Comp model,
      QualifiedInference.BindingTyping model theory
        (fixedInterface (constraints program input)).binding target ↔
      QualifiedInference.BindingTyping model theory
        (familyInterface (constraints program input)).binding target) ↔
    ¬ CanonicalRegisterMachine.Halts program input :=
  (problem_interfaces_exact (constraints program input)).trans (constraints_iff_nonhalting program input)

/-- No finite counter program recognizes equality on this compiled family
when fed the source representation. The explicit machine construction that
would compose a general interface encoder with the finite compiler is a
separate computational obligation. -/
theorem no_compiled_public_instance_semidecider
    (encoding : CanonicalRegisterMachine.Program → Nat) :
    ¬ ∃ recognizer : CanonicalRegisterMachine.Program,
      ∀ program : CanonicalRegisterMachine.Program,
        CanonicalRegisterMachine.Halts recognizer (encoding program) ↔
          (∀ theory : RoleConstraints.Theory model, ∀ target : Inference.Comp model,
            QualifiedInference.BindingTyping model theory
              (fixedInterface (constraints program (encoding program))).binding target ↔
            QualifiedInference.BindingTyping model theory
              (familyInterface (constraints program (encoding program))).binding target) := by
  rintro ⟨recognizer, exactness⟩
  apply CanonicalRegisterMachine.no_nonhalting_semidecider encoding
  exact ⟨recognizer, fun program =>
    (exactness program).trans (public_instances_iff_nonhalting program (encoding program))⟩

end Yulang.CommonCanonicalCounterConstraints
