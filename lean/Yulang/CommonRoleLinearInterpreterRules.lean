import Yulang.CommonRoleLinearInterpreter

/-! Finite linear root rules for the copying interpreter. -/

namespace Yulang.CommonRoleLinearInterpreterRules

open CommonRoleComputation (Tree Code Eval)
open CommonRoleLinearClock (Ground Pattern Rule Configuration Linear)
open CommonRoleLinearInterpreter (Kont Resume CopyKont State next)

def literal : Ground → Pattern
  | .int => .int
  | .pair first last => .pair (literal first) (literal last)
  | .variant tag value => .variant tag (literal value)

@[simp] theorem literal_instantiate (value : Ground) (assignment : Nat → Ground) :
    (literal value).instantiate assignment = value := by
  induction value <;> simp_all [literal, Pattern.instantiate]

@[simp] theorem literal_occurrences (value : Ground) (name : Nat) :
    (literal value).encode.occurrences name = 0 := by
  induction value <;> simp_all [literal, Pattern.encode, Roles.Term.occurrences, Roles.argsOccurrences]

private abbrev v0 : Pattern := .var 0
private abbrev v1 : Pattern := .var 1
private abbrev v2 : Pattern := .var 2
private abbrev v3 : Pattern := .var 3
private abbrev v4 : Pattern := .var 4
private abbrev v5 : Pattern := .var 5

def retHalt : Rule := ⟨2, 0, .pair v0 (.variant 0 .int), v0⟩
def retSeq : Rule :=
  ⟨2, 1, .pair v0 (.variant 1 (.pair v1 v2)), .pair v1 (.pair v0 v2)⟩
def retPairLeft : Rule :=
  ⟨2, 1, .pair v0 (.variant 2 (.pair v1 (.pair v2 v3))),
    .pair v1 (.pair v2 (.variant 3 (.pair v0 v3)))⟩
def retPairRight : Rule :=
  ⟨2, 2, .pair v0 (.variant 3 (.pair v1 v2)), .pair (.pair v1 v0) v2⟩
def retCondLeaf : Rule :=
  ⟨2, 1, .pair .int (.variant 4 (.pair v0 (.pair v1 (.pair v2 v3)))),
    .pair v0 (.pair v2 v3)⟩
def retCondNode : Rule :=
  ⟨2, 1, .pair (.pair v0 v1) (.variant 4 (.pair v2 (.pair v3 (.pair v4 v5)))),
    .pair v3 (.pair v4 v5)⟩
def retLoopLeaf : Rule :=
  ⟨2, 2, .pair .int (.variant 5 (.pair v0 (.pair v1 (.pair v2 v3)))), .pair v2 v3⟩
def retLoopNode : Rule :=
  ⟨2, 1, .pair (.pair v0 v1) (.variant 5 (.pair v2 (.pair v3 (.pair v4 v5)))),
    .pair v2 (.pair v4 (.variant 1 (.pair v3 v5)))⟩
def copyLeaf : Rule :=
  ⟨3, 4, .pair .int v0, .pair .int (.pair .int v0)⟩
def copyNode : Rule :=
  ⟨3, 3, .pair (.pair v0 v1) v2, .pair v0 (.variant 1 (.pair v1 v2))⟩
def copiedLeft : Rule :=
  ⟨4, 3, .pair v0 (.pair v1 (.variant 1 (.pair v2 v3))),
    .pair v2 (.variant 2 (.pair v0 (.pair v1 v3)))⟩
def copiedRight : Rule :=
  ⟨4, 4, .pair v0 (.pair v1 (.variant 2 (.pair v2 (.pair v3 v4)))),
    .pair (.pair v2 v0) (.pair (.pair v3 v1) v4)⟩
def copiedPair : Rule :=
  ⟨4, 1, .pair v0 (.pair v1 (.variant 0 (.variant 0 (.pair v2 (.pair v3 v4))))),
    .pair v2 (.pair v0 (.variant 2 (.pair v3 (.pair v1 v4))))⟩
def copiedCond : Rule :=
  ⟨4, 1, .pair v0 (.pair v1 (.variant 0 (.variant 1 (.pair v2 (.pair v3 (.pair v4 v5)))))),
    .pair v2 (.pair v0 (.variant 4 (.pair v3 (.pair v4 (.pair v1 v5)))))⟩
def copiedLoop : Rule :=
  ⟨4, 1, .pair v0 (.pair v1 (.variant 0 (.variant 2 (.pair v2 (.pair v3 (.pair v4 v5)))))),
    .pair v2 (.pair v0 (.variant 5 (.pair v3 (.pair v4 (.pair v1 v5)))))⟩

def genericRules : List Rule :=
  [retHalt, retSeq, retPairLeft, retPairRight, retCondLeaf, retCondNode,
    retLoopLeaf, retLoopNode, copyLeaf, copyNode, copiedLeft, copiedRight,
    copiedPair, copiedCond, copiedLoop]

theorem generic_linear : ∀ rule ∈ genericRules, Linear rule := by
  have checked : genericRules.all CommonRoleLinearClock.checkLinear = true := by decide +kernel
  intro rule member
  exact (CommonRoleLinearClock.checkLinear_exact rule).mp ((List.all_eq_true.mp checked) rule member)

/-- Program codes are constants in entry rules. Duplicating such constants is
permitted by linearity; only arbitrary substituted input/stack variables count. -/
def entryRules (code : Code) : List Rule :=
  let control := literal code.encode
  match code with
  | .const value => [⟨1, 2, .pair control (.pair v0 v1), .pair (literal value.encode) v1⟩]
  | .id => [⟨1, 2, .pair control (.pair v0 v1), .pair v0 v1⟩]
  | .left =>
      [⟨1, 2, .pair control (.pair .int v0), .pair .int v0⟩,
       ⟨1, 2, .pair control (.pair (.pair v0 v1) v2), .pair v0 v2⟩]
  | .right =>
      [⟨1, 2, .pair control (.pair .int v0), .pair .int v0⟩,
       ⟨1, 2, .pair control (.pair (.pair v0 v1) v2), .pair v1 v2⟩]
  | .pair first last =>
      [⟨1, 3, .pair control (.pair v0 v1),
        .pair v0 (.variant 0 (.variant 0 (.pair (literal first.encode)
          (.pair (literal last.encode) v1))))⟩]
  | .seq first last =>
      [⟨1, 1, .pair control (.pair v0 v1),
        .pair (literal first.encode) (.pair v0 (.variant 1 (.pair (literal last.encode) v1)))⟩]
  | .cond test yes no =>
      [⟨1, 3, .pair control (.pair v0 v1),
        .pair v0 (.variant 0 (.variant 1 (.pair (literal test.encode)
          (.pair (literal yes.encode) (.pair (literal no.encode) v1)))))⟩]
  | .whileE test body =>
      [⟨1, 3, .pair control (.pair v0 v1),
        .pair v0 (.variant 0 (.variant 2 (.pair (literal test.encode)
          (.pair (literal body.encode) (.pair control v1)))))⟩]

theorem entry_linear (code : Code) : ∀ rule ∈ entryRules code, Linear rule := by
  intro rule member
  cases code <;> simp only [entryRules, List.mem_cons, List.not_mem_nil, or_false] at member
  all_goals rcases member with rfl | rfl
  all_goals intro name
  all_goals simp only [Pattern.encode, Roles.Term.occurrences, Roles.argsOccurrences,
    literal_occurrences, Nat.add_zero, Nat.zero_add]
  all_goals omega

def assignment (values : List Ground) : Nat → Ground := fun name => (values[name]?).getD .int

/-- Every non-run transition of the typed machine is one actual linear rule
instance. The complete copying computation thus consists of ordinary rules. -/
theorem generic_step (state : State)
    (notRun : ∀ code input k, state ≠ .run code input k)
    (notHalted : ∀ input, state ≠ .halted input) :
    CommonRoleLinearClock.Step genericRules state.encode (next state).encode := by
  cases state with
  | run code input k => exact False.elim (notRun code input k rfl)
  | halted input => exact False.elim (notHalted input rfl)
  | ret input k =>
      cases k with
      | halt => exact ⟨retHalt, by simp [genericRules], assignment [input.encode], rfl, rfl, rfl, rfl⟩
      | seq code k => exact ⟨retSeq, by simp [genericRules], assignment [input.encode, code.encode, k.encode], rfl, rfl, rfl, rfl⟩
      | pairLeft code original k =>
          exact ⟨retPairLeft, by simp [genericRules], assignment [input.encode, code.encode, original.encode, k.encode],
            rfl, rfl, rfl, rfl⟩
      | pairRight first k =>
          exact ⟨retPairRight, by simp [genericRules], assignment [input.encode, first.encode, k.encode], rfl, rfl, rfl, rfl⟩
      | cond yes no original k =>
          cases input with
          | leaf => exact ⟨retCondLeaf, by simp [genericRules], assignment [yes.encode, no.encode, original.encode, k.encode], rfl, rfl, rfl, rfl⟩
          | node first last => exact ⟨retCondNode, by simp [genericRules], assignment [first.encode, last.encode, yes.encode, no.encode, original.encode, k.encode], rfl, rfl, rfl, rfl⟩
      | loop test body original k =>
          cases input with
          | leaf => exact ⟨retLoopLeaf, by simp [genericRules], assignment [body.encode, (Code.whileE test body).encode, original.encode, k.encode], rfl, rfl, rfl, rfl⟩
          | node first last => exact ⟨retLoopNode, by simp [genericRules], assignment [first.encode, last.encode, body.encode, (Code.whileE test body).encode, original.encode, k.encode], rfl, rfl, rfl, rfl⟩
  | copy input k =>
      cases input with
      | leaf => exact ⟨copyLeaf, by simp [genericRules], assignment [k.encode], rfl, rfl, rfl, rfl⟩
      | node first last => exact ⟨copyNode, by simp [genericRules], assignment [first.encode, last.encode, k.encode], rfl, rfl, rfl, rfl⟩
  | copied input k =>
      cases k with
      | left last k => exact ⟨copiedLeft, by simp [genericRules], assignment [input.encode, input.encode, last.encode, k.encode], rfl, rfl, rfl, rfl⟩
      | right first k => exact ⟨copiedRight, by simp [genericRules], assignment [input.encode, input.encode, first.encode, first.encode, k.encode], rfl, rfl, rfl, rfl⟩
      | done resume =>
          cases resume with
          | pair first last k => exact ⟨copiedPair, by simp [genericRules], assignment [input.encode, input.encode, first.encode, last.encode, k.encode], rfl, rfl, rfl, rfl⟩
          | cond test yes no k => exact ⟨copiedCond, by simp [genericRules], assignment [input.encode, input.encode, test.encode, yes.encode, no.encode, k.encode], rfl, rfl, rfl, rfl⟩
          | loop test body k => exact ⟨copiedLoop, by simp [genericRules], assignment [input.encode, input.encode, test.encode, body.encode, (Code.whileE test body).encode, k.encode], rfl, rfl, rfl, rfl⟩

theorem entry_step (code : Code) (input : Tree) (k : Kont) :
    CommonRoleLinearClock.Step (entryRules code) (State.run code input k).encode
      (next (.run code input k)).encode := by
  cases code with
  | const value =>
      refine ⟨(entryRules (.const value))[0]'(by simp [entryRules]), by simp [entryRules],
        assignment [input.encode, k.encode], rfl, rfl, ?_, ?_⟩
      all_goals simp [entryRules, State.encode, next, Pattern.instantiate, assignment]
  | id =>
      exact ⟨(entryRules .id)[0], by simp [entryRules],
        assignment [input.encode, k.encode], rfl, rfl, rfl, rfl⟩
  | left =>
      cases input with
      | leaf => exact ⟨(entryRules .left)[0], by simp [entryRules], assignment [k.encode], rfl, rfl, rfl, rfl⟩
      | node first last => exact ⟨(entryRules .left)[1], by simp [entryRules], assignment [first.encode, last.encode, k.encode], rfl, rfl, rfl, rfl⟩
  | right =>
      cases input with
      | leaf => exact ⟨(entryRules .right)[0], by simp [entryRules], assignment [k.encode], rfl, rfl, rfl, rfl⟩
      | node first last => exact ⟨(entryRules .right)[1], by simp [entryRules], assignment [first.encode, last.encode, k.encode], rfl, rfl, rfl, rfl⟩
  | pair first last =>
      refine ⟨(entryRules (.pair first last))[0]'(by simp [entryRules]), by simp [entryRules],
        assignment [input.encode, k.encode], rfl, rfl, ?_, ?_⟩
      all_goals simp [entryRules, State.encode, next, CopyKont.encode, Resume.encode, Pattern.instantiate, assignment]
  | seq first last =>
      refine ⟨(entryRules (.seq first last))[0]'(by simp [entryRules]), by simp [entryRules],
        assignment [input.encode, k.encode], rfl, rfl, ?_, ?_⟩
      all_goals simp [entryRules, State.encode, next, Kont.encode, Pattern.instantiate, assignment]
  | cond test yes no =>
      refine ⟨(entryRules (.cond test yes no))[0]'(by simp [entryRules]), by simp [entryRules],
        assignment [input.encode, k.encode], rfl, rfl, ?_, ?_⟩
      all_goals simp [entryRules, State.encode, next, CopyKont.encode, Resume.encode, Pattern.instantiate, assignment]
  | whileE test body =>
      refine ⟨(entryRules (.whileE test body))[0]'(by simp [entryRules]), by simp [entryRules],
        assignment [input.encode, k.encode], rfl, rfl, ?_, ?_⟩
      all_goals simp [entryRules, State.encode, next, CopyKont.encode, Resume.encode, Pattern.instantiate, assignment]

end Yulang.CommonRoleLinearInterpreterRules
