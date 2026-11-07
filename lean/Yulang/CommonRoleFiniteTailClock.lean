import Yulang.CommonRoleNormalizedDeclarations

/-! A finite absorbing record clock with no explicit duplicate declaration
fields. Repeating independent clock slots in a pair skeleton supplies arbitrary
size slack while every record tail is just a variable. No union or recursive
type is used. The core declaration syntax already admits open record tails;
source annotation reachability is deliberately not asserted. -/

namespace Yulang.CommonRoleFiniteTailClock

open CommonRoleInspectedSemantics
open CommonRoleLinearClock (Rule Linear Ground)

def forkPattern : Nat → Pattern → Pattern
  | 0, _ => .int
  | count + 1, pattern => .pair pattern (forkPattern count pattern)

def forkDescription : Nat → Description → Description
  | 0, _ => .int
  | count + 1, type => .pair type (forkDescription count type)

def atom : Description := .record .int .empty
def clock (count : Nat) : Description := forkDescription count atom
def clockHead (count fresh : Nat) : Pattern := forkPattern count (.record .int (.var fresh))
def clockChild (count fresh : Nat) : Pattern := forkPattern count (.var fresh)

theorem fork_size (count : Nat) (pattern : Pattern) :
    (forkPattern count pattern).encode.size = count * (pattern.encode.size + 1) + 1 := by
  induction count <;> simp_all [forkPattern, Pattern.encode, Roles.Term.size, Roles.argsSize, Nat.add_mul] <;> omega

theorem fork_occurrences (count : Nat) (pattern : Pattern) (name : Nat) :
    (forkPattern count pattern).encode.occurrences name = count * pattern.encode.occurrences name := by
  induction count <;> simp_all [forkPattern, Pattern.encode, Roles.Term.occurrences, Roles.argsOccurrences,
    Nat.add_mul, Nat.add_comm]

theorem lift_normal (pattern : CommonRoleLinearClock.Pattern) : (liftPattern pattern).visible false = liftPattern pattern := by
  induction pattern <;> simp_all [liftPattern, Pattern.visible]

theorem clock_normal (count fresh : Nat) :
    (clockHead count fresh).visible false = clockHead count fresh ∧
      (clockChild count fresh).visible false = clockChild count fresh := by
  induction count <;> simp_all [clockHead, clockChild, forkPattern, Pattern.visible]

theorem fork_instantiate (count : Nat) (pattern : Pattern) (assignment : Nat → Description) :
    instantiate (forkPattern count pattern) assignment = forkDescription count (instantiate pattern assignment) := by
  induction count <;> simp_all [forkPattern, forkDescription, instantiate]

theorem fork_equivalent (count : Nat) (pattern : Pattern) (assignment : Nat → Common.Ty) (type : Description)
    (same : Common.Equivalent (pattern.eval assignment) type.eval) :
    Common.Equivalent ((forkPattern count pattern).eval assignment) (forkDescription count type).eval := by
  induction count with
  | zero => exact Common.equivalent_refl _
  | succ count ih => exact (CommonCanonicalShapes.pair_equivalent_iff _ _ _ _).mpr ⟨same, ih⟩

theorem atom_absorbs : Common.Equivalent (Common.record 0 (.base .int) atom.eval) atom.eval :=
  Common.common_shadowed_head_equivalent 0 (.base .int) (.base .int) Common.emptyRecord

theorem head_clock_matches (count fresh : Nat) (assignment : Nat → Description) (captured : assignment fresh = atom) :
    Common.Equivalent ((clockHead count fresh).eval (fun name => (assignment name).eval)) (clock count).eval := by
  apply fork_equivalent
  simpa [Pattern.eval, captured] using atom_absorbs

theorem clock_finite (count : Nat) : (clock count).finite = true := by
  induction count <;> simp_all [clock, forkDescription, atom, Description.finite]

def capacity : List Rule → Nat
  | [] => 1
  | rule :: rest => rule.right.encode.size + capacity rest

theorem capacity_positive (rules : List Rule) : 0 < capacity rules := by
  induction rules <;> simp_all [capacity] <;> omega

theorem member_below_capacity (rules : List Rule) (rule : Rule) (member : rule ∈ rules) :
    rule.right.encode.size < capacity rules := by
  induction rules with
  | nil => contradiction
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | member
      · have positive := capacity_positive rest; simp [capacity]; omega
      · have smaller := ih member; simp [capacity]; omega

def count (code : CommonRoleComputation.Code) : Nat := capacity (CommonRoleLinearProgram.rules code)

def headPattern (slots : Nat) (rule : Rule) : Pattern := .pair (clockHead slots rule.fresh) (liftPattern rule.left)
def childPattern (slots : Nat) (rule : Rule) : Pattern := .pair (clockChild slots rule.fresh) (liftPattern rule.right)

def compile (slots key : Nat) (rule : Rule) : Roles.Impl :=
  ⟨rule.source, [(headPattern slots rule).encode], [⟨rule.target, [(childPattern slots rule).encode]⟩], key⟩

def terminalImpl : Roles.Impl := ⟨0, [(Pattern.pair (.var 0) (.var 1)).encode], [], 0⟩

theorem compile_normal (slots key : Nat) (rule : Rule) :
    CommonRoleNormalizedDeclarations.normalizeImpl (compile slots key rule) = compile slots key rule := by
  simp [CommonRoleNormalizedDeclarations.normalizeImpl, CommonRoleNormalizedDeclarations.normalizeGoal,
    compile, headPattern, childPattern, Pattern.visible, (clock_normal slots rule.fresh).1,
    (clock_normal slots rule.fresh).2, lift_normal]

theorem compile_wellFormed (slots key : Nat) (rule : Rule) (large : rule.right.encode.size < slots)
    (linear : Linear rule) : (compile slots key rule).WellFormed := by
  intro child member
  have same : child = ⟨rule.target, [(childPattern slots rule).encode]⟩ := by simpa [compile] using member
  subst child
  constructor
  · simp [compile, headPattern, childPattern, clockHead, clockChild, fork_size,
      CommonRoleFiniteShadowRegistry.lift_size, Pattern.encode, Roles.Term.size, Roles.argsSize]
    omega
  · intro name
    have counts := linear name
    simp [compile, headPattern, childPattern, clockHead, clockChild, fork_occurrences,
      CommonRoleFiniteShadowRegistry.lift_occurrences, Pattern.encode, Roles.Term.occurrences, Roles.argsOccurrences]
    omega

theorem compiled_checked (slots key : Nat) (rule : Rule) (large : rule.right.encode.size < slots)
    (linear : Linear rule) : CommonRoleNormalizedDeclarations.checkImpl (compile slots key rule) = true := by
  have checked := (CheckedRoles.checkImpl_exact _).mpr (compile_wellFormed slots key rule large linear)
  unfold CommonRoleNormalizedDeclarations.checkImpl
  rw [compile_normal]
  simpa [CommonRoleNormalizedDeclarations.checkPatterns, compile] using checked

def assignment (rule : Rule) (finite : Nat → Ground) : Nat → Description :=
  fun name => if name = rule.fresh then atom else .ground (finite name)

theorem assignment_fresh (rule : Rule) (finite : Nat → Ground) : assignment rule finite rule.fresh = atom := by
  simp [assignment]

theorem assignment_finite (rule : Rule) (finite : Nat → Ground) (name : Nat) :
    (assignment rule finite name).finite = true := by
  by_cases same : name = rule.fresh <;> simp [assignment, same, atom, Description.finite]

theorem assignment_data (rule : Rule) (pattern : CommonRoleLinearClock.Pattern)
    (bound : pattern.encode.bound ≤ rule.fresh) (finite : Nat → Ground) :
    Common.Equivalent (pattern.eval (fun name => (assignment rule finite name).eval)) (pattern.instantiate finite).eval := by
  rw [CommonRoleLinearClock.instantiate_eval]
  apply CommonRoleLinearClock.Pattern.eval_congr
  intro name occurs
  have different : name ≠ rule.fresh := by
    intro same
    subst name
    have absent := pattern.encode.occurrences_above_bound rule.fresh bound
    omega
  simp [assignment, different, Description.eval, Common.equivalent_refl]

end Yulang.CommonRoleFiniteTailClock
