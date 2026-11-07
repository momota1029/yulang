import Yulang.CommonRoleRegularObstructions
import Yulang.CommonRigidHeadInspection

/-!
# Linear root rewriting with a regular role-resolution clock

The finite syntax below has only fixed, injective Common constructors.
An independent linear root rewrite rule is compiled to an actual `Roles.Impl`.
Its extra first argument is an unbounded regular clock; syntactic wrappers on
that argument make the real Paterson check pass without restricting rewrite
length. No associated-type body or arbitrary decoder is involved.
-/

namespace Yulang.CommonRoleLinearClock

open Common (Ty Equivalent)

inductive Pattern where
  | var : Nat → Pattern
  | int
  | pair : Pattern → Pattern → Pattern
  | variant : Nat → Pattern → Pattern
  deriving DecidableEq, Repr

inductive Ground where
  | int
  | pair : Ground → Ground → Ground
  | variant : Nat → Ground → Ground
  deriving DecidableEq, Repr

def Pattern.encode : Pattern → Roles.Term
  | .var name => .var name
  | .int => .app 0 []
  | .pair first last => .app 1 [first.encode, last.encode]
  | .variant tag payload => .app (2 + tag) [payload.encode]

def Ground.encode : Ground → Roles.Term
  | .int => .app 0 []
  | .pair first last => .app 1 [first.encode, last.encode]
  | .variant tag payload => .app (2 + tag) [payload.encode]

def Pattern.eval (assignment : Nat → Ty) : Pattern → Ty
  | .var name => assignment name
  | .int => .base .int
  | .pair first last => Common.pair (first.eval assignment) (last.eval assignment)
  | .variant tag payload => Common.variant tag (payload.eval assignment)

def Ground.eval : Ground → Ty
  | .int => .base .int
  | .pair first last => Common.pair first.eval last.eval
  | .variant tag payload => Common.variant tag payload.eval

def Pattern.instantiate (assignment : Nat → Ground) : Pattern → Ground
  | .var name => assignment name
  | .int => .int
  | .pair first last => .pair (first.instantiate assignment) (last.instantiate assignment)
  | .variant tag payload => .variant tag (payload.instantiate assignment)

theorem instantiate_encode (pattern : Pattern) (assignment : Nat → Ground) :
    (pattern.instantiate assignment).encode = pattern.encode.subst (fun name => (assignment name).encode) := by
  induction pattern <;> simp_all [Pattern.instantiate, Pattern.encode, Ground.encode,
    Roles.Term.subst, Roles.substArgs]

theorem instantiate_eval (pattern : Pattern) (assignment : Nat → Ground) :
    (pattern.instantiate assignment).eval = pattern.eval (fun name => (assignment name).eval) := by
  induction pattern <;> simp_all [Pattern.instantiate, Pattern.eval, Ground.eval]

structure Rule where
  source : Nat
  target : Nat
  left : Pattern
  right : Pattern
  deriving DecidableEq, Repr

def Linear (rule : Rule) : Prop :=
  ∀ name, rule.right.encode.occurrences name ≤ rule.left.encode.occurrences name

def checkLinear (rule : Rule) : Bool :=
  CheckedRoles.checkOccurrences [rule.left.encode] [rule.right.encode]

theorem checkLinear_exact (rule : Rule) : checkLinear rule = true ↔ Linear rule := by
  simpa [checkLinear, Linear, Roles.argsOccurrences] using
    CheckedRoles.checkOccurrences_exact [rule.left.encode] [rule.right.encode]

structure Configuration where
  role : Nat
  value : Ground
  deriving DecidableEq, Repr

def Rule.Step (rule : Rule) (source target : Configuration) : Prop :=
  ∃ assignment : Nat → Ground,
    source.role = rule.source ∧ target.role = rule.target ∧
    rule.left.instantiate assignment = source.value ∧
    rule.right.instantiate assignment = target.value

def Step (rules : List Rule) (source target : Configuration) : Prop :=
  ∃ rule ∈ rules, rule.Step source target

def wrapPattern : Nat → Pattern → Pattern
  | 0, pattern => pattern
  | count + 1, pattern => .variant 7 (wrapPattern count pattern)

theorem wrapPattern_size (count : Nat) (pattern : Pattern) :
    (wrapPattern count pattern).encode.size = count + pattern.encode.size := by
  induction count with
  | zero => simp [wrapPattern]
  | succ count ih => simp [wrapPattern, Pattern.encode, Roles.Term.size, Roles.argsSize, ih]; omega

theorem wrapPattern_occurrences (count : Nat) (pattern : Pattern) (name : Nat) :
    (wrapPattern count pattern).encode.occurrences name = pattern.encode.occurrences name := by
  induction count with
  | zero => rfl
  | succ count ih => simp [wrapPattern, Pattern.encode, Roles.Term.occurrences, Roles.argsOccurrences, ih]

def Rule.fresh (rule : Rule) : Nat := max rule.left.encode.bound rule.right.encode.bound
def Rule.padding (rule : Rule) : Nat := rule.right.encode.size + 1

def compile (key : Nat) (rule : Rule) : Roles.Impl :=
  ⟨rule.source, [(wrapPattern rule.padding (.var rule.fresh)).encode, rule.left.encode],
    [⟨rule.target, [.var rule.fresh, rule.right.encode]⟩], key⟩

theorem compile_wellFormed (key : Nat) (rule : Rule) (linear : Linear rule) :
    (compile key rule).WellFormed := by
  intro child member
  have equality : child = ⟨rule.target, [.var rule.fresh, rule.right.encode]⟩ := by
    simpa [compile] using member
  subst child
  constructor
  · simp only [compile, Roles.argsSize, wrapPattern_size, Pattern.encode, Roles.Term.size,
      Rule.padding, Nat.add_zero]
    omega
  · intro name
    have count := linear name
    simp only [compile, Roles.argsOccurrences, wrapPattern_occurrences, Pattern.encode, Nat.add_zero]
    omega

theorem compile_accepted (key : Nat) (rule : Rule) (linear : Linear rule) :
    CheckedRoles.checkImpl (compile key rule) = true :=
  (CheckedRoles.checkImpl_exact _).mpr (compile_wellFormed key rule linear)

/-- A designated terminal role accepts any clock and any machine value. -/
def terminalImpl (key terminal : Nat) : Roles.Impl :=
  ⟨terminal, [.var 0, .var 1], [], key⟩

theorem terminal_accepted (key terminal : Nat) :
    CheckedRoles.checkImpl (terminalImpl key terminal) = true := rfl

end Yulang.CommonRoleLinearClock
