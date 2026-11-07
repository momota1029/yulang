import Yulang.CommonRoleLinearClock

/-! Injectivity and disjointness of the actual compiled role declarations. -/

namespace Yulang.CommonRoleLinearRepresentation

open CommonRoleLinearClock (Pattern Rule compile terminalImpl)

def decodePattern : Roles.Term → Option Pattern
  | .var name => some (.var name)
  | .app 0 [] => some .int
  | .app 1 [first, last] => do
      return .pair (← decodePattern first) (← decodePattern last)
  | .app (tag + 2) [payload] => do
      return .variant tag (← decodePattern payload)
  | _ => none

theorem decodePattern_encode (pattern : Pattern) : decodePattern pattern.encode = some pattern := by
  induction pattern with
  | var name => rfl
  | int => rfl
  | pair first last ihFirst ihLast => simp [Pattern.encode, decodePattern, ihFirst, ihLast]
  | variant tag payload ih =>
      simp [Pattern.encode, Nat.add_comm 2 tag, decodePattern, ih]

theorem pattern_encode_injective {first last : Pattern} (same : first.encode = last.encode) :
    first = last := by
  have decoded := congrArg decodePattern same
  rw [decodePattern_encode, decodePattern_encode] at decoded
  exact Option.some.inj decoded

/-- The actual Impl encoding preserves its declaration key and all four
source Rule fields, including the child target and the RHS pattern. -/
theorem compile_injective {firstKey lastKey : Nat} {first last : Rule}
    (same : compile firstKey first = compile lastKey last) :
    firstKey = lastKey ∧ first = last := by
  have keys : firstKey = lastKey := congrArg Roles.Impl.key same
  have sources : first.source = last.source := congrArg Roles.Impl.role same
  have heads := congrArg Roles.Impl.head same
  have leftEncoded : first.left.encode = last.left.encode :=
    (List.cons.inj (List.cons.inj heads).2).1
  have children := congrArg Roles.Impl.constraints same
  have child := (List.cons.inj children).1
  have targets : first.target = last.target := congrArg Roles.Goal.role child
  have arguments := congrArg Roles.Goal.args child
  have rightEncoded : first.right.encode = last.right.encode :=
    (List.cons.inj (List.cons.inj arguments).2).1
  have leftSame := pattern_encode_injective leftEncoded
  have rightSame := pattern_encode_injective rightEncoded
  refine ⟨keys, ?_⟩
  cases first
  cases last
  simp_all

theorem compile_entry_eq_iff (first last : Nat × Rule) :
    compile (first.1 + 1) first.2 = compile (last.1 + 1) last.2 ↔ first = last := by
  constructor
  · intro same
    obtain ⟨keys, rules⟩ := compile_injective same
    have indices : first.1 = last.1 := by omega
    exact Prod.ext indices rules
  · intro same
    cases same
    rfl

/-- The terminal declaration has no child; every compiled transition has
exactly one. Their identities cannot coincide, regardless of the keys. -/
theorem terminal_ne_compile (terminalKey terminal transitionKey : Nat) (rule : Rule) :
    terminalImpl terminalKey terminal ≠ compile transitionKey rule := by
  intro same
  have children := congrArg Roles.Impl.constraints same
  cases children

theorem compile_ne_terminal (transitionKey : Nat) (rule : Rule) (terminalKey terminal : Nat) :
    compile transitionKey rule ≠ terminalImpl terminalKey terminal :=
  fun same => terminal_ne_compile terminalKey terminal transitionKey rule same.symm

end Yulang.CommonRoleLinearRepresentation
