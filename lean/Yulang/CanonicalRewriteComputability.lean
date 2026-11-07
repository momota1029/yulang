import Yulang.CommonRoleTreeReflection

/-!
# Finite root-pattern programs

This finite symbolic machine language is suitable for direct compilation to
role declarations. Valid programs have range-restricted children and unique
matching heads. These are independent syntactic/semantic validity conditions,
not termination assumptions. Execution is a finite inductive derivation.
-/

namespace Yulang.CanonicalRewriteComputability

open CanonicalComputability (Data)
open CommonRoleSemanticPadding (Pattern RangeRestricted)

inductive Action where
  | halt : Bool → Action
  | next : Pattern → Action
  deriving DecidableEq, Repr

structure Rule where
  source : Pattern
  action : Action
  deriving DecidableEq, Repr

abbrev Program := List Rule

def Rule.WellFormed (rule : Rule) : Prop :=
  match rule.action with
  | .halt _ => True
  | .next target => RangeRestricted rule.source target

def Rule.Matches (rule : Rule) (input : Data) : Prop :=
  ∃ assignment, rule.source.instantiate assignment = input

def Valid (program : Program) : Prop :=
  (∀ rule ∈ program, rule.WellFormed) ∧
  (∀ input first last, first ∈ program → last ∈ program →
    first.Matches input → last.Matches input → first = last)

inductive Runs (program : Program) : Data → Bool → Prop where
  | halt (rule : Rule) (assignment : Nat → Data) (member : rule ∈ program)
      (stopped : rule.action = .halt answer) :
      Runs program (rule.source.instantiate assignment) answer
  | next (rule : Rule) (assignment : Nat → Data) (member : rule ∈ program)
      (moved : rule.action = .next target)
      (rest : Runs program (target.instantiate assignment) answer) :
      Runs program (rule.source.instantiate assignment) answer

def Halts (program : Program) (input : Data) : Prop := ∃ answer, Runs program input answer

def divergeRule (rule : Rule) : Rule :=
  match rule.action with
  | .halt true => ⟨rule.source, .next rule.source⟩
  | _ => rule

def divergeOnTrue (program : Program) : Program := program.map divergeRule

/-- The actual finite transformation preserves range restriction and unique
heads; a true terminal becomes a self-loop with the same head. -/
theorem diverge_valid (program : Program) (valid : Valid program) :
    Valid (divergeOnTrue program) := by
  have sameSource (rule : Rule) : (divergeRule rule).source = rule.source := by
    cases rule with
    | mk source action => cases action with
      | halt answer => cases answer <;> rfl
      | next target => rfl
  constructor
  · intro rule member
    obtain ⟨original, inside, rfl⟩ := List.mem_map.mp member
    have wf := valid.1 original inside
    cases original with
    | mk source action => cases action with
      | halt answer =>
          cases answer with
          | false => trivial
          | true => exact fun _ absent => absent
      | next target => exact wf
  · intro input first last before after firstMatch lastMatch
    obtain ⟨originalFirst, memFirst, rfl⟩ := List.mem_map.mp before
    obtain ⟨originalLast, memLast, rfl⟩ := List.mem_map.mp after
    have firstMatches : originalFirst.Matches input := by
      simpa only [Rule.Matches, sameSource] using firstMatch
    have lastMatches : originalLast.Matches input := by
      simpa only [Rule.Matches, sameSource] using lastMatch
    exact congrArg divergeRule (valid.2 input _ _ memFirst memLast firstMatches lastMatches)

/-- This execution equivalence does not assume determinism or validity.
True terminals contribute only self-loops, never finite stopping traces. -/
theorem runs_diverge_iff (program : Program) (input : Data) (answer : Bool) :
    Runs (divergeOnTrue program) input answer ↔
      answer = false ∧ Runs program input false := by
  constructor
  · intro execution
    induction execution with
    | @halt answer rule assignment member stopped =>
        obtain ⟨original, inside, rfl⟩ := List.mem_map.mp member
        cases original with
        | mk source action =>
          cases action with
          | halt value =>
              cases value with
              | false =>
                  have answerFalse : answer = false := by
                    simpa [divergeRule] using stopped.symm
                  subst answer
                  exact ⟨rfl, .halt ⟨source, .halt false⟩ assignment inside rfl⟩
              | true => simp [divergeRule] at stopped
          | next target => simp [divergeRule] at stopped
    | next rule assignment member moved rest ih =>
        obtain ⟨original, inside, rfl⟩ := List.mem_map.mp member
        cases original with
        | mk source action =>
          cases action with
          | halt value =>
              cases value with
              | false => simp [divergeRule] at moved
              | true =>
                  have same := Action.next.inj moved
                  subst same
                  exact ih
          | next target =>
              have same := Action.next.inj moved
              subst same
              exact ⟨ih.1, .next ⟨source, .next target⟩ assignment inside rfl ih.2⟩
  · rintro ⟨rfl, execution⟩
    have preserve (input : Data) (answer : Bool) (trace : Runs program input answer) :
        answer = false → Runs (divergeOnTrue program) input answer := by
      induction trace with
      | @halt answer rule assignment member stopped =>
          intro answerFalse
          cases rule with
          | mk source action =>
            simp only at stopped
            subst action
            subst answer
            exact .halt ⟨source, .halt false⟩ assignment
              (List.mem_map.mpr ⟨⟨source, .halt false⟩, member, rfl⟩) rfl
      | next rule assignment member moved rest ih =>
          intro answerFalse
          cases rule with
          | mk source action =>
            simp only at moved
            subst action
            exact .next ⟨source, .next _⟩ assignment
              (List.mem_map.mpr ⟨⟨source, .next _⟩, member, rfl⟩) rfl (ih answerFalse)
    exact preserve input false execution rfl

/-- Even restricted to range-restricted programs with unique heads, no
valid finite root-rewrite program decides self-halting under any encoding.
Both return values are specified; no implicit deterministic interpreter is
assumed in this theorem. -/
theorem no_self_halting_decider (encoding : Program → Data) :
    ¬ ∃ decider : Program, Valid decider ∧
      (∀ program, Valid program → ∃ answer, Runs decider (encoding program) answer) ∧
      (∀ program, Valid program →
        (Runs decider (encoding program) true ↔ Halts program (encoding program)) ∧
        (Runs decider (encoding program) false ↔ ¬ Halts program (encoding program))) := by
  rintro ⟨decider, valid, total, correct⟩
  let diagonal := divergeOnTrue decider
  let input := encoding diagonal
  have validDiagonal : Valid diagonal := diverge_valid decider valid
  have diagonalExact : Halts diagonal input ↔ Runs decider input false := by
    simp only [Halts, diagonal, runs_diverge_iff, exists_eq_left]
  obtain ⟨answer, execution⟩ := total diagonal validDiagonal
  have specification := correct diagonal validDiagonal
  cases answer with
  | false => exact (specification.2.mp execution) (diagonalExact.mpr execution)
  | true =>
      have halted := specification.1.mp execution
      exact (specification.2.mp (diagonalExact.mp halted)) halted

end Yulang.CanonicalRewriteComputability
