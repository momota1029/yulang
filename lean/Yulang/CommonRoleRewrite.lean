import Yulang.CanonicalRewriteComputability

/-!
# Finite pattern programs and Common-interpreted unary role declarations

The declarations are actual `Roles.Impl` values checked by `checkImpl`.
The independent semantic judgments below interpret unit/pair/union by Common
and require unique heads before checking the one possible child. They are the
unary fragment of the proposed Common role semantics, not a claim that the
existing finite-tree resolver accepts semantic matching or regular inputs.
-/

namespace Yulang.CommonRoleRewrite

open CanonicalComputability (Data)
open CanonicalRewriteComputability (Rule Action Program Valid Runs Halts)
open CommonRoleSemanticPadding

def compileRule (rule : Rule) : Roles.Impl :=
  match rule.action with
  | .halt _ => ⟨0, [rule.source.toTerm], [], 0⟩
  | .next target => declaration rule.source target 0

def compile (program : Program) : List Roles.Impl := program.map compileRule

def HeadInterpretation (assignment : Nat → Common.Ty) (rule : Roles.Impl)
    (head : Common.Ty) : Prop :=
  rule.role = 0 ∧ ∃ term, rule.head = [term] ∧ interpret assignment term = some head

def Matches (rule : Roles.Impl) (input : Common.Ty) : Prop :=
  ∃ assignment head, HeadInterpretation assignment rule head ∧ Common.Equivalent head input

def Unique (registry : List Roles.Impl) (rule : Roles.Impl) (input : Common.Ty) : Prop :=
  ∀ other ∈ registry, Matches other input → other = rule

/-- Finite evidence with overlap excluded before child evaluation. Neither
this judgment nor its matching relation invokes a resolver or a fuel bound. -/
inductive Evidence (registry : List Roles.Impl) : Common.Ty → Prop where
  | done (rule : Roles.Impl) (assignment : Nat → Common.Ty) (head input : Common.Ty)
      (member : rule ∈ registry) (headIs : HeadInterpretation assignment rule head)
      (same : Common.Equivalent head input) (unique : Unique registry rule input)
      (noChildren : rule.constraints = []) : Evidence registry input
  | next (rule : Roles.Impl) (assignment : Nat → Common.Ty) (head input child : Common.Ty)
      (term : Roles.Term) (member : rule ∈ registry)
      (headIs : HeadInterpretation assignment rule head)
      (same : Common.Equivalent head input) (unique : Unique registry rule input)
      (oneChild : rule.constraints = [⟨0, [term]⟩])
      (childIs : interpret assignment term = some child)
      (rest : Evidence registry child) : Evidence registry input

/-- Every finite valid program compiles to declarations accepted by the
existing raw checker. Semantic matching is not asserted to be raw matching. -/
theorem compile_checked (program : Program) (valid : Valid program) :
    ∀ rule ∈ compile program, CheckedRoles.checkImpl rule = true := by
  intro rule member
  obtain ⟨original, inside, rfl⟩ := List.mem_map.mp member
  have wf := valid.1 original inside
  cases original with
  | mk source action =>
    cases action with
    | halt answer =>
        apply (CheckedRoles.checkImpl_exact _).mpr
        intro child absent
        simp [compileRule] at absent
    | next target => exact padded_declaration_accepted source target 0 wf

/-- A compiled head has exactly its unpadded source meaning, for every
Common substitution and every Common goal. -/
theorem compiled_head_iff (rule : Rule) (assignment : Nat → Common.Ty) (input : Common.Ty) :
    (∃ head, HeadInterpretation assignment (compileRule rule) head ∧
      Common.Equivalent head input) ↔ Common.Equivalent (rule.source.eval assignment) input := by
  have ordinary (pattern : Pattern) :
      interpret assignment pattern.toTerm = some (pattern.eval assignment) := by
    induction pattern <;> simp_all [interpret, Pattern.toTerm, Pattern.eval]
  cases rule with
  | mk source action =>
    cases action with
    | halt answer =>
        simp [HeadInterpretation, compileRule, ordinary]
    | next target =>
        obtain ⟨head, evaluated, same⟩ := padded_head_exact (target.weight + 1) source assignment
        simp only [compileRule, declaration, HeadInterpretation, true_and, List.singleton_inj]
        constructor
        · rintro ⟨chosen, ⟨term, termIs, denoted⟩, matchesInput⟩
          subst term
          have sameHead : head = chosen := Option.some.inj (evaluated.symm.trans denoted)
          subst chosen
          exact Common.equivalent_trans (Common.equivalent_symm same) matchesInput
        · intro matchesInput
          exact ⟨head, ⟨_, rfl, evaluated⟩, Common.equivalent_trans same matchesInput⟩

/-- Arbitrary Common matching substitutions cannot introduce additional
matches on finite-tree inputs. No validity premise is needed for a head. -/
theorem compiled_matches_iff (rule : Rule) (input : Data) :
    Matches (compileRule rule) (encodeTree input) ↔ rule.Matches input := by
  constructor
  · rintro ⟨assignment, head, headIs, same⟩
    have sourceSame := (compiled_head_iff rule assignment (encodeTree input)).mp ⟨head, headIs, same⟩
    obtain ⟨replacement, matchedSource, _⟩ := pattern_match_reflects rule.source rule.source
      assignment input (fun _ absent => absent) sourceSame
    exact ⟨replacement, matchedSource⟩
  · rintro ⟨replacement, matchedSource⟩
    have evaluated (pattern : Pattern) :
        pattern.eval (fun name => encodeTree (replacement name)) =
          encodeTree (pattern.instantiate replacement) := by
      induction pattern <;> simp_all [Pattern.eval, Pattern.instantiate, encodeTree]
    have sourceSame : Common.Equivalent
        (rule.source.eval (fun name => encodeTree (replacement name))) (encodeTree input) := by
      rw [evaluated, matchedSource]
      exact Common.equivalent_refl _
    obtain ⟨head, headIs, same⟩ := (compiled_head_iff rule _ _).mpr sourceSame
    exact ⟨_, head, headIs, same⟩

end Yulang.CommonRoleRewrite
