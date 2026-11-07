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

/-- For unique-head programs, finite Common evidence (including the overlap
check) exists exactly when the original finite tree program halts. The goal
is a finite unit/pair tree; semantic substitutions remain unrestricted. -/
theorem evidence_iff_halting (program : Program) (valid : Valid program) (input : Data) :
    Evidence (compile program) (encodeTree input) ↔ Halts program input := by
  have ordinary (assignment : Nat → Common.Ty) (pattern : Pattern) :
      interpret assignment pattern.toTerm = some (pattern.eval assignment) := by
    induction pattern <;> simp_all [interpret, Pattern.toTerm, Pattern.eval]
  have evaluated (assignment : Nat → Data) (pattern : Pattern) :
      pattern.eval (fun name => encodeTree (assignment name)) =
        encodeTree (pattern.instantiate assignment) := by
    induction pattern <;> simp_all [Pattern.eval, Pattern.instantiate, encodeTree]
  have uniqueHead (rule : Rule) (member : rule ∈ program) (input : Data)
      (matched : rule.Matches input) : Unique (compile program) (compileRule rule) (encodeTree input) := by
    intro other inside otherMatch
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp inside
    exact congrArg compileRule (valid.2 input original rule originalMember member
      ((compiled_matches_iff original input).mp otherMatch) matched)
  constructor
  · intro evidence
    have reflect (value : Common.Ty) (trace : Evidence (compile program) value) :
        ∀ tree, Common.Equivalent value (encodeTree tree) → Halts program tree := by
      induction trace with
      | done rule assignment head value member headIs same unique noChildren =>
          intro tree treeSame
          obtain ⟨original, inside, rfl⟩ := List.mem_map.mp member
          have sourceSame := (compiled_head_iff original assignment _).mp
            ⟨head, headIs, Common.equivalent_trans same treeSame⟩
          obtain ⟨replacement, matchedSource, _⟩ := pattern_match_reflects original.source
            original.source assignment tree (fun _ absent => absent) sourceSame
          cases original with
          | mk source action =>
            cases action with
            | halt answer =>
                rw [← matchedSource]
                exact ⟨answer, .halt ⟨source, .halt answer⟩ replacement inside rfl⟩
            | next target => simp [compileRule, declaration] at noChildren
      | next rule assignment head value child term member headIs same unique oneChild childIs rest ih =>
          intro tree treeSame
          obtain ⟨original, inside, rfl⟩ := List.mem_map.mp member
          have sourceSame := (compiled_head_iff original assignment _).mp
            ⟨head, headIs, Common.equivalent_trans same treeSame⟩
          have wf := valid.1 original inside
          cases original with
          | mk source action =>
            cases action with
            | halt answer => simp [compileRule] at oneChild
            | next target =>
                obtain ⟨replacement, matchedSource, childSame⟩ := pattern_match_reflects source
                  target assignment tree wf sourceSame
                have termSame : target.toTerm = term := by
                  simpa [compileRule, declaration] using oneChild
                subst term
                have valueSame : target.eval assignment = child :=
                  Option.some.inj ((ordinary assignment target).symm.trans childIs)
                obtain ⟨answer, execution⟩ := ih (target.instantiate replacement) (valueSame ▸ childSame)
                rw [← matchedSource]
                exact ⟨answer, .next ⟨source, .next target⟩ replacement inside rfl execution⟩
    exact reflect _ evidence input (Common.equivalent_refl _)
  · rintro ⟨answer, execution⟩
    induction execution with
    | halt rule assignment member stopped =>
        have sourceSame : Common.Equivalent
            (rule.source.eval (fun name => encodeTree (assignment name)))
            (encodeTree (rule.source.instantiate assignment)) := by
          rw [evaluated]
          exact Common.equivalent_refl _
        obtain ⟨head, headIs, same⟩ := (compiled_head_iff rule _ _).mpr sourceSame
        exact .done (compileRule rule) _ head _
          (List.mem_map.mpr ⟨rule, member, rfl⟩) headIs same
          (uniqueHead rule member _ ⟨assignment, rfl⟩) (by simp [compileRule, stopped])
    | @next target answer rule assignment member moved rest ih =>
        have sourceSame : Common.Equivalent
            (rule.source.eval (fun name => encodeTree (assignment name)))
            (encodeTree (rule.source.instantiate assignment)) := by
          rw [evaluated]
          exact Common.equivalent_refl _
        obtain ⟨head, headIs, same⟩ := (compiled_head_iff rule _ _).mpr sourceSame
        apply Evidence.next (compileRule rule) _ head _ _ target.toTerm
          (List.mem_map.mpr ⟨rule, member, rfl⟩) headIs same
          (uniqueHead rule member _ ⟨assignment, rfl⟩)
          (by simp [compileRule, moved, declaration]) _ ih
        rw [ordinary, evaluated]

/-- Explicit finite serialization. No predicate, resolver, quotient choice,
or proof is embedded in the input supplied to a decision program. -/
def encodeNat : Nat → Data
  | 0 => .nil
  | n + 1 => .cons .nil (encodeNat n)

mutual
  def encodeTerm : Roles.Term → Data
    | .var name => .cons .nil (encodeNat name)
    | .app constructor arguments => .cons (.cons .nil (encodeNat constructor)) (encodeTerms arguments)
  def encodeTerms : List Roles.Term → Data
    | [] => .nil
    | first :: rest => .cons (encodeTerm first) (encodeTerms rest)
end

def encodeGoal (goal : Roles.Goal) : Data := .cons (encodeNat goal.role) (encodeTerms goal.args)

def encodeList (encode : α → Data) : List α → Data
  | [] => .nil
  | first :: rest => .cons (encode first) (encodeList encode rest)

def encodeDeclaration (rule : Roles.Impl) : Data :=
  .cons (encodeNat rule.key) (.cons (encodeNat rule.role)
    (.cons (encodeTerms rule.head) (encodeList encodeGoal rule.constraints)))

def registryInput (program : Program) : Data := encodeList encodeDeclaration (compile program)

/-- No valid finite root-pattern program decides semantic evidence for all
these checked finite registries. The queried type is the unit/pair encoding
of the registry's own finite serialization. This is a reduction theorem for
the explicit root-pattern computation model, not yet A2 E2. -/
theorem no_compiled_evidence_decider :
    ¬ ∃ decider : Program, Valid decider ∧
      (∀ program, Valid program → ∃ answer, Runs decider (registryInput program) answer) ∧
      (∀ program, Valid program →
        (Runs decider (registryInput program) true ↔
          Evidence (compile program) (encodeTree (registryInput program))) ∧
        (Runs decider (registryInput program) false ↔
          ¬ Evidence (compile program) (encodeTree (registryInput program)))) := by
  rintro ⟨decider, valid, total, correct⟩
  apply CanonicalRewriteComputability.no_self_halting_decider registryInput
  refine ⟨decider, valid, total, ?_⟩
  intro program validProgram
  simpa only [evidence_iff_halting program validProgram] using correct program validProgram

end Yulang.CommonRoleRewrite
