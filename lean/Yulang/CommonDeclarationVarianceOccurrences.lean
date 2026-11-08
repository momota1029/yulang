import Yulang.CommonDeclarationVarianceSyntax

/-!
# Exact finite declaration occurrence analysis

The finite pool consists of source graph positions, original parameters
and the two polarities. Its size supplies the internal saturation capacity;
there is no declaration-depth cutoff, caller fuel or supplied variance table.
The result is equivalent to the independent source derivation, including
arbitrarily deep mutual recursion and nonlinear nominal argument nesting.
-/

namespace Yulang.CommonDeclarationVarianceOccurrences

open CommonDeclarationVarianceSyntax

variable {Index Parameter : Type} [DecidableEq Index] [DecidableEq Parameter]

structure Universe (Index Parameter : Type) where
  indices : List Index
  parameters : List Parameter
  indices_complete : ∀ index, index ∈ indices
  parameters_complete : ∀ parameter, parameter ∈ parameters

def Universe.facts (pool : Universe Index Parameter) : List (Fact Index Parameter) :=
  pool.indices.flatMap fun index => pool.parameters.flatMap fun parameter =>
    [(index, parameter, false), (index, parameter, true)]

omit [DecidableEq Index] [DecidableEq Parameter] in
theorem Universe.facts_complete (pool : Universe Index Parameter) (fact : Fact Index Parameter) :
    fact ∈ pool.facts := by
  obtain ⟨index, parameter, sign⟩ := fact
  apply List.mem_flatMap.mpr
  refine ⟨index, pool.indices_complete index, List.mem_flatMap.mpr ?_⟩
  refine ⟨parameter, pool.parameters_complete parameter, ?_⟩
  cases sign <;> simp

def rulesAt (program : Program Index Parameter) (eager : Bool) (fact : Fact Index Parameter) :
    List (FiniteHorn.Rule (Fact Index Parameter)) :=
  (clauses program eager (program.body fact.1) fact.2.1 fact.2.2).map fun premises => ⟨premises, fact⟩

def rules (program : Program Index Parameter) (eager : Bool) (pool : Universe Index Parameter) :
    List (FiniteHorn.Rule (Fact Index Parameter)) := pool.facts.flatMap (rulesAt program eager)

omit [DecidableEq Index] in
theorem rule_member (program : Program Index Parameter) (eager : Bool)
    (pool : Universe Index Parameter) (fact : Fact Index Parameter) (premises)
    (member : premises ∈ clauses program eager (program.body fact.1) fact.2.1 fact.2.2) :
    (⟨premises, fact⟩ : FiniteHorn.Rule _) ∈ rules program eager pool := by
  apply List.mem_flatMap.mpr
  exact ⟨fact, pool.facts_complete fact, List.mem_map.mpr ⟨premises, member, rfl⟩⟩

omit [DecidableEq Index] in
theorem rules_sound (program : Program Index Parameter) (eager : Bool)
    (pool : Universe Index Parameter) (rule : FiniteHorn.Rule (Fact Index Parameter))
    (member : rule ∈ rules program eager pool) :
    FiniteHorn.Valid (fun fact => Derivation program eager
      (program.body fact.1) fact.2.1 fact.2.2) rule := by
  obtain ⟨fact, _, listed⟩ := List.mem_flatMap.mp member
  unfold rulesAt at listed
  obtain ⟨premises, clauseMember, same⟩ := List.mem_map.mp listed
  subst rule
  intro valid
  apply supports_derivation program eager
    (fun fact => Derivation program eager (program.body fact.1) fact.2.1 fact.2.2)
    (fun _ _ _ premise => premise)
  exact (clauses_exact _ _ _ _ _ _).mp ⟨premises, clauseMember, valid⟩

omit [DecidableEq Index] in
theorem horn_exact (program : Program Index Parameter) (eager : Bool)
    (pool : Universe Index Parameter) (index : Index) (parameter : Parameter) (sign : Bool) :
    FiniteHorn.Derives (rules program eager pool) (index, parameter, sign) ↔
      Derivation program eager (program.body index) parameter sign := by
  constructor
  · intro derived
    exact FiniteHorn.Derives.sound (rules_sound program eager pool) derived
  · intro derived
    have closed : ∀ index parameter sign,
        Supports program eager (FiniteHorn.Derives (rules program eager pool))
          (program.body index) parameter sign →
        FiniteHorn.Derives (rules program eager pool) (index, parameter, sign) := by
      intro index parameter sign supported
      obtain ⟨premises, member, valid⟩ := (clauses_exact _ _ _ _ _ _).mpr supported
      exact .applyRule ⟨premises, (index, parameter, sign)⟩
        (rule_member _ _ _ _ _ member) valid
    exact closed index parameter sign (derived.supported _ _ _ closed)

def occurrences (program : Program Index Parameter) (eager : Bool)
    (pool : Universe Index Parameter) : List (Fact Index Parameter) :=
  FiniteHorn.saturate (rules program eager pool) pool.facts

theorem occurrences_exact (program : Program Index Parameter) (eager : Bool)
    (pool : Universe Index Parameter) (index : Index) (parameter : Parameter) (sign : Bool) :
    (index, parameter, sign) ∈ occurrences program eager pool ↔
      Derivation program eager (program.body index) parameter sign :=
  (FiniteHorn.saturate_exact _ _ pool.facts_complete _).trans
    (horn_exact program eager pool index parameter sign)

def expressionOccurs (program : Program Index Parameter) (eager : Bool)
    (seen : List (Fact Index Parameter)) (expression : Expr Index Parameter)
    (parameter : Parameter) (sign : Bool) : Bool :=
  (clauses program eager expression parameter sign).any fun premises =>
    premises.all fun fact => decide (fact ∈ seen)

theorem expression_occurs_exact (program : Program Index Parameter) (eager : Bool)
    (pool : Universe Index Parameter) (expression : Expr Index Parameter)
    (parameter : Parameter) (sign : Bool) :
    expressionOccurs program eager (occurrences program eager pool) expression parameter sign = true ↔
      Derivation program eager expression parameter sign := by
  have memberships : ∀ fact : Fact Index Parameter,
      fact ∈ occurrences program eager pool ↔
        Derivation program eager (program.body fact.1) fact.2.1 fact.2.2 := by
    intro ⟨index, parameter, sign⟩
    exact occurrences_exact _ _ _ _ _ _
  change ((clauses program eager expression parameter sign).any fun premises =>
    premises.all fun fact => decide (fact ∈ occurrences program eager pool)) = true ↔ _
  simp only [List.any_eq_true, List.all_eq_true, decide_eq_true_eq, memberships]
  change AnyClause (fun fact => Derivation program eager
    (program.body fact.1) fact.2.1 fact.2.2) (clauses program eager expression parameter sign) ↔ _
  rw [clauses_exact]
  constructor
  · exact supports_derivation _ _ _ (fun _ _ _ premise => premise) _ _ _
  · intro derived
    exact derived.supported _ _ _ (fun _ _ _ premise =>
      supports_derivation _ _ _ (fun _ _ _ fact => fact) _ _ _ premise)

def used (program : Program Index Parameter) (eager : Bool)
    (seen : List (Fact Index Parameter)) (expression : Expr Index Parameter) (parameter : Parameter) : Bool :=
  expressionOccurs program eager seen expression parameter false ||
    expressionOccurs program eager seen expression parameter true

theorem used_exact (program : Program Index Parameter) (eager : Bool)
    (pool : Universe Index Parameter) (expression : Expr Index Parameter) (parameter : Parameter) :
    used program eager (occurrences program eager pool) expression parameter = true ↔
      ∃ sign, Derivation program eager expression parameter sign := by
  rw [used, Bool.or_eq_true, expression_occurs_exact, expression_occurs_exact]
  constructor
  · intro derived
    exact derived.elim (fun positive => ⟨false, positive⟩) (fun negative => ⟨true, negative⟩)
  · rintro ⟨sign, derived⟩
    cases sign
    · exact Or.inl derived
    · exact Or.inr derived

theorem eager_function_unused (program : Program Index Parameter)
    (pool : Universe Index Parameter) (expression : Expr Index Parameter) (parameter : Parameter) :
    used program true (occurrences program true pool) (.barrier expression) parameter = false := by
  apply Bool.eq_false_iff.mpr
  intro present
  obtain ⟨sign, derived⟩ := (used_exact _ _ _ _ _).mp present
  cases derived with
  | barrier impossible _ => cases impossible

end Yulang.CommonDeclarationVarianceOccurrences
