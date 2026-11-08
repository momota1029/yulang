import Yulang.CommonDeclarationVarianceOccurrences

/-!
# Active nominal calls, with exact function barriers

An immediate nominal call is relevant only if its actual argument carries
the original parameter and its formal is used by the callee. Descending
further into that actual argument requires the callee formal to be used in
the current traversal mode. In particular, a function wrapper inside the
callee blocks eager descent into a nested actual argument. The ordinary
mode retains these dependencies for propagation of invariant parameters.

The executable calculation translates source calls to positive equations
and reuses the proved finite saturation. `Calls` is an independent source
judgment referring only to original occurrence derivations.
-/

namespace Yulang.CommonDeclarationVarianceCalls

open CommonDeclarationVarianceSyntax CommonDeclarationVarianceOccurrences

variable {Index Parameter : Type} [DecidableEq Index] [DecidableEq Parameter]

def Used (program : Program Index Parameter) (eager : Bool)
    (expression : Expr Index Parameter) (parameter : Parameter) : Prop :=
  ∃ sign, Derivation program eager expression parameter sign

inductive Calls (program : Program Index Parameter) (eager : Bool) :
    Expr Index Parameter → Parameter → Parameter → Prop where
  | reference : Calls program eager (program.body index) source target →
      Calls program eager (.reference index) source target
  | first : Calls program eager first source target → Calls program eager (.both first last) source target
  | last : Calls program eager last source target → Calls program eager (.both first last) source target
  | negative : Calls program eager actual source target → Calls program eager (.negative actual) source target
  | barrier : eager = false → Calls program eager actual source target →
      Calls program eager (.barrier actual) source target
  | direct : Used program false (program.body (program.root formal)) formal →
      Used program false actual source → Calls program eager (.application formal actual) source formal
  | inside : Used program eager (program.body (program.root formal)) formal →
      Calls program eager actual source target → Calls program eager (.application formal actual) source target

def callSyntax (program : Program Index Parameter) (eager : Bool)
    (ordinary current : List (Fact Index Parameter)) (source : Parameter) :
    Expr Index Parameter → Expr Index Parameter
  | .empty | .parameter _ => .empty
  | .reference index => .reference index
  | .both first last => .both (callSyntax program eager ordinary current source first)
      (callSyntax program eager ordinary current source last)
  | .negative actual => callSyntax program eager ordinary current source actual
  | .barrier actual => if eager then .empty else callSyntax program eager ordinary current source actual
  | .application formal actual =>
      .both
        (if used program false ordinary (program.body (program.root formal)) formal &&
            used program false ordinary actual source then .parameter formal else .empty)
        (if used program eager current (program.body (program.root formal)) formal then
          callSyntax program eager ordinary current source actual else .empty)

def callProgram (program : Program Index Parameter) (eager : Bool)
    (pool : Universe Index Parameter) (source : Parameter) : Program Index Parameter where
  body index := callSyntax program eager (occurrences program false pool) (occurrences program eager pool)
    source (program.body index)
  root := program.root

private theorem call_support_sound (program : Program Index Parameter) (eager : Bool)
    (pool : Universe Index Parameter) (source : Parameter) (holds : Fact Index Parameter → Prop)
    (sound : ∀ index target sign, holds (index, target, sign) →
      Calls program eager (program.body index) source target)
    (expression : Expr Index Parameter) (target : Parameter) (sign : Bool) :
    Supports (callProgram program eager pool source) false holds
      (callSyntax program eager (occurrences program false pool) (occurrences program eager pool)
        source expression) target sign → Calls program eager expression source target := by
  induction expression with
  | empty | parameter => exact False.elim
  | reference index => exact fun supported => .reference (sound index target sign supported)
  | both first last ihFirst ihLast =>
      intro supported
      exact supported.elim (fun left => .first (ihFirst left)) (fun right => .last (ihLast right))
  | negative actual ih => exact fun supported => .negative (ih supported)
  | barrier actual ih =>
      cases eager
      · exact fun supported => .barrier rfl (ih supported)
      · exact False.elim
  | application formal actual ih =>
      intro supported
      change Supports _ _ _
        (.both (if _ then .parameter formal else .empty) (if _ then _ else .empty)) _ _ at supported
      rcases supported with direct | inner
      · split at direct
        · rename_i active
          simp only [Bool.and_eq_true] at active
          obtain ⟨callee, carried⟩ := active
          obtain ⟨same, _⟩ := direct
          subst target
          exact .direct ((used_exact _ _ _ _ _).mp callee) ((used_exact _ _ _ _ _).mp carried)
        · exact False.elim direct
      · split at inner
        · rename_i active
          exact .inside ((used_exact _ _ _ _ _).mp active) (ih inner)
        · exact False.elim inner

private theorem calls_supported (program : Program Index Parameter) (eager : Bool)
    (pool : Universe Index Parameter) (source : Parameter) (holds : Fact Index Parameter → Prop)
    (closed : ∀ index target, Supports (callProgram program eager pool source) false holds
      ((callProgram program eager pool source).body index) target false → holds (index, target, false))
    {expression : Expr Index Parameter} {target : Parameter}
    (called : Calls program eager expression source target) :
    Supports (callProgram program eager pool source) false holds
      (callSyntax program eager (occurrences program false pool) (occurrences program eager pool)
        source expression) target false := by
  induction called with
  | reference premise ih => exact closed _ _ (ih closed)
  | first premise ih => exact Or.inl (ih closed)
  | last premise ih => exact Or.inr (ih closed)
  | negative premise ih => exact ih closed
  | barrier mode premise ih => simpa only [callSyntax, mode, Bool.false_eq_true, ↓reduceIte] using ih closed
  | @direct formal actual source callee carried =>
      have callee' := (used_exact program false pool _ _).mpr callee
      have carried' := (used_exact program false pool _ _).mpr carried
      change Supports _ _ _ (.both _ _) _ _
      apply Or.inl
      simp only [callee', carried', Bool.and_self, ↓reduceIte, Supports, and_self]
  | @inside formal actual source target active premise ih =>
      have active' := (used_exact program eager pool _ _).mpr active
      change Supports _ _ _ (.both _ _) _ _
      apply Or.inr
      simpa only [active', ↓reduceIte] using ih closed

theorem call_horn_exact (program : Program Index Parameter) (eager : Bool)
    (pool : Universe Index Parameter) (source : Parameter) (index : Index) (target : Parameter) :
    FiniteHorn.Derives (rules (callProgram program eager pool source) false pool) (index, target, false) ↔
      Calls program eager (program.body index) source target := by
  constructor
  · intro derived
    apply FiniteHorn.Derives.sound (holds := fun fact =>
      Calls program eager (program.body fact.1) source fact.2.1) _ derived
    intro rule member valid
    obtain ⟨fact, _, listed⟩ := List.mem_flatMap.mp member
    unfold rulesAt at listed
    obtain ⟨premises, clauseMember, same⟩ := List.mem_map.mp listed
    subst rule
    apply call_support_sound program eager pool source
      (fun fact => Calls program eager (program.body fact.1) source fact.2.1)
      (fun _ _ _ premise => premise)
    exact (clauses_exact _ _ _ _ _ _).mp ⟨premises, clauseMember, valid⟩
  · intro called
    have closed : ∀ index target,
        Supports (callProgram program eager pool source) false
          (FiniteHorn.Derives (rules (callProgram program eager pool source) false pool))
          ((callProgram program eager pool source).body index) target false →
        FiniteHorn.Derives (rules (callProgram program eager pool source) false pool) (index, target, false) := by
      intro index target supported
      obtain ⟨premises, member, valid⟩ := (clauses_exact _ _ _ _ _ _).mpr supported
      exact .applyRule ⟨premises, (index, target, false)⟩ (rule_member _ _ _ _ _ member) valid
    exact closed _ _ (calls_supported _ _ _ _ _ closed called)

def callFacts (program : Program Index Parameter) (eager : Bool)
    (pool : Universe Index Parameter) (source : Parameter) : List (Fact Index Parameter) :=
  occurrences (callProgram program eager pool source) false pool

theorem call_facts_exact (program : Program Index Parameter) (eager : Bool)
    (pool : Universe Index Parameter) (source : Parameter) (index : Index) (target : Parameter) :
    (index, target, false) ∈ callFacts program eager pool source ↔
      Calls program eager (program.body index) source target :=
  (FiniteHorn.saturate_exact _ _ pool.facts_complete _).trans
    (call_horn_exact program eager pool source index target)

def edge (program : Program Index Parameter) (eager : Bool)
    (pool : Universe Index Parameter) (source target : Parameter) : Bool :=
  decide ((program.root source, target, false) ∈ callFacts program eager pool source)

theorem edge_exact (program : Program Index Parameter) (eager : Bool)
    (pool : Universe Index Parameter) (source target : Parameter) :
    edge program eager pool source target = true ↔
      Calls program eager (program.body (program.root source)) source target := by
  simp only [edge, decide_eq_true_eq, call_facts_exact]

end Yulang.CommonDeclarationVarianceCalls
