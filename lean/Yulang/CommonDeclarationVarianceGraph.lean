import Yulang.CommonDeclarationVarianceRecursion

/-!
# Active source-position graph for declaration variance

Vertices retain BOTH the finite source position and the original parameter.
Reference edges retain that parameter; nominal edges enter the callee's
original formal. Consequently regular internal field-template recursion is
checked as well as named nominal recursion. No acyclic-reference assumption
is delegated to a caller.

Every edge is active: it carries an ordinarily used parameter. Immediate
edges stop at functions and enter a nominal actual only when the callee
formal has eager use. Ordinary edges retain dependencies under wrappers.
-/

namespace Yulang.CommonDeclarationVarianceGraph

open CommonDeclarationVarianceSyntax CommonDeclarationVarianceOccurrences CommonDeclarationVarianceCalls
open CommonDeclarationVarianceRecursion (Action)

variable {Index Parameter : Type} [DecidableEq Index] [DecidableEq Parameter]

abbrev Vertex (Index Parameter : Type) := Index × Parameter
abbrev State (Index Parameter : Type) := CommonDeclarationVarianceRecursion.State (Vertex Index Parameter)

inductive Transition (program : Program Index Parameter) (eager : Bool) :
    Expr Index Parameter → Parameter → Vertex Index Parameter → Prop where
  | reference : Used program false (program.body index) source →
      Transition program eager (.reference index) source (index, source)
  | first : Transition program eager first source target → Transition program eager (.both first last) source target
  | last : Transition program eager last source target → Transition program eager (.both first last) source target
  | negative : Transition program eager actual source target → Transition program eager (.negative actual) source target
  | barrier : eager = false → Transition program eager actual source target →
      Transition program eager (.barrier actual) source target
  | direct : Used program false (program.body (program.root formal)) formal →
      Used program false actual source →
      Transition program eager (.application formal actual) source (program.root formal, formal)
  | inside : Used program eager (program.body (program.root formal)) formal →
      Transition program eager actual source target → Transition program eager (.application formal actual) source target

def next (program : Program Index Parameter) (eager : Bool)
    (ordinary current : List (Fact Index Parameter)) (source : Parameter) :
    Expr Index Parameter → List (Vertex Index Parameter)
  | .empty | .parameter _ => []
  | .reference index => if used program false ordinary (program.body index) source then [(index, source)] else []
  | .both first last => next program eager ordinary current source first ++ next program eager ordinary current source last
  | .negative actual => next program eager ordinary current source actual
  | .barrier actual => if eager then [] else next program eager ordinary current source actual
  | .application formal actual =>
      (if used program false ordinary (program.body (program.root formal)) formal &&
          used program false ordinary actual source then [(program.root formal, formal)] else []) ++
      (if used program eager current (program.body (program.root formal)) formal then
        next program eager ordinary current source actual else [])

theorem next_exact (program : Program Index Parameter) (eager : Bool)
    (pool : Universe Index Parameter) (source : Parameter) (expression : Expr Index Parameter)
    (target : Vertex Index Parameter) :
    target ∈ next program eager (occurrences program false pool) (occurrences program eager pool) source expression ↔
      Transition program eager expression source target := by
  constructor
  · induction expression with
    | empty | parameter => simp [next]
    | reference index =>
        intro member
        unfold next at member
        split at member
        · rename_i active
          have same := List.mem_singleton.mp member
          subst target
          exact .reference ((used_exact _ _ _ _ _).mp active)
        · cases member
    | both first last ihFirst ihLast =>
        intro member
        exact (List.mem_append.mp member).elim
          (fun left => .first (ihFirst left)) (fun right => .last (ihLast right))
    | negative actual ih => exact fun member => .negative (ih member)
    | barrier actual ih =>
        cases eager
        · exact fun member => .barrier rfl (ih member)
        · simp [next]
    | application formal actual ih =>
        intro member
        rcases List.mem_append.mp member with direct | inner
        · split at direct
          · rename_i active
            simp only [Bool.and_eq_true] at active
            have same := List.mem_singleton.mp direct
            subst target
            exact .direct ((used_exact _ _ _ _ _).mp active.1) ((used_exact _ _ _ _ _).mp active.2)
          · cases direct
        · split at inner
          · rename_i active
            exact .inside ((used_exact _ _ _ _ _).mp active) (ih inner)
          · cases inner
  · intro transition
    induction transition with
    | reference used => simp [next, (used_exact _ _ _ _ _).mpr used]
    | first premise ih => exact List.mem_append_left _ ih
    | last premise ih => exact List.mem_append_right _ ih
    | negative premise ih => exact ih
    | barrier mode premise ih => simpa only [next, mode, Bool.false_eq_true, ↓reduceIte] using ih
    | direct callee actual =>
        apply List.mem_append_left
        simp [(used_exact _ _ _ _ _).mpr callee, (used_exact _ _ _ _ _).mpr actual]
    | inside active premise ih =>
        apply List.mem_append_right
        simpa only [(used_exact _ _ _ _ _).mpr active, ↓reduceIte] using ih

def vertexPool (pool : Universe Index Parameter) : Universe Unit (Vertex Index Parameter) where
  indices := [()]
  parameters := pool.indices.flatMap fun index => pool.parameters.map (index, ·)
  indices_complete := by intro index; cases index; simp
  parameters_complete := by intro ⟨index, parameter⟩; simp [pool.indices_complete, pool.parameters_complete]

inductive Reason (program : Program Index Parameter) : State Index Parameter → Prop where
  | reflexive (vertex : Vertex Index Parameter) : Reason program (.inl (vertex, vertex))
  | path : Transition program true (program.body first.1) first.2 middle →
      Reason program (.inl (middle, last)) → Reason program (.inl (first, last))
  | cycle : Transition program true (program.body first.1) first.2 target →
      Reason program (.inl (target, first)) → Reason program (.inr first)
  | mixed : Derivation program false (program.body vertex.1) vertex.2 false →
      Derivation program false (program.body vertex.1) vertex.2 true → Reason program (.inr vertex)
  | propagate : Transition program false (program.body first.1) first.2 target →
      Reason program (.inr target) → Reason program (.inr first)

structure Cache (Index Parameter : Type) where
  ordinary : List (Fact Index Parameter)
  eager : List (Fact Index Parameter)

def cache (program : Program Index Parameter) (pool : Universe Index Parameter) : Cache Index Parameter :=
  ⟨occurrences program false pool, occurrences program true pool⟩

def enabled (program : Program Index Parameter) (stored : Cache Index Parameter) : Action (Vertex Index Parameter) → Bool
  | .reflexive _ => true
  | .path first target _ | .cycle first target =>
      decide (target ∈ next program true stored.ordinary stored.eager first.2 (program.body first.1))
  | .mixed vertex => decide ((vertex.1, vertex.2, false) ∈ stored.ordinary) &&
      decide ((vertex.1, vertex.2, true) ∈ stored.ordinary)
  | .propagate first target =>
      decide (target ∈ next program false stored.ordinary stored.ordinary first.2 (program.body first.1))

def emit (program : Program Index Parameter) (stored : Cache Index Parameter) (action : Action (Vertex Index Parameter)) :
    List (FiniteHorn.Rule (State Index Parameter)) := if enabled program stored action then [action.rule] else []

def rules (program : Program Index Parameter) (stored : Cache Index Parameter) (pool : Universe Index Parameter) :
    List (FiniteHorn.Rule (State Index Parameter)) :=
  (CommonDeclarationVarianceRecursion.actions (vertexPool pool)).flatMap (emit program stored)

theorem rule_member (program : Program Index Parameter) (stored : Cache Index Parameter)
    (pool : Universe Index Parameter) (action : Action (Vertex Index Parameter))
    (active : enabled program stored action = true) : action.rule ∈ rules program stored pool := by
  apply List.mem_flatMap.mpr
  exact ⟨action, CommonDeclarationVarianceRecursion.actions_complete (vertexPool pool) action,
    by simp [emit, active]⟩

theorem rules_sound (program : Program Index Parameter) (pool : Universe Index Parameter)
    (rule : FiniteHorn.Rule (State Index Parameter)) (member : rule ∈ rules program (cache program pool) pool) :
    FiniteHorn.Valid (Reason program) rule := by
  obtain ⟨action, _, listed⟩ := List.mem_flatMap.mp member
  unfold emit at listed
  split at listed
  · rename_i active
    have same : action.rule = rule := (List.mem_singleton.mp listed).symm
    subst rule
    intro valid
    cases action with
    | reflexive vertex => exact .reflexive _
    | path first next last =>
        exact .path ((next_exact _ _ _ _ _ _).mp (of_decide_eq_true active)) (valid _ List.mem_cons_self)
    | cycle first next =>
        exact .cycle ((next_exact _ _ _ _ _ _).mp (of_decide_eq_true active)) (valid _ List.mem_cons_self)
    | mixed vertex =>
        simp only [enabled, cache, Bool.and_eq_true] at active
        exact .mixed ((occurrences_exact _ _ _ _ _ _).mp (of_decide_eq_true active.1))
          ((occurrences_exact _ _ _ _ _ _).mp (of_decide_eq_true active.2))
    | propagate first next =>
        exact .propagate ((next_exact _ _ _ _ _ _).mp (of_decide_eq_true active)) (valid _ List.mem_cons_self)
  · cases listed

theorem horn_exact (program : Program Index Parameter) (pool : Universe Index Parameter) (state : State Index Parameter) :
    FiniteHorn.Derives (rules program (cache program pool) pool) state ↔ Reason program state := by
  constructor
  · exact FiniteHorn.Derives.sound (rules_sound program pool)
  · intro derived
    have applyAction : ∀ action, enabled program (cache program pool) action = true →
        (∀ premise ∈ action.rule.premises, FiniteHorn.Derives (rules program (cache program pool) pool) premise) →
        FiniteHorn.Derives (rules program (cache program pool) pool) action.rule.conclusion := by
      intro action active premises
      exact .applyRule action.rule (rule_member _ _ _ _ active) premises
    induction derived with
    | reflexive vertex => apply applyAction (.reflexive vertex) rfl; simp [Action.rule]
    | @path first next last called path ih =>
        apply applyAction (.path first next last)
        · exact decide_eq_true ((next_exact _ _ _ _ _ _).mpr called)
        · intro premise member; exact (List.mem_singleton.mp member) ▸ ih
    | @cycle first next called path ih =>
        apply applyAction (.cycle first next)
        · exact decide_eq_true ((next_exact _ _ _ _ _ _).mpr called)
        · intro premise member; exact (List.mem_singleton.mp member) ▸ ih
    | @mixed vertex positive negative =>
        apply applyAction (.mixed vertex)
        · simp only [enabled, cache, Bool.and_eq_true]
          exact ⟨decide_eq_true ((occurrences_exact _ _ _ _ _ _).mpr positive),
            decide_eq_true ((occurrences_exact _ _ _ _ _ _).mpr negative)⟩
        · simp [Action.rule]
    | @propagate first next called blocked ih =>
        apply applyAction (.propagate first next)
        · exact decide_eq_true ((next_exact _ _ _ _ _ _).mpr called)
        · intro premise member; exact (List.mem_singleton.mp member) ▸ ih

def analyze (program : Program Index Parameter) (pool : Universe Index Parameter) : List (State Index Parameter) :=
  let stored := cache program pool
  FiniteHorn.saturate (rules program stored pool) (CommonDeclarationVarianceRecursion.states (vertexPool pool))

theorem analyze_exact (program : Program Index Parameter) (pool : Universe Index Parameter) (state : State Index Parameter) :
    state ∈ analyze program pool ↔ Reason program state :=
  (FiniteHorn.saturate_exact _ _ (CommonDeclarationVarianceRecursion.states_complete (vertexPool pool)) _).trans
    (horn_exact _ _ _)

end Yulang.CommonDeclarationVarianceGraph
