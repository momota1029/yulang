import Yulang.CommonDeclarationVarianceCalls

/-!
# Finite recursive-cost and invariant propagation

Only a nonempty cycle of active eager nominal calls seeds recursive
invariance. Both ordinary polarities also seed invariance. Invariance then
propagates along ordinary calls, including calls beneath function wrappers.
Thus wrapper creation stops eager scanning without making an invariant
callee argument covariant.

`Reason` is independent of emitted Horn rules and computed caches. Its paths
and invariant judgments mention the original source occurrence/call rules.
The finite calculation is exact for every original parameter identity.
-/

namespace Yulang.CommonDeclarationVarianceRecursion

open CommonDeclarationVarianceSyntax CommonDeclarationVarianceOccurrences CommonDeclarationVarianceCalls

variable {Index Parameter : Type} [DecidableEq Index] [DecidableEq Parameter]

def edges (program : Program Index Parameter) (eager : Bool) (pool : Universe Index Parameter) :
    List (Parameter × Parameter) :=
  pool.parameters.flatMap fun source =>
    let seen := callFacts program eager pool source
    (pool.parameters.filter fun target => decide ((program.root source, target, false) ∈ seen)).map (source, ·)

theorem edges_exact (program : Program Index Parameter) (eager : Bool)
    (pool : Universe Index Parameter) (source target : Parameter) :
    (source, target) ∈ edges program eager pool ↔
      Calls program eager (program.body (program.root source)) source target := by
  simp only [edges, List.mem_flatMap, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨first, _, last, ⟨_, present⟩, same⟩
    cases same
    exact (call_facts_exact _ _ _ _ _ _).mp present
  · intro called
    exact ⟨source, pool.parameters_complete source, target,
      ⟨pool.parameters_complete target, (call_facts_exact _ _ _ _ _ _).mpr called⟩, rfl⟩

structure Cache (Index Parameter : Type) where
  signs : List (Fact Index Parameter)
  eager : List (Parameter × Parameter)
  ordinary : List (Parameter × Parameter)

def cache (program : Program Index Parameter) (pool : Universe Index Parameter) : Cache Index Parameter :=
  ⟨occurrences program false pool, edges program true pool, edges program false pool⟩

abbrev State (Parameter : Type) := (Parameter × Parameter) ⊕ Parameter

inductive Reason (program : Program Index Parameter) : State Parameter → Prop where
  | reflexive (parameter : Parameter) : Reason program (.inl (parameter, parameter))
  | path : Calls program true (program.body (program.root first)) first middle →
      Reason program (.inl (middle, last)) → Reason program (.inl (first, last))
  | cycle : Calls program true (program.body (program.root first)) first next →
      Reason program (.inl (next, first)) → Reason program (.inr first)
  | mixed : Derivation program false (program.body (program.root parameter)) parameter false →
      Derivation program false (program.body (program.root parameter)) parameter true →
      Reason program (.inr parameter)
  | propagate : Calls program false (program.body (program.root first)) first next →
      Reason program (.inr next) → Reason program (.inr first)

inductive Action (Parameter : Type) where
  | reflexive : Parameter → Action Parameter
  | path : Parameter → Parameter → Parameter → Action Parameter
  | cycle : Parameter → Parameter → Action Parameter
  | mixed : Parameter → Action Parameter
  | propagate : Parameter → Parameter → Action Parameter

def actions (pool : Universe Index Parameter) : List (Action Parameter) :=
  pool.parameters.map Action.reflexive ++ pool.parameters.map Action.mixed ++
    pool.parameters.flatMap fun first => pool.parameters.flatMap fun next =>
      [.cycle first next, .propagate first next] ++ pool.parameters.map (.path first next)

omit [DecidableEq Index] [DecidableEq Parameter] in
theorem actions_complete (pool : Universe Index Parameter) (action : Action Parameter) :
    action ∈ actions pool := by
  cases action <;> simp [actions, pool.parameters_complete]

def Action.rule : Action Parameter → FiniteHorn.Rule (State Parameter)
  | .reflexive parameter => ⟨[], .inl (parameter, parameter)⟩
  | .path first next last => ⟨[.inl (next, last)], .inl (first, last)⟩
  | .cycle first next => ⟨[.inl (next, first)], .inr first⟩
  | .mixed parameter => ⟨[], .inr parameter⟩
  | .propagate first next => ⟨[.inr next], .inr first⟩

def enabled (program : Program Index Parameter) (stored : Cache Index Parameter) : Action Parameter → Bool
  | .reflexive _ => true
  | .path first next _ | .cycle first next => decide ((first, next) ∈ stored.eager)
  | .mixed parameter => decide ((program.root parameter, parameter, false) ∈ stored.signs) &&
      decide ((program.root parameter, parameter, true) ∈ stored.signs)
  | .propagate first next => decide ((first, next) ∈ stored.ordinary)

def emit (program : Program Index Parameter) (stored : Cache Index Parameter) (action : Action Parameter) :
    List (FiniteHorn.Rule (State Parameter)) := if enabled program stored action then [action.rule] else []

def rules (program : Program Index Parameter) (stored : Cache Index Parameter) (pool : Universe Index Parameter) :
    List (FiniteHorn.Rule (State Parameter)) := (actions pool).flatMap (emit program stored)

theorem rule_member (program : Program Index Parameter) (stored : Cache Index Parameter)
    (pool : Universe Index Parameter) (action : Action Parameter)
    (active : enabled program stored action = true) :
    action.rule ∈ rules program stored pool := by
  apply List.mem_flatMap.mpr
  exact ⟨action, actions_complete pool action, by simp [emit, active]⟩

theorem rules_sound (program : Program Index Parameter) (pool : Universe Index Parameter)
    (rule : FiniteHorn.Rule (State Parameter)) (member : rule ∈ rules program (cache program pool) pool) :
    FiniteHorn.Valid (Reason program) rule := by
  obtain ⟨action, _, listed⟩ := List.mem_flatMap.mp member
  unfold emit at listed
  split at listed
  · rename_i active
    have same : action.rule = rule := (List.mem_singleton.mp listed).symm
    subst rule
    intro valid
    cases action with
    | reflexive parameter => exact .reflexive _
    | path first next last =>
        exact .path ((edges_exact _ _ _ _ _).mp (of_decide_eq_true active))
          (valid _ List.mem_cons_self)
    | cycle first next =>
        exact .cycle ((edges_exact _ _ _ _ _).mp (of_decide_eq_true active))
          (valid _ List.mem_cons_self)
    | mixed parameter =>
        simp only [enabled, cache, Bool.and_eq_true] at active
        exact .mixed ((occurrences_exact _ _ _ _ _ _).mp (of_decide_eq_true active.1))
          ((occurrences_exact _ _ _ _ _ _).mp (of_decide_eq_true active.2))
    | propagate first next =>
        exact .propagate ((edges_exact _ _ _ _ _).mp (of_decide_eq_true active))
          (valid _ List.mem_cons_self)
  · simp only [List.not_mem_nil] at listed

theorem horn_exact (program : Program Index Parameter) (pool : Universe Index Parameter)
    (state : State Parameter) :
    FiniteHorn.Derives (rules program (cache program pool) pool) state ↔ Reason program state := by
  constructor
  · exact FiniteHorn.Derives.sound (rules_sound program pool)
  · intro derived
    have applyAction : ∀ action, enabled program (cache program pool) action = true →
        (∀ premise ∈ action.rule.premises,
          FiniteHorn.Derives (rules program (cache program pool) pool) premise) →
        FiniteHorn.Derives (rules program (cache program pool) pool) action.rule.conclusion := by
      intro action active premises
      exact .applyRule action.rule (rule_member _ _ _ _ active) premises
    induction derived with
    | reflexive parameter =>
        apply applyAction (.reflexive parameter) rfl
        simp [Action.rule]
    | @path first next last called path ih =>
        apply applyAction (.path first next last)
        · exact decide_eq_true ((edges_exact _ _ _ _ _).mpr called)
        · intro premise member
          have same := List.mem_singleton.mp member
          exact same ▸ ih
    | @cycle first next called path ih =>
        apply applyAction (.cycle first next)
        · exact decide_eq_true ((edges_exact _ _ _ _ _).mpr called)
        · intro premise member
          have same := List.mem_singleton.mp member
          exact same ▸ ih
    | @mixed parameter positive negative =>
        apply applyAction (.mixed parameter)
        · simp only [enabled, cache, Bool.and_eq_true]
          exact ⟨decide_eq_true ((occurrences_exact _ _ _ _ _ _).mpr positive),
            decide_eq_true ((occurrences_exact _ _ _ _ _ _).mpr negative)⟩
        · simp [Action.rule]
    | @propagate first next called blocked ih =>
        apply applyAction (.propagate first next)
        · exact decide_eq_true ((edges_exact _ _ _ _ _).mpr called)
        · intro premise member
          have same := List.mem_singleton.mp member
          exact same ▸ ih

def states (pool : Universe Index Parameter) : List (State Parameter) :=
  (pool.parameters.flatMap fun first => pool.parameters.map fun last => Sum.inl (first, last)) ++
    pool.parameters.map Sum.inr

omit [DecidableEq Index] [DecidableEq Parameter] in
theorem states_complete (pool : Universe Index Parameter) (state : State Parameter) :
    state ∈ states pool := by
  cases state with
  | inl pair => obtain ⟨first, last⟩ := pair; simp [states, pool.parameters_complete]
  | inr parameter => simp [states, pool.parameters_complete]

def analyze (program : Program Index Parameter) (pool : Universe Index Parameter) : List (State Parameter) :=
  let stored := cache program pool
  FiniteHorn.saturate (rules program stored pool) (states pool)

theorem analyze_exact (program : Program Index Parameter) (pool : Universe Index Parameter) (state : State Parameter) :
    state ∈ analyze program pool ↔ Reason program state :=
  (FiniteHorn.saturate_exact _ _ (states_complete pool) _).trans (horn_exact _ _ _)

end Yulang.CommonDeclarationVarianceRecursion
