import Yulang.CommonRoleScalarDictionaryModels

/-!
# Ordinary-state scalar registries

Arbitrary finite visible lists of actual int/str leaf declarations. The caller
supplies neither a solved assignment nor a chosen candidate. The ordinary
solver checks consistency before the paired-atom materializer and the existing
dictionary elaborator run. Unsupported materialization remains pending in this
adapter, not a claim about complete language knownness. No where, associated
equations, regular types, or general B4 source instance are added here.
-/
namespace Yulang.CommonRoleScalarRegistry
open CommonRoleScalarDictionaryModels (Scalar declaration goal)
open CommonRoleSettledConstraints (State)
open CommonRoleOrdinaryKnownness (materialize)
open RoleDictionaries (Plan Answer Dictionary)
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All)

structure Entry where
  role : Nat
  key : Nat
  scalar : Scalar
  deriving DecidableEq, Repr

def Entry.impl (entry : Entry) : Roles.Impl :=
  declaration entry.role entry.key entry.scalar

def visible (entries : List Entry) : List Roles.Impl := entries.map Entry.impl

theorem wellFormed (entries : List Entry) : Roles.WellFormed (visible entries) := by
  intro implementation member
  obtain ⟨entry, _, rfl⟩ := List.mem_map.mp member
  simp [Entry.impl, declaration, Roles.Impl.WellFormed]

theorem leaf (entries : List Entry) (implementation : Roles.Impl)
    (member : implementation ∈ visible entries) : implementation.constraints = [] := by
  obtain ⟨entry, _, rfl⟩ := List.mem_map.mp member
  rfl

/-- Candidate identity comes from the original source declaration, not its
position in the visible list. -/
def Candidate (entries : List Entry) (role : Nat) (term : Roles.Term)
    (implementation : Roles.Impl) : Prop :=
  ∃ entry ∈ entries, entry.impl = implementation ∧ entry.role = role ∧ term = entry.scalar.term

theorem matches_entry (entry : Entry) (role : Nat) (term : Roles.Term) :
    Roles.Matches entry.impl (goal role term) ↔ entry.role = role ∧ term = entry.scalar.term := by
  obtain ⟨sourceRole, key, scalar⟩ := entry
  cases scalar <;> simp [Roles.Matches, Entry.impl, declaration, goal, Scalar.term,
    Roles.substArgs, Roles.Term.subst, eq_comm]
  all_goals intro _
  all_goals constructor
  all_goals first
    | exact fun ⟨_, ht⟩ => ht
    | exact fun ht => ⟨fun name => .var name, ht⟩

theorem candidate_exact (entries : List Entry) (role : Nat) (term : Roles.Term)
    (implementation : Roles.Impl) :
    implementation ∈ Roles.candidates (visible entries) (goal role term) ↔
      Candidate entries role term implementation := by
  rw [Roles.mem_candidates]
  constructor
  · rintro ⟨member, matched⟩
    change implementation ∈ entries.map Entry.impl at member
    obtain ⟨entry, origin, rfl⟩ := List.mem_map.mp member
    exact ⟨entry, origin, rfl, (matches_entry entry role term).mp matched⟩
  · rintro ⟨entry, member, rfl, matched⟩
    exact ⟨List.mem_map.mpr ⟨entry, member, rfl⟩, (matches_entry entry role term).mpr matched⟩

def Unique (entries : List Entry) (role : Nat) (term : Roles.Term)
    (implementation : Roles.Impl) : Prop :=
  Candidate entries role term implementation ∧
    ∀ other, Candidate entries role term other → other = implementation

theorem unique_exact (entries : List Entry) (role : Nat) (term : Roles.Term)
    (implementation : Roles.Impl) :
    Roles.candidates (visible entries) (goal role term) = [implementation] ↔
      Unique entries role term implementation := by
  constructor
  · intro unique
    constructor
    · exact (candidate_exact ..).mp (unique ▸ List.mem_singleton_self _)
    · intro other matched
      have member := (candidate_exact ..).mpr matched
      simpa [unique] using member
  · rintro ⟨matched, only⟩
    have member := (candidate_exact ..).mpr matched
    have nodup := Roles.candidates_nodup (visible entries) (goal role term)
    cases candidates : Roles.candidates (visible entries) (goal role term) with
    | nil => simp [candidates] at member
    | cons first rest =>
      have same : first = implementation := only first ((candidate_exact ..).mp (by simp [candidates]))
      subst first
      cases rest with
      | nil => rfl
      | cons second rest =>
        have secondSame : second = implementation := only second ((candidate_exact ..).mp (by simp [candidates]))
        subst second
        simp [candidates] at nodup

/-- A declaration-origin classifier independent of the resolver. No child
failure can be folded into root rejection because this fragment has no where. -/
inductive Ready (entries : List Entry) (role : Nat) (term : Roles.Term) : Answer → Prop where
  | rejected : (∀ implementation, ¬ Candidate entries role term implementation) →
      Ready entries role term .noImpl
  | ambiguous : Candidate entries role term first → Candidate entries role term second →
      first ≠ second → Ready entries role term .ambiguous
  | selected : Unique entries role term implementation →
      Ready entries role term (.resolved (.node implementation []))

theorem elaborate_selected (entries : List Entry) (role : Nat) (term : Roles.Term) (out : Plan) :
    RoleDictionaries.elaborate (visible entries) (wellFormed entries) (goal role term) = .resolved out ↔
      ∃ implementation, Unique entries role term implementation ∧ out = .node implementation [] := by
  rw [RoleDictionaries.elaborate_success_iff]
  constructor
  · rintro ⟨dictionary, erased⟩
    cases dictionary with
    | impl implementation unique children =>
      have member := (Roles.mem_candidates.mp (unique ▸ List.mem_singleton_self implementation)).1
      refine ⟨implementation, (unique_exact ..).mp unique, ?_⟩
      have empty := leaf entries implementation member
      have noChildren : (implementation.constraints.attach.map fun constraint =>
          (children constraint.val constraint.property).erase) = [] := by
        apply List.map_eq_nil_iff.mpr
        simpa using empty
      simpa only [RoleDictionaries.Dictionary.erase, noChildren] using erased.symm
  · rintro ⟨implementation, unique, rfl⟩
    have singleton := (unique_exact ..).mpr unique
    have member := (Roles.mem_candidates.mp (singleton ▸ List.mem_singleton_self implementation)).1
    have empty := leaf entries implementation member
    let dictionary : Dictionary (visible entries) (goal role term) :=
      .impl implementation singleton (fun constraint member => False.elim (by simp [empty] at member))
    exact ⟨dictionary, by simp [dictionary, RoleDictionaries.Dictionary.erase, empty]⟩


theorem resolve_leaf (entries : List Entry) (role : Nat) (term : Roles.Term) :
    Roles.resolve (visible entries) (wellFormed entries) (goal role term) =
      match Roles.candidates (visible entries) (goal role term) with
      | [] => .noImpl
      | [_] => .resolved
      | _ :: _ :: _ => .ambiguous := by
  cases candidates : Roles.candidates (visible entries) (goal role term) with
  | nil => exact Roles.resolve_none _ _ _ candidates
  | cons first rest =>
    cases rest with
    | nil =>
      rw [Roles.resolve_one _ _ _ first candidates]
      have member := (Roles.mem_candidates.mp (candidates ▸ List.mem_singleton_self first)).1
      simp [leaf entries first member, Roles.combine]
    | cons second rest => exact Roles.resolve_many _ _ _ first second rest candidates

theorem elaborate_rejected (entries : List Entry) (role : Nat) (term : Roles.Term) :
    RoleDictionaries.elaborate (visible entries) (wellFormed entries) (goal role term) = .noImpl ↔
      ∀ implementation, ¬ Candidate entries role term implementation := by
  rw [RoleDictionaries.elaborate_noImpl_iff, resolve_leaf]
  simp only [← candidate_exact]
  cases candidates : Roles.candidates (visible entries) (goal role term) with
  | nil => simp
  | cons first rest =>
    cases rest <;> constructor
    all_goals first
      | intro impossible; cases impossible
      | intro empty; exact False.elim (empty first (by simp))

theorem elaborate_ambiguous (entries : List Entry) (role : Nat) (term : Roles.Term) :
    RoleDictionaries.elaborate (visible entries) (wellFormed entries) (goal role term) = .ambiguous ↔
      ∃ first second, Candidate entries role term first ∧ Candidate entries role term second ∧
        first ≠ second := by
  rw [RoleDictionaries.elaborate_ambiguous_iff, resolve_leaf]
  have overlap : Roles.HeadOverlap (visible entries) (goal role term) ↔
      ∃ first second, Candidate entries role term first ∧ Candidate entries role term second ∧ first ≠ second := by
    rw [Roles.head_overlap_iff]
    constructor
    · rintro ⟨first, firstVisible, second, secondVisible, distinct, firstMatch, secondMatch⟩
      exact ⟨first, second, (candidate_exact ..).mp (Roles.mem_candidates.mpr ⟨firstVisible, firstMatch⟩),
        (candidate_exact ..).mp (Roles.mem_candidates.mpr ⟨secondVisible, secondMatch⟩), distinct⟩
    · rintro ⟨first, second, firstCandidate, secondCandidate, distinct⟩
      have firstMatch := Roles.mem_candidates.mp ((candidate_exact ..).mpr firstCandidate)
      have secondMatch := Roles.mem_candidates.mp ((candidate_exact ..).mpr secondCandidate)
      exact ⟨first, firstMatch.1, second, secondMatch.1, distinct, firstMatch.2, secondMatch.2⟩
  rw [← overlap]
  cases candidates : Roles.candidates (visible entries) (goal role term) with
  | nil => simp [Roles.HeadOverlap, candidates]
  | cons first rest => cases rest <;> simp [Roles.HeadOverlap, candidates]

/-- Soundness and completeness for each actual dictionary/diagnostic output. -/
theorem elaborate_exact (entries : List Entry) (role : Nat) (term : Roles.Term) (out : Answer) :
    RoleDictionaries.elaborate (visible entries) (wellFormed entries) (goal role term) = out ↔
      Ready entries role term out := by
  constructor
  · intro returned
    cases out with
    | resolved plan =>
      obtain ⟨implementation, unique, rfl⟩ := (elaborate_selected entries role term plan).mp returned
      exact .selected unique
    | noImpl => exact .rejected ((elaborate_rejected entries role term).mp returned)
    | ambiguous =>
      obtain ⟨first, second, hf, hs, distinct⟩ := (elaborate_ambiguous entries role term).mp returned
      exact .ambiguous hf hs distinct
  · intro derived
    cases derived with
    | rejected empty => exact (elaborate_rejected entries role term).mpr empty
    | ambiguous first second distinct => exact (elaborate_ambiguous entries role term).mpr ⟨_, _, first, second, distinct⟩
    | selected unique => exact (elaborate_selected entries role term _).mpr ⟨_, unique, rfl⟩

/-- Independent scalar evidence in original ordinary atoms. -/
def Known (state : State n) (receiver : Fin n) (term : Roles.Term) : Prop :=
  ∃ scalar : Scalar, CommonRoleOrdinaryKnownness.Evidence state.atoms receiver scalar.base ∧
    term = scalar.term

theorem materialize_exact (state : State n) (receiver : Fin n) (models : state.Models) (term : Roles.Term) :
    materialize state.atoms receiver = some term ↔ Known state receiver term := by
  obtain ⟨assignment, satisfies⟩ := models
  constructor
  · intro materialized
    obtain ⟨base, detected, encoded⟩ := Option.bind_eq_some_iff.mp materialized
    have evidence := CommonRoleOrdinaryKnownness.detect_evidence _ _ _ detected
    cases base with
    | int => exact ⟨.int, evidence, by simpa [CommonRoleOrdinaryKnownness.encode, Scalar.term] using encoded.symm⟩
    | str => exact ⟨.str, evidence, by simpa [CommonRoleOrdinaryKnownness.encode, Scalar.term] using encoded.symm⟩
    | bool => simp [CommonRoleOrdinaryKnownness.encode] at encoded
    | unit => simp [CommonRoleOrdinaryKnownness.encode] at encoded
  · rintro ⟨scalar, evidence, rfl⟩
    obtain ⟨base, detected⟩ := (CommonRoleOrdinaryKnownness.detect_exists _ _).mpr ⟨scalar.base, evidence⟩
    have same := CommonRoleOrdinaryKnownness.evidence_unique _ _ assignment satisfies base scalar.base
      (CommonRoleOrdinaryKnownness.detect_evidence _ _ _ detected) evidence
    subst base
    cases scalar <;> simp [materialize, detected, Scalar.base, Scalar.term, CommonRoleOrdinaryKnownness.encode]

inductive Outcome where
  | pending
  | ready (answer : Answer)
  deriving Repr

/-- The classifier never invokes the ordinary solver, materializer, candidate
enumerator, or dictionary elaborator. -/
inductive Classify (entries : List Entry) (role : Nat) (receiver : Fin n) (state : State n) : Outcome → Prop where
  | pending : (∀ term, ¬ Known state receiver term) → Classify entries role receiver state .pending
  | ready : Known state receiver term → Ready entries role term answer →
      Classify entries role receiver state (.ready answer)

def run (entries : List Entry) (role : Nat) (receiver : Fin n) (state : State n) : Option Outcome :=
  if CommonRoleOpenPropagation.consistent state then
    some (match materialize state.atoms receiver with
      | none => .pending
      | some term => .ready (RoleDictionaries.elaborate (visible entries) (wellFormed entries) (goal role term)))
  else none

/-- Soundness/completeness: all states, receiver slots, registries and results.
Consistency and independent classification are conclusions, not caller inputs.
No-supported-evidence pending is narrower than general language knownness. -/
theorem run_exact (entries : List Entry) (role : Nat) (receiver : Fin n) (state : State n) (out : Outcome) :
    run entries role receiver state = some out ↔ state.Models ∧ Classify entries role receiver state out := by
  unfold run
  by_cases consistent : CommonRoleOpenPropagation.consistent state = true
  · have models := (CommonRoleOpenPropagation.consistent_exact state).mp consistent
    simp only [consistent, ↓reduceIte, Option.some.injEq, models, true_and]
    constructor
    · intro returned
      cases materialized : materialize state.atoms receiver with
      | none =>
        simp only [materialized] at returned
        subst out
        exact .pending (fun term known => by
          have found := (materialize_exact state receiver models term).mpr known
          rw [materialized] at found
          cases found)
      | some term =>
        simp only [materialized] at returned
        subst out
        exact .ready ((materialize_exact state receiver models term).mp materialized)
          ((elaborate_exact entries role term _).mp rfl)
    · intro derived
      cases derived with
      | pending unknown =>
        have absent : materialize state.atoms receiver = none := by
          cases found : materialize state.atoms receiver with
          | none => rfl
          | some term => exact False.elim (unknown term ((materialize_exact state receiver models term).mp found))
        simp [absent]
      | @ready term answer known classified =>
        rw [(materialize_exact state receiver models term).mpr known]
        exact congrArg Outcome.ready ((elaborate_exact entries role term answer).mpr classified)
  · have absent : ¬ state.Models := fun models => consistent ((CommonRoleOpenPropagation.consistent_exact state).mpr models)
    simp [consistent, absent]


theorem scalar_term_injective (first last : Scalar) (equal : first.term = last.term) : first = last := by
  cases first <;> cases last <;> simp [Scalar.term] at equal ⊢

/-- All-model meaning of the actual selected leaf, with source identity and
all children (empty here) retained. No chosen solver model is privileged. -/
inductive Implements (entries : List Entry) (role : Nat) (argument : Common.Ty) : Plan → Prop where
  | leaf (entry : Entry) : entry ∈ entries → entry.role = role →
      Common.Equivalent argument (.base entry.scalar.base) →
      Implements entries role argument (.node entry.impl [])

/-- Soundness for every model of the original state, for arbitrary visible
scalar declarations and arbitrary returned plans. -/
theorem run_all_models (entries : List Entry) (role : Nat) (receiver : Fin n) (state : State n)
    (out : Plan) (returned : run entries role receiver state = some (.ready (.resolved out)))
    (assignment : Fin n → Comp Common.model) (models : All Common.model assignment state.atoms) :
    Implements entries role (assignment receiver).1 out := by
  obtain ⟨_, classified⟩ := (run_exact entries role receiver state _).mp returned
  cases classified with
  | ready known ready =>
    cases ready with
    | selected unique =>
      obtain ⟨entry, member, rfl, sameRole, sameTerm⟩ := unique.1
      obtain ⟨scalar, evidence, term⟩ := known
      have same : scalar = entry.scalar := scalar_term_injective _ _ (term.symm.trans sameTerm)
      rw [same] at evidence
      exact .leaf entry member sameRole
        (CommonRoleOrdinaryKnownness.evidence_models _ _ _ evidence assignment models)

/-- Exact success plus the semantic evidence for all original models. -/
theorem successful_dictionary_exact (entries : List Entry) (role : Nat)
    (receiver : Fin n) (state : State n) (out : Plan) :
    (run entries role receiver state = some (.ready (.resolved out)) ∧
      ∀ assignment : Fin n → Comp Common.model, All Common.model assignment state.atoms →
        Implements entries role (assignment receiver).1 out) ↔
      state.Models ∧ Classify entries role receiver state (.ready (.resolved out)) := by
  constructor
  · intro returned
    exact (run_exact entries role receiver state _).mp returned.1
  · intro classified
    have returned := (run_exact entries role receiver state _).mpr classified
    exact ⟨returned, run_all_models entries role receiver state out returned⟩

/-- The visible declaration set, not enumeration order or duplicate entries,
determines all four results and the literal selected dictionary payload. -/
theorem run_visible_set (first last : List Entry)
    (same : ∀ entry, entry ∈ first ↔ entry ∈ last) (role : Nat)
    (receiver : Fin n) (state : State n) : run first role receiver state = run last role receiver state := by
  have sameVisible : ∀ implementation, implementation ∈ visible first ↔ implementation ∈ visible last := by
    intro implementation
    simp only [visible, List.mem_map]
    constructor
    · rintro ⟨entry, member, equal⟩; exact ⟨entry, (same entry).mp member, equal⟩
    · rintro ⟨entry, member, equal⟩; exact ⟨entry, (same entry).mpr member, equal⟩
  unfold run
  split
  · cases materialized : materialize state.atoms receiver with
    | none => rfl
    | some term =>
      exact congrArg some (congrArg Outcome.ready
        (RoleDictionaries.elaborate_congr sameVisible (wellFormed first) (wellFormed last) (goal role term)))
  · rfl

theorem run_permutation (first last : List Entry) (permutation : first.Perm last)
    (role : Nat) (receiver : Fin n) (state : State n) :
    run first role receiver state = run last role receiver state :=
  run_visible_set first last (fun _ => permutation.mem_iff) role receiver state

theorem run_duplicate (entries : List Entry) (role : Nat) (receiver : Fin n) (state : State n) :
    run (entries ++ entries) role receiver state = run entries role receiver state :=
  run_visible_set _ _ (by simp) role receiver state

/-- Even a unique visible implementation cannot instantiate an unknown
receiver. Empty ordinary evidence stays pending for every registry. -/
theorem empty_pending (entries : List Entry) (role : Nat) (receiver : Fin n) :
    run entries role receiver State.empty = some .pending := by
  apply (run_exact entries role receiver State.empty _).mpr
  have models : (State.empty : State n).Models :=
    ⟨fun _ => Core.PresenceGeneration.Comp.pure Common.model .bottom, by intro atom member; cases member⟩
  exact ⟨models, .pending (by
    intro term known
    have impossible := (materialize_exact State.empty receiver models term).mpr known
    cases impossible)⟩

/-- An inconsistent ordinary state is unavailable, rather than silently
introducing an additional language-level rejection reason. -/
theorem inconsistent_unavailable (entries : List Entry) (role : Nat)
    (receiver : Fin n) (state : State n) (inconsistent : ¬ state.Models) :
    run entries role receiver state = none := by
  have no : CommonRoleOpenPropagation.consistent state ≠ true := fun yes =>
    inconsistent ((CommonRoleOpenPropagation.consistent_exact state).mp yes)
  simp [run, no]


/-- A recorded receiver equation flows through the real ordinary solver and
materializer, for every source registry, not a precomputed result table. -/
theorem run_recorded (entries : List Entry) (role : Nat) (receiver : Fin n) (scalar : Scalar) :
    run entries role receiver (CommonRoleCandidateStateFrontier.extend State.empty receiver scalar.base) =
      some (.ready (RoleDictionaries.elaborate (visible entries) (wellFormed entries) (goal role scalar.term))) := by
  let state := CommonRoleCandidateStateFrontier.extend State.empty receiver scalar.base
  have models : state.Models := by
    refine ⟨fun _ => Comp.pure Common.model (.base scalar.base), ?_⟩
    apply (CommonRoleCandidateStateFrontier.extend_exact ..).mpr
    exact ⟨(by intro atom member; cases member), Common.equivalent_refl _⟩
  have consistent := (CommonRoleOpenPropagation.consistent_exact state).mpr models
  have materialized : materialize state.atoms receiver = some scalar.term := by
    change materialize (CommonRoleCandidateStateFrontier.equality receiver scalar.base) receiver = _
    rw [materialize, CommonRoleOrdinaryKnownness.explicit_pair_detected]
    cases scalar <;> rfl
  change run entries role receiver state = _
  simp [run, consistent, materialized]

/-- Regression for the old target overlap: a known empty registry rejects;
an unknown empty registry stays pending by `empty_pending`. -/
theorem known_empty_rejected (role : Nat) (receiver : Fin n) (scalar : Scalar) :
    run [] role receiver (CommonRoleCandidateStateFrontier.extend State.empty receiver scalar.base) =
      some (.ready .noImpl) := by
  rw [run_recorded]
  have rejected := (elaborate_rejected [] role scalar.term).mpr (by
    intro implementation candidate
    obtain ⟨entry, member, _⟩ := candidate
    cases member)
  rw [rejected]

theorem recorded_singleton_selected (entry : Entry) (receiver : Fin n) :
    run [entry] entry.role receiver
      (CommonRoleCandidateStateFrontier.extend State.empty receiver entry.scalar.base) =
      some (.ready (.resolved (.node entry.impl []))) := by
  rw [run_recorded]
  have resolved := (CommonRoleScalarDictionaryModels.elaborate_exact entry.role entry.key entry.scalar
    entry.scalar.term (CommonRoleScalarDictionaryModels.plan entry.role entry.key entry.scalar)).mpr ⟨rfl, rfl⟩
  simpa only [visible, List.map_cons, List.map_nil, Entry.impl, CommonRoleScalarDictionaryModels.plan] using
    congrArg (fun answer => some (Outcome.ready answer)) resolved

/-- Distinct source declaration identities with the same scalar head remain
ambiguous, even though both individually construct valid dictionaries. -/
theorem recorded_overlap_ambiguous (role firstKey secondKey : Nat) (scalar : Scalar)
    (distinct : firstKey ≠ secondKey) (receiver : Fin n) :
    run [⟨role, firstKey, scalar⟩, ⟨role, secondKey, scalar⟩] role receiver
      (CommonRoleCandidateStateFrontier.extend State.empty receiver scalar.base) = some (.ready .ambiguous) := by
  rw [run_recorded]
  apply congrArg (fun answer => some (Outcome.ready answer))
  apply (elaborate_ambiguous _ role scalar.term).mpr
  refine ⟨declaration role firstKey scalar, declaration role secondKey scalar, ?_, ?_, ?_⟩
  · exact ⟨⟨role, firstKey, scalar⟩, by simp, rfl, rfl, rfl⟩
  · exact ⟨⟨role, secondKey, scalar⟩, by simp, rfl, rfl, rfl⟩
  · intro equal
    exact distinct (congrArg Roles.Impl.key equal)

end Yulang.CommonRoleScalarRegistry
