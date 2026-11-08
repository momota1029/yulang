import Yulang.CommonRoleOrdinaryKnownness
import Yulang.FiniteHorn

/-! General finite source-graph associated saturation, not arbitrary B4.
The explicit source graph is an implementation restriction: dynamic where
expansion and its source provenance are not supplied by this module. No fuel,
model, successful result, or complete fact universe is a caller premise. -/
namespace Yulang.CommonRoleFiniteAssociatedClosure
open CommonRoleSettledConstraints (State)
open CommonRoleOrdinaryKnownness (Evidence)
open CommonRoleAssociatedStateFlow (Request Computed)

abbrev Fact (n : Nat) := Fin n × Inference.Base

def bases : List Inference.Base := [.int, .str, .bool, .unit]
def facts (n : Nat) : List (Fact n) :=
  (List.finRange n).flatMap fun slot => bases.map fun head => (slot, head)

theorem facts_complete (fact : Fact n) : fact ∈ facts n := by
  rcases fact with ⟨slot, head⟩
  cases head <;> simp [facts, bases]

theorem facts_length (n : Nat) : (facts n).length = 4 * n := by
  simp [facts, bases, List.length_flatMap, List.map_const', List.sum_replicate_nat, Nat.mul_comm]

structure Occurrence (n : Nat) where
  receiver : Fin n
  output : Fin n
  name : Nat
  template : Inference.Base → Roles.Goal

structure Source (n : Nat) where
  identity : Fin n → Nat
  occurrences : List (Occurrence n)

def request (q : Occurrence n) (head : Inference.Base) : Request n :=
  ⟨q.template head, q.name, q.output⟩

def seed (fact : Fact n) : FiniteHorn.Rule (Fact n) := ⟨[], fact⟩
def unary (input output : Fact n) : FiniteHorn.Rule (Fact n) := ⟨[input], output⟩

def initial (s : State n) : List (Fact n) :=
  (List.finRange n).flatMap fun slot =>
    (CommonRoleOrdinaryKnownness.candidates s.atoms slot).map fun head => (slot, head)

theorem initial_exact (s : State n) (slot : Fin n) (head : Inference.Base) :
    (slot, head) ∈ initial s ↔ Evidence s.atoms slot head := by
  simp [initial, CommonRoleOrdinaryKnownness.candidates_exact]

def identityRules (p : Source n) : List (FiniteHorn.Rule (Fact n)) :=
  (List.finRange n).flatMap fun source =>
    (List.finRange n).flatMap fun target =>
      if p.identity source = p.identity target then
        bases.map fun head => unary (source, head) (target, head)
      else []

def occurrenceRules (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (q : Occurrence n) :
    List (FiniteHorn.Rule (Fact n)) :=
  bases.filterMap fun head =>
    (CommonRoleAssociatedStateFlow.value env roles wf (request q head)).map fun output =>
      unary (q.receiver, head) (q.output, output)

def rules (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (p : Source n) (s : State n) :=
  (initial s).map seed ++ identityRules p ++ p.occurrences.flatMap (occurrenceRules env roles wf)

def saturate (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (p : Source n) (s : State n) : List (Fact n) :=
  FiniteHorn.saturate (rules env roles wf p s) (facts n)

/-- Independent source derivations: initial evidence, shared identity, and
actual associated declaration output. Does not mention the executable closure. -/
inductive Derives (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (p : Source n) (s : State n) : Fact n → Prop
  | initial {slot head} : Evidence s.atoms slot head → Derives env roles wf p s (slot, head)
  | identity {source target head} : p.identity source = p.identity target →
      Derives env roles wf p s (source, head) → Derives env roles wf p s (target, head)
  | associated {q head output} : q ∈ p.occurrences →
      Derives env roles wf p s (q.receiver, head) →
      Computed env roles wf (request q head) output →
      Derives env roles wf p s (q.output, output)

private theorem base_mem (head : Inference.Base) : head ∈ bases := by cases head <;> simp [bases]

private theorem identity_member (p : Source n) (source target : Fin n)
    (head : Inference.Base) (same : p.identity source = p.identity target) :
    unary (source, head) (target, head) ∈ identityRules p := by
  apply List.mem_flatMap.mpr
  refine ⟨source, by simp, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨target, by simp, ?_⟩
  simp only [same, ↓reduceIte]
  exact List.mem_map.mpr ⟨head, base_mem head, rfl⟩

private theorem occurrence_member (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (q : Occurrence n) (head output : Inference.Base)
    (computed : Computed env roles wf (request q head) output) :
    unary (q.receiver, head) (q.output, output) ∈ occurrenceRules env roles wf q := by
  apply List.mem_filterMap.mpr
  refine ⟨head, base_mem head, ?_⟩
  rw [(CommonRoleAssociatedStateFlow.value_exact ..).mpr computed]
  rfl

private theorem rules_valid (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (p : Source n) (s : State n) :
    ∀ rule ∈ rules env roles wf p s, FiniteHorn.Valid (Derives env roles wf p s) rule := by
  intro rule member premises
  rcases List.mem_append.mp member with earlier | assoc
  · rcases List.mem_append.mp earlier with init | identities
    · obtain ⟨fact, present, rfl⟩ := List.mem_map.mp init
      exact .initial ((initial_exact s fact.1 fact.2).mp present)
    · obtain ⟨source, _, member⟩ := List.mem_flatMap.mp identities
      obtain ⟨target, _, member⟩ := List.mem_flatMap.mp member
      split at member
      · rename_i same
        obtain ⟨head, _, rfl⟩ := List.mem_map.mp member
        exact .identity same (premises _ (by simp [unary]))
      · simp at member
  · obtain ⟨q, qmember, present⟩ := List.mem_flatMap.mp assoc
    obtain ⟨head, _, result⟩ := List.mem_filterMap.mp present
    obtain ⟨output, computed, rfl⟩ := Option.map_eq_some_iff.mp result
    exact .associated qmember (premises _ (by simp [unary]))
      ((CommonRoleAssociatedStateFlow.value_exact ..).mp computed)

/-- Soundness and completeness for every finite source graph and every old state.
This is not source-parser/B4 completeness: the source graph is explicit. -/
theorem saturate_exact (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (p : Source n) (s : State n) (fact : Fact n) :
    fact ∈ saturate env roles wf p s ↔ Derives env roles wf p s fact := by
  constructor
  · exact FiniteHorn.saturate_preserves _ _ _ (rules_valid env roles wf p s) fact
  · intro derived
    induction derived with
    | @initial slot head evidence =>
      apply FiniteHorn.saturate_closed _ _ facts_complete
      refine ⟨seed (slot, head), ?_, rfl, ?_⟩
      · apply List.mem_append_left
        apply List.mem_append_left
        exact List.mem_map.mpr ⟨_, (initial_exact ..).mpr evidence, rfl⟩
      · simp [seed]
    | @identity source target head same _ ih =>
      apply FiniteHorn.saturate_closed _ _ facts_complete
      refine ⟨unary (source, head) (target, head), ?_, rfl, ?_⟩
      · apply List.mem_append_left
        exact List.mem_append_right _ (identity_member p source target head same)
      · simpa [unary, saturate] using ih
    | @associated q head output member _ computed ih =>
      apply FiniteHorn.saturate_closed _ _ facts_complete
      refine ⟨unary (q.receiver, head) (q.output, output), ?_, rfl, ?_⟩
      · apply List.mem_append_right
        exact List.mem_flatMap.mpr ⟨q, member, occurrence_member env roles wf q head output computed⟩
      · simpa [unary, saturate] using ih

/-- At most four distinct head facts per source slot are inserted. -/
theorem saturate_capacity (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (p : Source n) (s : State n) :
    (saturate env roles wf p s).length ≤ 4 * n := by
  rw [← facts_length]
  exact FiniteHorn.saturate_length_le _ _ facts_complete

/-- No duplicate fact is appended, even on cyclic dependency graphs. -/
theorem saturate_nodup (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (p : Source n) (s : State n) :
    (saturate env roles wf p s).Nodup := FiniteHorn.saturate_nodup _ _

/-- All newly enabled associated obligations are closed in the final cache. -/
theorem associated_closed (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (p : Source n) (s : State n)
    (q : Occurrence n) (member : q ∈ p.occurrences) (head output : Inference.Base)
    (known : (q.receiver, head) ∈ saturate env roles wf p s)
    (computed : Computed env roles wf (request q head) output) :
    (q.output, output) ∈ saturate env roles wf p s :=
  (saturate_exact ..).mpr (.associated member ((saturate_exact ..).mp known) computed)

end Yulang.CommonRoleFiniteAssociatedClosure
