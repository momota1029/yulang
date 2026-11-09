import Yulang.CommonRoleFeedbackSupport
import Yulang.CommonRoleAssociatedDeclarationExact

/-! Exhaustive diagnostic search for self-supported finite feedback states.
This is NOT language resolution: existence, uniqueness, model inhabitation and
source-lowering completeness are not claimed. Decode uses canonical token order,
a finite-table implementation restriction, not a specification rejection rule. -/
namespace Yulang.CommonRoleSupportSearch
open CommonRoleMaterializedDomain CommonRoleSourceWorklist
open CommonRoleOpenProducer (Registry)
open CommonRoleSettledConstraints (State)
open CommonRoleAssociatedStateFlow (Request Computed)
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All)

def subsets : List α → List (List α)
  | [] => [[]]
  | x :: xs => subsets xs ++ (subsets xs).map (x :: ·)

/-- All finite token subsets are represented, canonically in universe order. -/
theorem filter_mem_subsets (p : α → Bool) (xs : List α) :
    xs.filter p ∈ subsets xs := by
  induction xs with
  | nil => simp [subsets]
  | cons x xs ih =>
    cases hx : p x <;> simp [subsets, hx, ih]

/-- Exhaustive enumeration terminates with exactly 2^k candidates before filtering. -/
theorem subsets_length (xs : List α) : (subsets xs).length = 2 ^ xs.length := by
  induction xs with
  | nil => simp [subsets]
  | cons x xs ih => simp [subsets, ih, Nat.pow_succ, Nat.mul_two]

theorem subset_of_mem_subsets {xs ys : List α} (h : ys ∈ subsets xs) : ys ⊆ xs := by
  induction xs generalizing ys with
  | nil => simpa [subsets] using h
  | cons x xs ih =>
    simp only [subsets, List.mem_append, List.mem_map] at h
    rcases h with h | ⟨zs, hz, rfl⟩
    · exact fun a ha => List.mem_cons_of_mem x (ih h ha)
    · intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem x (ih hz ha)

variable (registry : Registry) (root : SourceRequest n)
  (decode : List (Fin k) → State n) (emit : Node registry root → List (Fin k))

/-- Independent support equation, allowing non-monotone actual child generation. -/
def Supported (seen : List (Fin k)) : Prop :=
  ∀ i, i ∈ seen ↔ ∃ q, Reach registry root (decode seen) q ∧ i ∈ emit q

def active (seen : List (Fin k)) : List (Fin k) :=
  (saturate registry root (decode seen)).flatMap emit

def check (seen : List (Fin k)) : Bool :=
  (List.finRange k).all fun i => (seen.contains i == (active registry root decode emit seen).contains i)

theorem check_exact (seen : List (Fin k)) :
    check registry root decode emit seen = true ↔ Supported registry root decode emit seen := by
  simp only [check, List.all_eq_true]
  constructor
  · intro h i
    have eq := h i (List.mem_finRange i)
    have eq' : (i ∈ seen) ↔ i ∈ active registry root decode emit seen := by
      simpa using eq
    rw [eq']
    simp only [active, List.mem_flatMap, saturate_exact]
  · intro h i _
    have eq' : (i ∈ seen) ↔ i ∈ active registry root decode emit seen := by
      simpa only [active, List.mem_flatMap, saturate_exact] using h i
    simpa using eq'

def search : List (List (Fin k)) :=
  (subsets (List.finRange k)).filter (check registry root decode emit)

/-- Search is sound and complete for all canonical finite candidates. -/
theorem search_exact (seen : List (Fin k)) :
    seen ∈ search registry root decode emit ↔
      seen ∈ subsets (List.finRange k) ∧ Supported registry root decode emit seen := by
  simp only [search, List.mem_filter, check_exact]

/-- In particular every supported canonical representation of an arbitrary
finite token list is found. The decoder is evaluated on that representation. -/
theorem canonical_complete (seen : List (Fin k))
    (h : Supported registry root decode emit ((List.finRange k).filter (seen.contains ·))) :
    (List.finRange k).filter (seen.contains ·) ∈ search registry root decode emit :=
  (search_exact ..).mpr ⟨filter_mem_subsets _ _, h⟩

theorem search_capacity : (search registry root decode emit).length ≤ 2 ^ k := by
  calc
    _ ≤ (subsets (List.finRange k)).length := List.length_filter_le ..
    _ = 2 ^ k := by rw [subsets_length, List.length_finRange]

/-- Empty search means no self-supported canonical candidate, NOT a language error. -/
theorem empty_exact : search registry root decode emit = [] ↔
    ¬ ∃ seen, seen ∈ subsets (List.finRange k) ∧ Supported registry root decode emit seen := by
  rw [List.eq_nil_iff_forall_not_mem]
  simp only [search_exact]
  simp

/-- Every returned candidate has exactly the seed models satisfying all equations
of its FINAL reachable sources. No stale historical token assumption is required.
Receivers are fixed and table/emit are supplied; this is not full B4. -/
theorem models_exact (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (seed : State n) (table : Fin k → Request n)
    (seen : List (Fin k))
    (found : seen ∈ search registry root
      (CommonRoleAssociatedFeedback.decode env roles wf seed table) emit)
    (assignment : Fin n → Comp Common.model) :
    All Common.model assignment (CommonRoleAssociatedFeedback.decode env roles wf seed table seen).atoms ↔
      All Common.model assignment seed.atoms ∧
      ∀ q, Reach registry root (CommonRoleAssociatedFeedback.decode env roles wf seed table seen) q →
        ∀ i ∈ emit q, ∀ head, Computed env roles wf (table i) head →
          Common.Equivalent (assignment (table i).output).1 (.base head) := by
  have supported := ((search_exact ..).mp found).2
  rw [CommonRoleAssociatedFeedback.decode_models]
  constructor
  · rintro ⟨initial, equations⟩
    exact ⟨initial, fun q reach i member head computed =>
      equations i ((supported i).mpr ⟨q, reach, member⟩) head computed⟩
  · rintro ⟨initial, equations⟩
    refine ⟨initial, ?_⟩
    intro i member head computed
    obtain ⟨q, reach, emitted⟩ := (supported i).mp member
    exact equations q reach i emitted head computed

/-- Actual computed source-table adapter: every returned candidate has precisely
all declaration-computed equations of its finally reachable annotations.
All source nodes and annotations are quantified; no monotonicity/support certificate
is supplied by the caller. This is still a finite fixed-receiver fragment. -/
theorem source_models_exact (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (seed : State n)
    (annotations : Node registry root → List (Request n))
    (seen : List (Fin (CommonRoleSourceAssociatedAdapter.entries registry root annotations).length))
    (found : seen ∈ search registry root
      (CommonRoleAssociatedFeedback.decode env roles wf seed
        (CommonRoleSourceAssociatedAdapter.table registry root annotations))
      (CommonRoleSourceAssociatedAdapter.emit registry root annotations))
    (assignment : Fin n → Comp Common.model) :
    All Common.model assignment (CommonRoleAssociatedFeedback.decode env roles wf seed
      (CommonRoleSourceAssociatedAdapter.table registry root annotations) seen).atoms ↔
      All Common.model assignment seed.atoms ∧
      ∀ q, Reach registry root (CommonRoleAssociatedFeedback.decode env roles wf seed
        (CommonRoleSourceAssociatedAdapter.table registry root annotations) seen) q →
        ∀ r ∈ annotations q, ∀ head, Computed env roles wf r head →
          Common.Equivalent (assignment r.output).1 (.base head) := by
  rw [models_exact registry root _ env roles wf seed _ seen found assignment]
  constructor
  · rintro ⟨initial, equations⟩
    refine ⟨initial, ?_⟩
    intro q reach r member head computed
    obtain ⟨i, emitted, hi⟩ := CommonRoleSourceAssociatedAdapter.emitted_complete
      registry root annotations q r member
    subst r
    exact equations q reach i emitted head computed
  · rintro ⟨initial, equations⟩
    exact ⟨initial, fun q reach i emitted head computed => equations q reach _
      (CommonRoleSourceAssociatedAdapter.emitted_sound registry root annotations q i emitted)
      head computed⟩

/-- The final equation view is also exact against independent first-order
associated derivations, under the explicit associated well-formedness check. -/
theorem source_declarative_models_exact (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (seed : State n) (annotations : Node registry root → List (Request n))
    (seen : List (Fin (CommonRoleSourceAssociatedAdapter.entries registry root annotations).length))
    (found : seen ∈ search registry root
      (CommonRoleAssociatedFeedback.decode env roles wf seed
        (CommonRoleSourceAssociatedAdapter.table registry root annotations))
      (CommonRoleSourceAssociatedAdapter.emit registry root annotations))
    (assignment : Fin n → Comp Common.model) :
    All Common.model assignment (CommonRoleAssociatedFeedback.decode env roles wf seed
      (CommonRoleSourceAssociatedAdapter.table registry root annotations) seen).atoms ↔
      All Common.model assignment seed.atoms ∧
      ∀ q, Reach registry root (CommonRoleAssociatedFeedback.decode env roles wf seed
        (CommonRoleSourceAssociatedAdapter.table registry root annotations) seen) q →
        ∀ r ∈ annotations q, ∀ head,
          CommonRoleAssociatedDeclarationExact.DeclarativeComputed env roles r head →
          Common.Equivalent (assignment r.output).1 (.base head) := by
  rw [source_models_exact registry root env roles wf seed annotations seen found assignment]
  simp only [CommonRoleAssociatedDeclarationExact.computed_iff_declarative env roles wf awf]

end Yulang.CommonRoleSupportSearch
