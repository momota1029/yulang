import Yulang.CommonRoleGuardedCandidates

/-! State-independent candidate-keyed equation metadata with re-evaluated guards.
A branch mask is explicit input, NOT a solver-produced choice. Conjoining active
records for an incompatible mask is not language typing. Fixed receivers and
supplied annotations remain restrictions; no feedback fixedpoint is computed. -/
namespace Yulang.CommonRoleGuardedEquations
open CommonRoleSettledSyntax CommonRoleOpenProducer
open CommonRoleMaterializedDomain
open CommonRoleSourceWorklist (Node nodes nodes_complete)
open CommonRoleSettledConstraints (State)
open CommonRoleAssociatedStateFlow (Request Computed)
open CommonRoleGuardedCandidates (collect Reach collect_exact)
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All)

variable (registry : Registry) (root : SourceRequest n)

abbrev Entry := Node registry root × Declaration × Request n

/-- No observation or branch mask occurs in the stored carrier. -/
def entries (annotations : Node registry root → Declaration → List (Request n)) :
    List (Entry registry root) :=
  (nodes registry root).flatMap fun q => registry.declarations.flatMap fun d =>
    (annotations q d).map fun r => (q, d, r)

theorem entries_exact (annotations : Node registry root → Declaration → List (Request n))
    (q : Node registry root) (d : Declaration) (r : Request n) :
    (q, d, r) ∈ entries registry root annotations ↔
      d ∈ registry.declarations ∧ r ∈ annotations q d := by
  simp only [entries, List.mem_flatMap, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨p, _, e, he, t, ht, hp, hd, hr⟩
    subst p; subst e; subst t
    exact ⟨he, ht⟩
  · rintro ⟨hd, hr⟩
    exact ⟨q, nodes_complete .., d, hd, r, hr, rfl, rfl, rfl⟩

/-- Independent successful candidate inspection. No uniqueness is claimed. -/
def Candidate (s : State n) (p : SourceRequest n) (d : Declaration) : Prop :=
  d.role = p.role ∧ ∃ lp hp,
    Inspect d.head (p.lower.eval s) (.hit lp) ∧
    Inspect d.head (p.upper.eval s) (.hit hp)

def candidate (s : State n) (p : SourceRequest n) (d : Declaration) : Bool :=
  (production [d] (p.eval s)).isSome

theorem candidate_exact (s : State n) (p : SourceRequest n) (d : Declaration) :
    candidate s p d = true ↔ Candidate s p d := by
  unfold candidate production scan hits trial Candidate
  simp only [SourceRequest.eval]
  by_cases same : d.role = p.role
  · simp only [same, ↓reduceIte, true_and]
    cases lo : inspect d.head (p.lower.eval s) <;>
      cases hi : inspect d.head (p.upper.eval s) <;>
      simp [scan, encode, lo, hi, ← inspect_exact]
  · simp [scan, same]

/-- Candidate source children agree with independent dual inspection, not
with the first successful declaration in the registry. -/
theorem candidate_children_exact (s : State n) (p c : SourceRequest n) (d : Declaration) :
    c ∈ CommonRoleGuardedCandidates.candidateNext d s p ↔
      Candidate s p d ∧ c ∈ CommonRoleSourceTemplateClosure.declarationChildren d p := by
  unfold CommonRoleGuardedCandidates.candidateNext production scan hits trial Candidate
  simp only [SourceRequest.eval]
  by_cases same : d.role = p.role
  · simp only [same, ↓reduceIte, true_and]
    cases lo : inspect d.head (p.lower.eval s) <;>
      cases hi : inspect d.head (p.upper.eval s) <;>
      simp [scan, encode, lo, hi, ← inspect_exact]
  · simp [scan, same]

variable (mask : SourceRequest n → Declaration → Bool) (observation : State n)

/-- Independent all-enabled-candidate path judgment. It refers to declarative
Inspect and source substitution, not executable production or Horn saturation. -/
inductive CandidatePath : Node registry root → Prop where
  | root : CandidatePath (CommonRoleSourceWorklist.rootNode registry root)
  | step : CandidatePath p → d ∈ registry.declarations → mask p.val d = true →
      Candidate observation p.val d →
      c.val ∈ CommonRoleSourceTemplateClosure.declarationChildren d p.val → CandidatePath c

theorem reach_iff_path (q : Node registry root) :
    Reach registry root mask observation q ↔ CandidatePath registry root mask observation q := by
  constructor
  · intro h
    induction h with
    | root => exact .root
    | @step p c _ edge ih =>
      obtain ⟨d, hd, hm, hc⟩ := edge
      obtain ⟨hit, child⟩ := (candidate_children_exact observation p.val c.val d).mp hc
      exact .step ih hd hm hit child
  · intro h
    induction h with
    | root => exact .root
    | @step p d c _ hd hm hit child ih =>
      exact .step ih ⟨d, hd, hm, (candidate_children_exact observation p.val c.val d).mpr ⟨hit,child⟩⟩

/-- Guard keeps both source provenance and candidate identity. -/
def Active (e : Entry registry root) : Prop :=
  Reach registry root mask observation e.1 ∧
    mask e.1.val e.2.1 = true ∧ Candidate observation e.1.val e.2.1

def active (e : Entry registry root) : Bool :=
  (collect registry root mask observation).contains e.1 &&
    mask e.1.val e.2.1 && candidate observation e.1.val e.2.1

theorem active_exact (e : Entry registry root) :
    active registry root mask observation e = true ↔ Active registry root mask observation e := by
  simp only [active, Bool.and_eq_true, List.contains_iff_mem, collect_exact, candidate_exact, Active]
  exact and_assoc

def activate (annotations : Node registry root → Declaration → List (Request n)) :
    List (Entry registry root) :=
  (entries registry root annotations).filter (active registry root mask observation)

theorem activate_exact (annotations : Node registry root → Declaration → List (Request n))
    (q : Node registry root) (d : Declaration) (r : Request n) :
    (q, d, r) ∈ activate registry root mask observation annotations ↔
      d ∈ registry.declarations ∧ r ∈ annotations q d ∧
      Reach registry root mask observation q ∧ mask q.val d = true ∧ Candidate observation q.val d := by
  simp only [activate, List.mem_filter, entries_exact, active_exact, Active]
  exact and_assoc

/-- Disabled records are retained in metadata for every future observation/mask. -/
theorem retained (annotations : Node registry root → Declaration → List (Request n))
    (q : Node registry root) (d : Declaration) (r : Request n)
    (hd : d ∈ registry.declarations) (hr : r ∈ annotations q d) :
    (q, d, r) ∈ entries registry root annotations :=
  (entries_exact registry root annotations q d r).mpr ⟨hd, hr⟩

variable (env : Roles.AssocEnv) (roles : Roles.RoleDecls) (wf : Roles.WellFormed env.cores)

def view (annotations : Node registry root → Declaration → List (Request n)) (seed : State n) : State n :=
  CommonRoleAssociatedBatch.run env roles wf
    ((activate registry root mask observation annotations).map fun e => e.2.2) seed

/-- Exact conditional equation view for all explicit masks and observations.
This is NOT a claim that view is a language solution or that it preserves its
own activation guards after narrowing. Inactive alternatives impose no equation. -/
theorem view_exact (annotations : Node registry root → Declaration → List (Request n))
    (seed : State n) (assignment : Fin n → Comp Common.model) :
    All Common.model assignment (view registry root mask observation env roles wf annotations seed).atoms ↔
      All Common.model assignment seed.atoms ∧
      ∀ q d, d ∈ registry.declarations → Reach registry root mask observation q →
        mask q.val d = true → Candidate observation q.val d →
        ∀ r ∈ annotations q d, ∀ head, Computed env roles wf r head →
          Common.Equivalent (assignment r.output).1 (.base head) := by
  rw [view, CommonRoleAssociatedBatch.run_models]
  constructor
  · rintro ⟨hs, he⟩
    refine ⟨hs, ?_⟩
    intro q d hd hq hm hc r hr head hh
    exact he r (List.mem_map.mpr ⟨(q,d,r),
      (activate_exact registry root mask observation annotations q d r).mpr ⟨hd,hr,hq,hm,hc⟩, rfl⟩)
      head hh
  · rintro ⟨hs, he⟩
    refine ⟨hs, ?_⟩
    intro r hr head hh
    obtain ⟨⟨q,d,t⟩, ht, rfl⟩ := List.mem_map.mp hr
    obtain ⟨hd, ht, hq, hm, hc⟩ := (activate_exact registry root mask observation annotations q d t).mp ht
    exact he q d hd hq hm hc t ht head hh

/-- Actual associated RHS computation is equivalent to independent declaration
resolution/derivation under explicit associated well-formedness. -/
theorem view_declarative_exact (awf : Roles.AssocWellFormed env roles)
    (annotations : Node registry root → Declaration → List (Request n))
    (seed : State n) (assignment : Fin n → Comp Common.model) :
    All Common.model assignment (view registry root mask observation env roles wf annotations seed).atoms ↔
      All Common.model assignment seed.atoms ∧
      ∀ q d, d ∈ registry.declarations → CandidatePath registry root mask observation q →
        mask q.val d = true → Candidate observation q.val d →
        ∀ r ∈ annotations q d, ∀ head,
          CommonRoleAssociatedDeclarationExact.DeclarativeComputed env roles r head →
          Common.Equivalent (assignment r.output).1 (.base head) := by
  rw [view_exact]
  simp only [CommonRoleAssociatedDeclarationExact.computed_iff_declarative env roles wf awf,
    reach_iff_path]

end Yulang.CommonRoleGuardedEquations
