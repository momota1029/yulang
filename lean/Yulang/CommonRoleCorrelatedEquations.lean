import Yulang.CommonRoleCorrelatedCarrier

/-! Associated equation views keyed by entire ancestor candidate histories.
Every mask and annotation is path-local, so merging source nodes does not erase
ancestor identity. The choice policy and observation state remain inputs. This
module does not assert simultaneous language consistency of enabled paths. -/
namespace Yulang.CommonRoleCorrelatedEquations
open CommonRoleSettledSyntax CommonRoleOpenProducer CommonRoleMaterializedDomain
open CommonRoleSourceWorklist (Node)
open CommonRoleSettledConstraints (State)
open CommonRoleGuardedEquations (Candidate candidate candidate_exact)
open CommonRoleCorrelatedPaths (History Route Path collect collect_exact)
open CommonRoleAssociatedStateFlow (Request Computed)
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All)

variable (registry : Registry) (root : SourceRequest n)
  (mask : History registry root → Node registry root → Declaration → Bool)
  (observation : State n)

abbrev Entry := Route registry root × Declaration × Request n

/-- Stored independently of the current mask/observation. -/
def entries (annotations : Route registry root → Declaration → List (Request n)) :
    List (Entry registry root) :=
  (CommonRoleCorrelatedCarrier.carrier registry root).flatMap fun r =>
    registry.declarations.flatMap fun d => (annotations r d).map fun q => (r,d,q)

theorem entries_exact (annotations : Route registry root → Declaration → List (Request n))
    (r : Route registry root) (d : Declaration) (q : Request n) :
    (r,d,q) ∈ entries registry root annotations ↔
      r ∈ CommonRoleCorrelatedCarrier.carrier registry root ∧
      d ∈ registry.declarations ∧ q ∈ annotations r d := by
  simp only [entries, List.mem_flatMap, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨t, ht, e, he, z, hz, htr, hed, hzq⟩
    subst t; subst e; subst z
    exact ⟨ht, he, hz⟩
  · rintro ⟨hr, hd, hq⟩
    exact ⟨r,hr,d,hd,q,hq,rfl,rfl,rfl⟩

def active (e : Entry registry root) : Bool :=
  (collect registry root mask observation).contains e.1 &&
    (mask e.1.1 e.1.2 e.2.1 && candidate observation e.1.2.val e.2.1)

def activate (annotations : Route registry root → Declaration → List (Request n)) :
    List (Entry registry root) :=
  (entries registry root annotations).filter (active registry root mask observation)

/-- Guard and annotation retain the same full history. No existentially chosen
other route to the same tip can license this entry. -/
theorem activate_exact (annotations : Route registry root → Declaration → List (Request n))
    (r : Route registry root) (d : Declaration) (q : Request n) :
    (r,d,q) ∈ activate registry root mask observation annotations ↔
      Path registry root mask observation r ∧ d ∈ registry.declarations ∧
      mask r.1 r.2 d = true ∧ Candidate observation r.2.val d ∧ q ∈ annotations r d := by
  simp only [activate, List.mem_filter, entries_exact, active, Bool.and_eq_true,
    List.contains_iff_mem, collect_exact, candidate_exact]
  constructor
  · rintro ⟨⟨_,hd,hq⟩,hp,hm,hc⟩
    exact ⟨hp,hd,hm,hc,hq⟩
  · rintro ⟨hp,hd,hm,hc,hq⟩
    exact ⟨⟨CommonRoleCorrelatedCarrier.path_retained registry root mask observation r hp,hd,hq⟩,
      hp,hm,hc⟩

/-- Every path's annotations are stored even when this path is not currently
active. The witness state/mask is arbitrary and absent from the stored entries. -/
theorem entry_retained (annotations : Route registry root → Declaration → List (Request n))
    (r : Route registry root) (d : Declaration) (q : Request n)
    (hp : Path registry root mask observation r)
    (hd : d ∈ registry.declarations) (hq : q ∈ annotations r d) :
    (r,d,q) ∈ entries registry root annotations :=
  (entries_exact registry root annotations r d q).mpr
    ⟨CommonRoleCorrelatedCarrier.path_retained registry root mask observation r hp,hd,hq⟩

/-- A disabled entry cannot borrow support from another history with the same tip. -/
theorem disabled_history_excluded
    (annotations : Route registry root → Declaration → List (Request n))
    (r : Route registry root) (d : Declaration) (q : Request n)
    (disabled : mask r.1 r.2 d = false) :
    (r,d,q) ∉ activate registry root mask observation annotations := by
  intro member
  have enabled := ((activate_exact registry root mask observation annotations r d q).mp member).2.2.1
  simp [disabled] at enabled

variable (env : Roles.AssocEnv) (roles : Roles.RoleDecls) (wf : Roles.WellFormed env.cores)

def view (annotations : Route registry root → Declaration → List (Request n)) (seed : State n) : State n :=
  CommonRoleAssociatedBatch.run env roles wf
    ((activate registry root mask observation annotations).map fun e => e.2.2) seed

/-- Soundness/completeness of the conditional path-correlated equation view.
The Path premise is independently defined using Inspect and source substitution.
This is not feedback convergence, guard preservation, or language typing. -/
theorem view_exact (annotations : Route registry root → Declaration → List (Request n))
    (seed : State n) (assignment : Fin n → Comp Common.model) :
    All Common.model assignment (view registry root mask observation env roles wf annotations seed).atoms ↔
      All Common.model assignment seed.atoms ∧
      ∀ r, Path registry root mask observation r →
        ∀ d ∈ registry.declarations, mask r.1 r.2 d = true → Candidate observation r.2.val d →
        ∀ q ∈ annotations r d, ∀ head, Computed env roles wf q head →
          Common.Equivalent (assignment q.output).1 (.base head) := by
  rw [view, CommonRoleAssociatedBatch.run_models]
  constructor
  · rintro ⟨hs, he⟩
    refine ⟨hs, ?_⟩
    intro r hr d hd hm hc q hq head hh
    exact he q (List.mem_map.mpr ⟨(r,d,q),
      (activate_exact registry root mask observation annotations r d q).mpr ⟨hr,hd,hm,hc,hq⟩, rfl⟩)
      head hh
  · rintro ⟨hs, he⟩
    refine ⟨hs, ?_⟩
    intro q hq head hh
    obtain ⟨⟨r,d,t⟩, ht, rfl⟩ := List.mem_map.mp hq
    obtain ⟨hr, hd, hm, hc, ht⟩ := (activate_exact registry root mask observation annotations r d t).mp ht
    exact he r hr d hd hm hc t ht head hh

/-- Connect the actual equation interpreter to independent associated-declaration
resolution. AssocWellFormed is an explicit assumption, not an inferred result. -/
theorem view_declarative_exact (awf : Roles.AssocWellFormed env roles)
    (annotations : Route registry root → Declaration → List (Request n))
    (seed : State n) (assignment : Fin n → Comp Common.model) :
    All Common.model assignment (view registry root mask observation env roles wf annotations seed).atoms ↔
      All Common.model assignment seed.atoms ∧
      ∀ r, Path registry root mask observation r →
        ∀ d ∈ registry.declarations, mask r.1 r.2 d = true → Candidate observation r.2.val d →
        ∀ q ∈ annotations r d, ∀ head,
          CommonRoleAssociatedDeclarationExact.DeclarativeComputed env roles q head →
          Common.Equivalent (assignment q.output).1 (.base head) := by
  rw [view_exact]
  simp only [CommonRoleAssociatedDeclarationExact.computed_iff_declarative env roles wf awf]

end Yulang.CommonRoleCorrelatedEquations
