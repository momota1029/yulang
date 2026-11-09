import Yulang.CommonRoleGlobalChoiceEquations

/-! Finite self-consistent diagnostic certificates, rechecked at their own
associated output. No prior observation is supplied. All selected requests must
resolve; failure of this stronger certificate is NOT a language rejection.
Receivers and annotations are supplied; existence and driver convergence are
not asserted. -/
namespace Yulang.CommonRoleStableGlobalChoices
open CommonRoleSettledSyntax CommonRoleOpenProducer CommonRoleMaterializedDomain
open CommonRoleCorrelatedPaths (Route)
open CommonRoleAssociatedStateFlow (Request Computed value)
open CommonRoleSettledConstraints (State)
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All)
open CommonRoleGlobalChoices (Table Valid choiceSpace)

variable (registry : Registry) (root : SourceRequest n)

def canonical (table : Table registry root) : Table registry root :=
  (choiceSpace registry root).filter table.contains

theorem canonical_mem (table : Table registry root) (p) :
    p ∈ canonical registry root table ↔ p ∈ choiceSpace registry root ∧ p ∈ table := by
  simp [canonical]

theorem canonical_ext (a b : Table registry root) (same : ∀ p, p ∈ a ↔ p ∈ b) :
    canonical registry root a = canonical registry root b := by
  unfold canonical
  apply List.filter_congr
  intro p _
  apply Bool.eq_iff_iff.mpr
  simpa only [List.contains_iff_mem] using same p

theorem canonical_idempotent (table : Table registry root) :
    canonical registry root (canonical registry root table) = canonical registry root table := by
  unfold canonical
  apply List.filter_congr
  intro p hp
  apply Bool.eq_iff_iff.mpr
  simp only [List.contains_iff_mem, List.mem_filter]
  simp [hp]

variable (env : Roles.AssocEnv) (roles : Roles.RoleDecls) (wf : Roles.WellFormed env.cores)
  (annotations : Route registry root → Declaration → List (Request n))

def requests (table : Table registry root) : List (Request n) :=
  (canonical registry root table).flatMap fun p => annotations p.1 p.2

theorem requests_exact (table : Table registry root) (q : Request n) :
    q ∈ requests registry root annotations table ↔
      ∃ r d, (r,d) ∈ choiceSpace registry root ∧ (r,d) ∈ table ∧ q ∈ annotations r d := by
  simp only [requests, List.mem_flatMap, canonical_mem]
  constructor
  · rintro ⟨⟨r,d⟩,⟨hu,ht⟩,hq⟩
    exact ⟨r,d,hu,ht,hq⟩
  · rintro ⟨r,d,hu,ht,hq⟩
    exact ⟨(r,d),⟨hu,ht⟩,hq⟩

variable (seed : State n)
def output (table : Table registry root) : State n :=
  CommonRoleAssociatedBatch.run env roles wf (requests registry root annotations table) seed

theorem output_canonical (table : Table registry root) :
    output registry root env roles wf annotations seed (canonical registry root table) =
      output registry root env roles wf annotations seed table := by
  simp only [output, requests, canonical_idempotent]

/-- Complete diagnostic evidence: every chosen request resolves, and all routes
and candidates remain supported after their own equations have been generated. -/
def Stable (table : Table registry root) : Prop :=
  Valid registry root (output registry root env roles wf annotations seed table) table ∧
    ∀ q ∈ requests registry root annotations table, ∃ head, Computed env roles wf q head

def check (table : Table registry root) : Bool :=
  CommonRoleGlobalChoices.check registry root
    (output registry root env roles wf annotations seed table) table &&
    (requests registry root annotations table).all fun q => (value env roles wf q).isSome

theorem check_exact (table : Table registry root) :
    check registry root env roles wf annotations seed table = true ↔
      Stable registry root env roles wf annotations seed table := by
  simp only [check, Bool.and_eq_true, CommonRoleGlobalChoices.check_exact,
    List.all_eq_true, Stable]
  apply and_congr Iff.rfl
  apply forall_congr'; intro q
  apply imp_congr_right; intro _
  simp only [Option.isSome_iff_exists, CommonRoleAssociatedStateFlow.value_exact]

def search : List (Table registry root) :=
  (CommonRoleSupportSearch.subsets (choiceSpace registry root)).filter
    (check registry root env roles wf annotations seed)

theorem search_exact (table : Table registry root) :
    table ∈ search registry root env roles wf annotations seed ↔
      table ∈ CommonRoleSupportSearch.subsets (choiceSpace registry root) ∧
      Stable registry root env roles wf annotations seed table := by
  simp only [search, List.mem_filter, check_exact]

/-- Every independently stable table has a searched canonical representative,
with identical output state, not merely equivalent models. -/
theorem complete (table : Table registry root)
    (stable : Stable registry root env roles wf annotations seed table) :
    canonical registry root table ∈ search registry root env roles wf annotations seed ∧
      (∀ p, p ∈ canonical registry root table ↔ p ∈ table) ∧
      output registry root env roles wf annotations seed (canonical registry root table) =
        output registry root env roles wf annotations seed table := by
  have same : ∀ p, p ∈ canonical registry root table ↔ p ∈ table := by
    intro ⟨r,d⟩
    rw [canonical_mem]
    constructor
    · exact And.right
    · intro h
      obtain ⟨hd,hp,_⟩ := stable.1.1 r d h
      exact ⟨(CommonRoleGlobalChoices.universe_exact registry root r d).mpr
        ⟨CommonRoleCorrelatedCarrier.path_retained registry root _ _ r hp,hd⟩,h⟩
  refine ⟨?_,same,output_canonical registry root env roles wf annotations seed table⟩
  apply (search_exact ..).mpr
  refine ⟨CommonRoleSupportSearch.filter_mem_subsets table.contains _,?_,?_⟩
  · rw [output_canonical]
    exact (CommonRoleGlobalChoices.valid_ext registry root _ _ _ same).mpr stable.1
  · simpa only [requests, canonical_idempotent] using stable.2

theorem search_capacity : (search registry root env roles wf annotations seed).length ≤
    2 ^ (choiceSpace registry root).length := by
  calc
    _ ≤ (CommonRoleSupportSearch.subsets (choiceSpace registry root)).length := List.length_filter_le ..
    _ = _ := CommonRoleSupportSearch.subsets_length _

/-- No selected request in a returned table is silently unresolved. -/
theorem resolved (table : Table registry root)
    (found : table ∈ search registry root env roles wf annotations seed)
    (r : Route registry root) (d : Declaration) (chosen : (r,d) ∈ table)
    (q : Request n) (hq : q ∈ annotations r d) : ∃ head, Computed env roles wf q head := by
  have st := ((search_exact ..).mp found).2
  obtain ⟨hd,hp,_⟩ := st.1.1 r d chosen
  apply st.2 q
  exact (requests_exact registry root annotations table q).mpr
    ⟨r,d,(CommonRoleGlobalChoices.universe_exact registry root r d).mpr
      ⟨CommonRoleCorrelatedCarrier.path_retained registry root _ _ r hp,hd⟩,chosen,hq⟩

/-- A selected annotation with an unknown first-order receiver cannot belong to
a complete stable certificate. This is NOT a language error classification. -/
theorem unknown_request_excluded (table : Table registry root)
    (r : Route registry root) (d : Declaration) (chosen : (r,d) ∈ table)
    (q : Request n) (hq : q ∈ annotations r d)
    (unknown : Roles.argsBound q.receiver.args ≠ 0) :
    table ∉ search registry root env roles wf annotations seed := by
  intro found
  obtain ⟨head,hhead⟩ := resolved registry root env roles wf annotations seed table found r d chosen q hq
  exact unknown hhead.1

end Yulang.CommonRoleStableGlobalChoices
