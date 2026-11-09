import Yulang.CommonRoleDiagnosticTree
import Yulang.CommonRoleEvidenceNormalization

/-! Finite diagnostic certificates rechecked at their scalar-evidence-normalized
associated output. Direct reciprocal-edge evidence is saturated internally. No external observation or evidence-closure premise is supplied. All selected requests must
resolve; failure of this stronger certificate is NOT a language rejection.
Receivers and annotations are supplied; existence and driver convergence are
not asserted. -/
namespace Yulang.CommonRoleNormalizedGlobalChoices
open CommonRoleSettledSyntax CommonRoleOpenProducer CommonRoleMaterializedDomain
open CommonRoleCorrelatedPaths (Route)
open CommonRoleAssociatedStateFlow (Request Computed value)
open CommonRoleSettledConstraints (State)
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All)
open CommonRoleGlobalChoices (Table Valid choiceSpace)

variable (registry : Registry) (root : SourceRequest n)

open CommonRoleStableGlobalChoices (canonical canonical_mem canonical_ext canonical_idempotent)

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
  CommonRoleEvidenceNormalization.normalize
    (CommonRoleAssociatedBatch.run env roles wf (requests registry root annotations table) seed)

theorem output_canonical (table : Table registry root) :
    output registry root env roles wf annotations seed (canonical registry root table) =
      output registry root env roles wf annotations seed table := by
  simp only [output, requests, canonical_idempotent]

/-- Scalar propagation is exact for the existing reciprocal-edge derivation.
It does not claim completeness for arbitrary ordinary semantic consequences. -/
theorem output_evidence (table : Table registry root) (i : Fin n) (b : Inference.Base) :
    CommonRoleOrdinaryKnownness.Evidence
      (output registry root env roles wf annotations seed table).atoms i b ↔
    CommonRoleEvidenceSaturation.Derived
      (CommonRoleStableGlobalChoices.output registry root env roles wf annotations seed table) (i,b) :=
  CommonRoleEvidenceNormalization.normalize_evidence _ i b

/-- Evidence normalization changes observation, but preserves all associated
output models, including when the model set is empty. No stable-table premise. -/
theorem output_models_raw (table : Table registry root)
    (assignment : Fin n → Comp Common.model) :
    All Common.model assignment (output registry root env roles wf annotations seed table).atoms ↔
    All Common.model assignment
      (CommonRoleStableGlobalChoices.output registry root env roles wf annotations seed table).atoms :=
  CommonRoleEvidenceNormalization.normalize_models _ assignment

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

/-- Every independently normalized-stable table has a searched canonical representative,
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


open CommonRoleDiagnosticTree (Visit diagnose valid_tree_total)
/-- All chosen equations are conjoined, and each chosen request really resolves.
This is a two-sided model statement, not a satisfiability/existence assertion. -/
theorem output_models (table : Table registry root)
    (stable : Stable registry root env roles wf annotations seed table)
    (assignment : Fin n → Comp Common.model) :
    All Common.model assignment (output registry root env roles wf annotations seed table).atoms ↔
      All Common.model assignment seed.atoms ∧
      ∀ r d, (r,d) ∈ table → ∀ q ∈ annotations r d, ∀ head,
        Computed env roles wf q head → Common.Equivalent (assignment q.output).1 (.base head) := by
  rw [output, CommonRoleEvidenceNormalization.normalize_models, CommonRoleAssociatedBatch.run_models]
  apply and_congr Iff.rfl
  constructor
  · intro h r d chosen q hq head hh
    obtain ⟨hd,hp,_⟩ := stable.1.1 r d chosen
    apply h q _ head hh
    exact (requests_exact registry root annotations table q).mpr
      ⟨r,d,(CommonRoleGlobalChoices.universe_exact registry root r d).mpr
        ⟨CommonRoleCorrelatedCarrier.path_retained registry root _ _ r hp,hd⟩,chosen,hq⟩
  · intro h q hq head hh
    obtain ⟨r,d,_,chosen,hann⟩ :=
      (requests_exact registry root annotations table q).mp hq
    exact h r d chosen q hann head hh


def infer : List (State n) :=
  (search registry root env roles wf annotations seed).map
    (output registry root env roles wf annotations seed)

/-- Soundness and completeness against ALL stable tables, not just a supplied
candidate or observation. Canonicalization preserves their exact output state. -/
theorem infer_models_exact (assignment : Fin n → Comp Common.model) :
    (∃ out ∈ infer registry root env roles wf annotations seed,
      All Common.model assignment out.atoms) ↔
    All Common.model assignment seed.atoms ∧
      ∃ table : Table registry root,
        Stable registry root env roles wf annotations seed table ∧
        ∀ r d, (r,d) ∈ table → ∀ q ∈ annotations r d, ∀ head,
          Computed env roles wf q head → Common.Equivalent (assignment q.output).1 (.base head) := by
  constructor
  · rintro ⟨out,hm,hmodels⟩
    obtain ⟨table,found,rfl⟩ := List.mem_map.mp hm
    have st := ((search_exact ..).mp found).2
    obtain ⟨hs,he⟩ := (output_models registry root env roles wf annotations seed table st assignment).mp hmodels
    exact ⟨hs,table,st,he⟩
  · rintro ⟨hs,table,st,he⟩
    obtain ⟨found,_,out_eq⟩ := complete registry root env roles wf annotations seed table st
    refine ⟨output registry root env roles wf annotations seed table,?_,?_⟩
    · exact List.mem_map.mpr ⟨_,found,out_eq⟩
    · exact (output_models registry root env roles wf annotations seed table st assignment).mpr ⟨hs,he⟩


/-- At each route in a searched self-output tree there is exactly one table
choice, and every annotation of that choice really resolves. This does not assert
that such a searched tree exists, or that it is a language-selected dictionary. -/
theorem searched_tree_complete
    (table : Table registry root)
    (found : table ∈ search registry root env roles wf annotations seed)
    (r : Route registry root)
    (visit : Visit registry root
      (diagnose registry root table (output registry root env roles wf annotations seed table)) r) :
    ∃ d, (r,d) ∈ table ∧ (∀ e, (r,e) ∈ table → e = d) ∧
      ∀ q ∈ annotations r d, ∃ head, CommonRoleAssociatedStateFlow.Computed env roles wf q head := by
  have st := ((search_exact registry root env roles wf annotations seed table).mp found).2
  obtain ⟨d,hd⟩ := valid_tree_total registry root table _ st.1 r visit
  refine ⟨d,hd,?_,?_⟩
  · intro e he
    exact st.1.2.1 r e d he hd
  · intro q hq
    exact resolved registry root env roles wf annotations seed table found r d hd q hq


/-- Equivalent independent certificate: validation at one's own output, plus
actual resolution of each annotation. No request is hidden by an implication. -/
theorem stable_declarative (awf : Roles.AssocWellFormed env roles)
    (table : Table registry root) :
    Stable registry root env roles wf annotations seed table ↔
      CommonRoleGlobalChoices.Valid registry root
        (output registry root env roles wf annotations seed table) table ∧
      ∀ r d, (r,d) ∈ table → ∀ q ∈ annotations r d, ∃ head,
        CommonRoleAssociatedDeclarationExact.DeclarativeComputed env roles q head := by
  constructor
  · intro st
    refine ⟨st.1,?_⟩
    intro r d chosen q hq
    obtain ⟨hd,hp,_⟩ := st.1.1 r d chosen
    have member := (requests_exact registry root annotations table q).mpr
      ⟨r,d,(CommonRoleGlobalChoices.universe_exact registry root r d).mpr
        ⟨CommonRoleCorrelatedCarrier.path_retained registry root _ _ r hp,hd⟩,chosen,hq⟩
    obtain ⟨head,hhead⟩ := st.2 q member
    exact ⟨head,(CommonRoleAssociatedDeclarationExact.computed_iff_declarative env roles wf awf q head).mp hhead⟩
  · rintro ⟨hv,hr⟩
    refine ⟨hv,?_⟩
    intro q hq
    obtain ⟨r,d,_,chosen,hann⟩ :=
      (requests_exact registry root annotations table q).mp hq
    obtain ⟨head,hh⟩ := hr r d chosen q hann
    exact ⟨head,(CommonRoleAssociatedDeclarationExact.computed_iff_declarative env roles wf awf q head).mpr hh⟩


/-- Independent declaration version, including resolution success rather than
silently dropping unresolved requests. Core and associated wellformedness are
explicit premises; source annotations and first-order receivers remain inputs. -/
theorem infer_declarative_models_exact (awf : Roles.AssocWellFormed env roles)
    (assignment : Fin n → Comp Common.model) :
    (∃ out ∈ infer registry root env roles wf annotations seed,
      All Common.model assignment out.atoms) ↔
    All Common.model assignment seed.atoms ∧
      ∃ table : Table registry root,
        CommonRoleGlobalChoices.Valid registry root
          (output registry root env roles wf annotations seed table) table ∧
        (∀ r d, (r,d) ∈ table → ∀ q ∈ annotations r d, ∃ head,
          CommonRoleAssociatedDeclarationExact.DeclarativeComputed env roles q head) ∧
        ∀ r d, (r,d) ∈ table → ∀ q ∈ annotations r d, ∀ head,
          CommonRoleAssociatedDeclarationExact.DeclarativeComputed env roles q head →
            Common.Equivalent (assignment q.output).1 (.base head) := by
  rw [infer_models_exact]
  simp only [stable_declarative registry root env roles wf annotations seed awf,
    CommonRoleAssociatedDeclarationExact.computed_iff_declarative env roles wf awf, and_assoc]


/-- The associated output models are exactly the seed models satisfying every
chosen annotation indexed by every visited tree route and table choice.
Annotations remain external inputs, not serialized tree payloads. No disconnected
table entry contributes a hidden equation. -/
theorem searched_tree_models
    (table : Table registry root)
    (found : table ∈ search registry root env roles wf annotations seed)
    (assignment : Fin n → Core.PresenceGeneration.Comp Common.model) :
    PresenceNormalForm.All Common.model assignment
      (output registry root env roles wf annotations seed table).atoms ↔
    PresenceNormalForm.All Common.model assignment seed.atoms ∧
      ∀ r, Visit registry root
        (diagnose registry root table
          (output registry root env roles wf annotations seed table)) r →
        ∀ d, (r,d) ∈ table → ∀ q ∈ annotations r d, ∀ head,
          CommonRoleAssociatedStateFlow.Computed env roles wf q head →
            Common.Equivalent (assignment q.output).1 (.base head) := by
  have st := ((search_exact registry root env roles wf annotations seed table).mp found).2
  rw [output_models registry root env roles wf annotations seed table st assignment]
  apply and_congr Iff.rfl
  constructor
  · intro h r _ d hd q hq head hh
    exact h r d hd q hq head hh
  · intro h r d hd q hq head hh
    exact h r ((CommonRoleDiagnosticTree.diagnose_visit_exact registry root table _ r).mpr (st.1.1 r d hd).2.1)
      d hd q hq head hh


end Yulang.CommonRoleNormalizedGlobalChoices
