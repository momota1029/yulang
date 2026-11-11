import Yulang.CommonRoleSourceDictionaryForest

/-! Visible associated declarations may be reordered or repeated without changing
independent source evidence, either output bit, or any complete dictionary payload.
This concerns the finite checked scalar fragment, not general Form inference,
source canonical ordering, method interpretation, or final language classification.
The matching-row conditions below retain occurrence provenance explicitly. -/
namespace Yulang.CommonRoleSourceEnvironmentCongruence
open Roles RoleDictionaries
open CommonRoleAssociatedClauseExtraction (Clause Equation Step)
open CommonRoleCheckedMixedSource (Source Derives Models)
open CommonRoleEvidenceDischarge (Discharged AllDischarged)
open CommonRoleSourceRoleObligations (raw)
open CommonRoleSourceDictionaryForest (Entry Row Report run)

/-- Equality of declarations, including associated bodies, not just head shapes. -/
def Same (left right : AssocEnv) : Prop :=
  ∀ i, i ∈ left.impls ↔ i ∈ right.impls

theorem Same.symm {left right : AssocEnv} (same : Same left right) : Same right left :=
  fun i => (same i).symm

theorem cores_same {left right : AssocEnv} (same : Same left right) (i : Impl) :
    i ∈ left.cores ↔ i ∈ right.cores := by
  simp only [AssocEnv.cores,List.mem_map]
  constructor
  · rintro ⟨a,ha,eq⟩; exact ⟨a,(same a).mp ha,eq⟩
  · rintro ⟨a,ha,eq⟩; exact ⟨a,(same a).mpr ha,eq⟩

theorem resolves_congr {left right : AssocEnv} (same : Same left right) (g : Goal) :
    RoleConstraints.Resolves left.cores g ↔ RoleConstraints.Resolves right.cores g := by
  exact and_congr (RoleVisibility.derives_congr (cores_same same) g)
    (not_congr (RoleVisibility.reachesOverlap_congr (cores_same same) g))

theorem assoc_derives_congr {left right : AssocEnv} (same : Same left right)
    (roles : RoleDecls) (g : Goal) (name : Nat) (value : Term) :
    AssocDerives left roles g name value ↔ AssocDerives right roles g name value := by
  have forward {a b : AssocEnv} (eq : Same a b)
      (h : AssocDerives a roles g name value) : AssocDerives b roles g name value := by
    cases h with
    | explicit i σ member role head children rhs body =>
      exact .explicit i σ ((eq i).mp member) role head
        (fun c hc => (RoleVisibility.derives_congr (cores_same eq) _).mp (children c hc)) rhs body
    | default i σ member role head children rhs omitted body =>
      exact .default i σ ((eq i).mp member) role head
        (fun c hc => (RoleVisibility.derives_congr (cores_same eq) _).mp (children c hc)) rhs omitted body
  exact ⟨forward same,forward same.symm⟩

theorem step_congr {left right : AssocEnv} (same : Same left right)
    (roles : RoleDecls) (c : Clause) (e : Equation) (head result : Inference.Base) :
    Step left roles c e head result ↔ Step right roles c e head result := by
  simp only [Step,resolves_congr same,assoc_derives_congr same]

/-- All independently derived facts agree, not merely successful role queries. -/
theorem derives_congr {left right : AssocEnv} (same : Same left right)
    (roles : RoleDecls) (src : Source) (a : Nat) (b : Inference.Base) :
    Derives left roles src a b ↔ Derives right roles src a b := by
  have forward {x y : AssocEnv} (eq : Same x y) {a b}
      (h : Derives x roles src a b) : Derives y roles src a b := by
    induction h with
    | initial upper lower => exact .initial upper lower
    | transfer upper lower _ ih => exact .transfer upper lower ih
    | equation c e member eqMember _ step ih =>
      exact .equation c e member eqMember ih ((step_congr eq roles c e _ _).mp step)
  exact ⟨forward same,forward same.symm⟩

theorem models_congr {left right : AssocEnv} (same : Same left right)
    (roles : RoleDecls) (src : Source) : Models left roles src ↔ Models right roles src := by
  simp only [Models,derives_congr same]

theorem discharged_congr {left right : AssocEnv} (same : Same left right)
    (roles : RoleDecls) (src : Source) (c : Clause) :
    Discharged left roles src c ↔ Discharged right roles src c := by
  simp only [Discharged,CommonRoleSourceRoleObligations.Discharges,
    derives_congr same,resolves_congr same]

theorem all_discharged_congr {left right : AssocEnv} (same : Same left right)
    (roles : RoleDecls) (src : Source) :
    AllDischarged left roles src ↔ AllDischarged right roles src := by
  simp only [AllDischarged,discharged_congr same]

/-- Both observations are invariant separately, even for inconsistent ordinary
input or incomplete roles. Invalid source remains absent on both sides. -/
theorem observation_congr {left right : AssocEnv} (same : Same left right)
    (roles : RoleDecls) (lw : WellFormed left.cores) (rw : WellFormed right.cores)
    (la : AssocWellFormed left roles) (ra : AssocWellFormed right roles) (src : Source) :
    (run left roles lw src).map Report.observation =
      (run right roles rw src).map Report.observation := by
  have projection (e : AssocEnv) (w : WellFormed e.cores) :
      (run e roles w src).map Report.observation = CommonRoleEvidenceDischarge.run e roles w src := by
    simp only [run,Option.map_map,Function.comp_def,
      CommonRoleSourceDictionaryForest.enrich_observation]
    exact CommonRoleSourceDiagnosticForest.observation_projection e roles w src
  rw [projection,projection]
  cases checked : CommonRoleCheckedMixedSource.check roles src with
  | none => simp [CommonRoleEvidenceDischarge.run,checked]
  | some p =>
    simp only [CommonRoleEvidenceDischarge.run,checked,Option.map_some]
    apply congrArg some
    apply Prod.ext
    · apply Bool.eq_iff_iff.mpr
      rw [CommonRoleCheckedMixedSource.checked_solver_exact left roles lw la src p checked,
        CommonRoleCheckedMixedSource.checked_solver_exact right roles rw ra src p checked]
      exact models_congr same roles src
    · apply Bool.eq_iff_iff.mpr
      rw [CommonRoleEvidenceDischarge.run_roles_exact left roles lw la src p checked,
        CommonRoleEvidenceDischarge.run_roles_exact right roles rw ra src p checked]
      exact all_discharged_congr same roles src

/-- Equality of the complete existing Plan, preserving ordered repeated children. -/
theorem dictionary_payload_congr {left right : AssocEnv} (same : Same left right)
    (lw : WellFormed left.cores) (rw : WellFormed right.cores) (g : Goal) (p : Plan) :
    (∃ d : Dictionary left.cores g, d.erase = p) ↔
      ∃ d : Dictionary right.cores g, d.erase = p := by
  rw [← elaborate_success_iff left.cores lw g p,← elaborate_success_iff right.cores rw g p,
    elaborate_congr (cores_same same) lw rw g]

/-- Source-to-dictionary invariance includes mixed associated/ordinary evidence
closure. Report and row membership are checked outputs, never run inputs. -/
theorem run_plan_congr {left right : AssocEnv} (same : Same left right)
    (roles : RoleDecls) (lw : WellFormed left.cores) (rw : WellFormed right.cores)
    (la : AssocWellFormed left roles) (ra : AssocWellFormed right roles) (src : Source)
    (lr rr : Report) (lc : run left roles lw src = some lr)
    (rc : run right roles rw src = some rr) (lrow rrow : Row)
    (lm : lrow ∈ lr.rows) (rm : rrow ∈ rr.rows) (c : Clause)
    (ls : lrow.obligation = raw c) (rs : rrow.obligation = raw c)
    (b : Inference.Base) (p : Plan) :
    (∃ t, Entry.mk (.materialized b t) (some p) ∈ lrow.attempts) ↔
      ∃ t, Entry.mk (.materialized b t) (some p) ∈ rrow.attempts := by
  rw [CommonRoleSourceDictionaryForest.run_plan_exact left roles lw la src lr lc lrow lm c ls b p,
    CommonRoleSourceDictionaryForest.run_plan_exact right roles rw ra src rr rc rrow rm c rs b p]
  simp only [derives_congr same,dictionary_payload_congr same lw rw]

/-- Permutations of visible declarations are a concrete sufficient condition. -/
theorem observation_perm {left right : AssocEnv} (perm : left.impls.Perm right.impls)
    (roles : RoleDecls) (lw : WellFormed left.cores) (rw : WellFormed right.cores)
    (la : AssocWellFormed left roles) (ra : AssocWellFormed right roles) (src : Source) :
    (run left roles lw src).map Report.observation =
      (run right roles rw src).map Report.observation :=
  observation_congr (fun _ => perm.mem_iff) roles lw rw la ra src

end Yulang.CommonRoleSourceEnvironmentCongruence
