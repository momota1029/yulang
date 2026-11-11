import Yulang.CommonRoleSourceDiagnosticForest
import Yulang.CommonRoleDiagnosticDictionaries

/-! Computed source dictionaries enrich, rather than replace, diagnostic forests.
Each scalar attempt keeps its original failure-preserving tree and receives an
optional existing dictionary Plan. No attempt or source occurrence is filtered. -/
namespace Yulang.CommonRoleSourceDictionaryForest
open Roles RoleDictionaries
open CommonRoleCheckedMixedSource (Source Derives Models)
open CommonRoleAssociatedClauseExtraction (Clause)
open CommonRoleSourceRoleObligations (RawObligation ValidSource raw)
open CommonRoleSourceDiagnosticForest (Attempt Materializes)
open CommonRoleRecursiveDiagnostics (Tree)
open CommonRoleDiagnosticDictionaries (project)

structure Entry where
  diagnostic : Attempt
  plan : Option Plan
  deriving Repr

structure Row where
  obligation : RawObligation
  attempts : List Entry
  deriving Repr

structure Report where
  ordinary : Bool
  rows : List Row
  deriving Repr

def attach (a : Attempt) : Entry :=
  ⟨a,match a with
    | .unsupported _ => none
    | .materialized _ t => project t⟩

def enrichRow (r : CommonRoleSourceDiagnosticForest.Row) : Row :=
  ⟨r.obligation,r.attempts.map attach⟩

def enrich (r : CommonRoleSourceDiagnosticForest.Report) : Report :=
  ⟨r.ordinary,r.rows.map enrichRow⟩

def Row.erase (r : Row) : CommonRoleSourceDiagnosticForest.Row :=
  ⟨r.obligation,r.attempts.map Entry.diagnostic⟩

def Report.erase (r : Report) : CommonRoleSourceDiagnosticForest.Report :=
  ⟨r.ordinary,r.rows.map Row.erase⟩

def Report.observation (r : Report) : Bool × Bool :=
  (r.ordinary,r.rows.all fun row => row.attempts.any fun a => a.plan.isSome)

def run (env : AssocEnv) (roles : RoleDecls) (wf : WellFormed env.cores)
    (src : Source) : Option Report :=
  (CommonRoleSourceDiagnosticForest.run env roles wf src).map enrich

/-- Literal list roundtrip includes failed trees, scalar attempts and order. -/
theorem enrichRow_erase (r : CommonRoleSourceDiagnosticForest.Row) :
    (enrichRow r).erase = r := by
  cases r
  simp [enrichRow,Row.erase,attach,Function.comp_def]

theorem enrich_erase (r : CommonRoleSourceDiagnosticForest.Report) :
    (enrich r).erase = r := by
  cases r
  simp [enrich,Report.erase,Function.comp_def,enrichRow_erase]

theorem run_erasure (env : AssocEnv) (roles : RoleDecls) (wf : WellFormed env.cores)
    (src : Source) :
    (run env roles wf src).map Report.erase =
      CommonRoleSourceDiagnosticForest.run env roles wf src := by
  simp only [run,Option.map_map,Function.comp_def,enrich_erase,Option.map_id']

/-- Having a projected payload agrees with the old attempt's success bit. -/
theorem attach_accepted (a : Attempt) : (attach a).plan.isSome = a.accepted := by
  cases a with
  | unsupported b => rfl
  | materialized b t =>
    simp only [attach,Attempt.accepted]
    apply Bool.eq_iff_iff.mpr
    simpa using CommonRoleDiagnosticDictionaries.project_success t

theorem enrich_observation (r : CommonRoleSourceDiagnosticForest.Report) :
    (enrich r).observation = r.observation := by
  simp only [enrich,Report.observation,CommonRoleSourceDiagnosticForest.Report.observation,
    List.all_map,Function.comp_def,enrichRow,List.any_map,attach_accepted]
  rfl

theorem run_success_iff (env : AssocEnv) (roles : RoleDecls) (wf : WellFormed env.cores)
    (awf : AssocWellFormed env roles) (src : Source) :
    (run env roles wf src).map Report.observation = some (true,true) ↔
      ValidSource roles src.clauses ∧ Models env roles src ∧
        CommonRoleEvidenceDischarge.AllDischarged env roles src := by
  simp only [run,Option.map_map,Function.comp_def,enrich_observation]
  exact CommonRoleSourceDiagnosticForest.run_success_iff env roles wf awf src

/-- Reports exist without requiring ordinary consistency or successful roles. -/
theorem run_exists_iff (env : AssocEnv) (roles : RoleDecls) (wf : WellFormed env.cores)
    (src : Source) : (∃ r, run env roles wf src = some r) ↔ ValidSource roles src.clauses := by
  rw [← CommonRoleSourceDiagnosticForest.run_exists_iff env roles wf src]
  cases h : CommonRoleSourceDiagnosticForest.run env roles wf src <;> simp [run,h]

/-- The independent whole-source model statement is unaffected by projection. -/
theorem run_spec (env : AssocEnv) (roles : RoleDecls) (wf : WellFormed env.cores)
    (awf : AssocWellFormed env roles) (src : Source) (r : Report)
    (computed : run env roles wf src = some r) :
    ValidSource roles src.clauses ∧ r.rows.map Row.obligation = src.clauses.map raw ∧
      (r.ordinary = true ↔ Models env roles src) ∧
      CommonRoleSourceDiagnosticForest.run env roles wf src = some r.erase := by
  have old : CommonRoleSourceDiagnosticForest.run env roles wf src = some r.erase := by
    rw [← run_erasure,computed]; rfl
  have spec := CommonRoleSourceDiagnosticForest.run_spec env roles wf awf src r.erase old
  refine ⟨spec.1,?_,spec.2.2.1,old⟩
  simpa only [Report.erase,Row.erase,List.map_map,Function.comp_def] using spec.2.1

theorem enrichRow_plan_exact (r : CommonRoleSourceDiagnosticForest.Row)
    (b : Inference.Base) (p : Plan) :
    (∃ t, Entry.mk (.materialized b t) (some p) ∈ (enrichRow r).attempts) ↔
      ∃ t, Attempt.materialized b t ∈ r.attempts ∧ project t = some p := by
  constructor
  · rintro ⟨t,member⟩
    obtain ⟨a,ha,eq⟩ := List.mem_map.mp member
    have ae : a = .materialized b t := congrArg Entry.diagnostic eq
    subst a
    exact ⟨t,ha,congrArg Entry.plan eq⟩
  · rintro ⟨t,member,eq⟩
    exact ⟨t,List.mem_map.mpr ⟨.materialized b t,member,by simp [attach,eq]⟩⟩

/-- Every returned plan is exactly the existing indexed dictionary payload,
backed by independently derived source evidence and structural materialization.
There is no caller-supplied execution schedule, successful tree or head map. -/
theorem run_plan_exact (env : AssocEnv) (roles : RoleDecls) (wf : WellFormed env.cores)
    (awf : AssocWellFormed env roles) (src : Source) (r : Report)
    (computed : run env roles wf src = some r) (row : Row) (member : row ∈ r.rows)
    (c : Clause) (same : row.obligation = raw c) (b : Inference.Base) (p : Plan) :
    (∃ t, Entry.mk (.materialized b t) (some p) ∈ row.attempts) ↔
      Derives env roles src c.receiver b ∧ ∃ g, Materializes c b g ∧
        ∃ d : Dictionary env.cores g, d.erase = p := by
  cases old : CommonRoleSourceDiagnosticForest.run env roles wf src with
  | none => simp [run,old] at computed
  | some prior =>
    have eq : enrich prior = r := by simpa [run,old] using computed
    subst r
    obtain ⟨priorRow,priorMember,rfl⟩ := List.mem_map.mp member
    rw [enrichRow_plan_exact]
    constructor
    · rintro ⟨t,present,projected⟩
      obtain ⟨derived,g,material,diag⟩ :=
        (CommonRoleSourceDiagnosticForest.run_materialized_exact env roles wf awf src
          prior old priorRow priorMember c same b t).mp present
      rw [← diag] at projected
      exact ⟨derived,g,material,
        (CommonRoleDiagnosticDictionaries.diagnose_project_exact env.cores wf g p).mp projected⟩
    · rintro ⟨derived,g,material,dict⟩
      refine ⟨CommonRoleRecursiveDiagnostics.diagnose env.cores wf g,?_,
        (CommonRoleDiagnosticDictionaries.diagnose_project_exact env.cores wf g p).mpr dict⟩
      exact (CommonRoleSourceDiagnosticForest.run_materialized_exact env roles wf awf src
        prior old priorRow priorMember c same b _).mpr ⟨derived,g,material,rfl⟩

/-- Every declaration stored at any depth is visible at the root caller. -/
theorem run_plan_visible (env : AssocEnv) (roles : RoleDecls) (wf : WellFormed env.cores)
    (awf : AssocWellFormed env roles) (src : Source) (r : Report)
    (computed : run env roles wf src = some r) (row : Row) (member : row ∈ r.rows)
    (c : Clause) (same : row.obligation = raw c) (b : Inference.Base) (p : Plan)
    (found : ∃ t, Entry.mk (.materialized b t) (some p) ∈ row.attempts) :
    ∀ i ∈ p.declarations, i ∈ env.cores := by
  obtain ⟨_,_,_,d,rfl⟩ :=
    (run_plan_exact env roles wf awf src r computed row member c same b p).mp found
  exact d.all_visible

/-- Arbitrary-depth payload lookup at the public source entry. Root success is
stated explicitly: a successful child alone does not create a root dictionary. -/
theorem run_plan_path_exact (env : AssocEnv) (roles : RoleDecls) (wf : WellFormed env.cores)
    (awf : AssocWellFormed env roles) (src : Source) (r : Report)
    (computed : run env roles wf src = some r) (row : Row) (member : row ∈ r.rows)
    (c : Clause) (same : row.obligation = raw c) (b : Inference.Base)
    (path : List Nat) (q : Plan) :
    (∃ t p, Entry.mk (.materialized b t) (some p) ∈ row.attempts ∧
      CommonRoleDiagnosticDictionaries.follow p path = some q) ↔
      Derives env roles src c.receiver b ∧ ∃ g, Materializes c b g ∧
        RoleConstraints.Resolves env.cores g ∧ ∃ target,
          CommonRoleRecursiveDiagnostics.Path env.cores g path target ∧
          ∃ d : Dictionary env.cores target, d.erase = q := by
  constructor
  · rintro ⟨t,p,present,found⟩
    obtain ⟨derived,g,material,d,erased⟩ :=
      (run_plan_exact env roles wf awf src r computed row member c same b p).mp ⟨t,present⟩
    have projected := (CommonRoleDiagnosticDictionaries.diagnose_project_exact env.cores wf g p).mpr
      ⟨d,erased⟩
    exact ⟨derived,g,material,d.resolves wf,
      (CommonRoleDiagnosticDictionaries.diagnose_plan_path_exact env.cores wf g p projected path q).mp found⟩
  · rintro ⟨derived,g,material,resolved,target,route,dict⟩
    let d := buildResolved env.cores wf g ((RoleConstraints.resolve_exact env.cores wf g).mpr resolved)
    obtain ⟨t,present⟩ :=
      (run_plan_exact env roles wf awf src r computed row member c same b d.erase).mpr
        ⟨derived,g,material,d,rfl⟩
    exact ⟨t,d.erase,present,
      (CommonRoleDiagnosticDictionaries.diagnose_plan_path_exact env.cores wf g d.erase
        (CommonRoleDiagnosticDictionaries.dictionary_projects env.cores wf d) path q).mpr
          ⟨target,route,dict⟩⟩

end Yulang.CommonRoleSourceDictionaryForest
