import Yulang.CommonRoleEvidenceDischarge
import Yulang.CommonRoleRecursiveDiagnostics

/-! Checked finite source diagnostics retain every obligation and every computed
scalar attempt. Successful, missing and overlapping rigid child trees remain
available alongside the ordinary consistency bit. Absent scalar evidence and
unsupported encodings are observations, not final language classifications. -/
namespace Yulang.CommonRoleSourceDiagnosticForest
open CommonRoleCheckedMixedSource (Source Derives Models check finish)
open CommonRoleAssociatedClauseExtraction (Clause)
open CommonRoleSourceRoleObligations (Package Obligation RawObligation ValidSource erase raw)
open CommonRoleStructuralAssociatedTemplates (generate Fills)
open CommonRoleRecursiveDiagnostics (Tree Represents diagnose)
open CommonRoleEvidenceDischarge (heads)

inductive Attempt where
  | unsupported (base : Inference.Base)
  | materialized (base : Inference.Base) (tree : Tree)
  deriving Repr

def Attempt.base : Attempt → Inference.Base
  | .unsupported b | .materialized b _ => b

def Attempt.accepted : Attempt → Bool
  | .unsupported _ => false
  | .materialized _ tree => decide (tree.status = .resolved)

structure Row where
  obligation : RawObligation
  attempts : List Attempt
  deriving Repr

def Row.accepted (r : Row) : Bool := r.attempts.any Attempt.accepted

structure Report where
  ordinary : Bool
  rows : List Row
  deriving Repr

def Report.observation (r : Report) : Bool × Bool :=
  (r.ordinary,r.rows.all Row.accepted)

/-- Source materialization reads structural filling, not a generated goal. -/
def Materializes (c : Clause) (b : Inference.Base) (g : Roles.Goal) : Prop :=
  ∃ payload, CommonRoleOrdinaryKnownness.encode b = some payload ∧
    g.role = c.goal.role ∧ Fills payload c.goal.args g.args

def ExplainsAttempt (impls : List Roles.Impl) (c : Clause) : Attempt → Prop
  | .unsupported b => ¬ ∃ g, Materializes c b g
  | .materialized b t => Materializes c b t.goal ∧ Represents impls t.goal t

def Explains (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (src : Source) (c : Clause) (r : Row) : Prop :=
  r.obligation = raw c ∧
    (∀ b, b ∈ r.attempts.map Attempt.base ↔ Derives env roles src c.receiver b) ∧
    ∀ a ∈ r.attempts, ExplainsAttempt env.cores c a

/-- Unsupported encoding is not mistaken for a missing implementation. -/
def attempt (impls : List Roles.Impl) (wf : Roles.WellFormed impls)
    (o : Obligation) (b : Inference.Base) : Attempt :=
  let g := generate o.template b
  if Roles.argsBound g.args = 0 then .materialized b (diagnose impls wf g)
  else .unsupported b

theorem attempt_base (impls : List Roles.Impl) (wf : Roles.WellFormed impls)
    (o : Obligation) (b : Inference.Base) : (attempt impls wf o b).base = b := by
  dsimp only [attempt]; split <;> rfl

theorem materializes_iff (o : Obligation) (c : Clause) (same : erase o = raw c)
    (b : Inference.Base) (g : Roles.Goal) :
    Materializes c b g ↔ Roles.argsBound (generate o.template b).args = 0 ∧
      generate o.template b = g := by
  have goal := congrArg RawObligation.goal same
  change o.template.goal = c.goal at goal
  rw [← CommonRoleStructuralAssociatedTemplates.materializes_exact]
  simp only [Materializes,CommonRoleStructuralAssociatedTemplates.Materializes,goal]

theorem attempt_explains (impls : List Roles.Impl) (wf : Roles.WellFormed impls)
    (o : Obligation) (c : Clause) (same : erase o = raw c) (b : Inference.Base) :
    ExplainsAttempt impls c (attempt impls wf o b) := by
  dsimp only [attempt]
  split
  · rename_i closed
    exact ⟨(materializes_iff o c same b _).mpr
      ⟨closed,(CommonRoleRecursiveDiagnostics.diagnose_goal impls wf _).symm⟩,
      by rw [CommonRoleRecursiveDiagnostics.diagnose_goal]; exact
        CommonRoleRecursiveDiagnostics.diagnose_represents impls wf _⟩
  · rename_i unsupported
    intro h
    obtain ⟨g,material⟩ := h
    exact unsupported ((materializes_iff o c same b g).mp material).1

theorem attempt_accepted (impls : List Roles.Impl) (wf : Roles.WellFormed impls)
    (o : Obligation) (b : Inference.Base) :
    (attempt impls wf o b).accepted =
      CommonRoleSourceRoleObligations.runOne impls wf (fun _ => b) o := by
  dsimp only [attempt,CommonRoleSourceRoleObligations.runOne]
  split <;> simp_all [Attempt.accepted,CommonRoleRecursiveDiagnostics.diagnose_status]

def inspect (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (src : Source) (p : Package) (o : Obligation) : Row :=
  ⟨erase o,(heads env roles wf src p o.receiver).map (attempt env.cores wf o)⟩

theorem inspect_explains (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (src : Source) (p : Package) (checked : check roles src = some p)
    (o : Obligation) (c : Clause) (same : erase o = raw c) :
    Explains env roles src c (inspect env roles wf src p o) := by
  refine ⟨same,?_,?_⟩
  · intro b
    have receiver := congrArg RawObligation.receiver same
    change o.receiver = c.receiver at receiver
    simp only [inspect,List.map_map,Function.comp_def,attempt_base]
    simpa only [List.map_id',receiver] using
      CommonRoleEvidenceDischarge.heads_exact env roles wf awf src p checked o.receiver b
  · intro a ha
    obtain ⟨b,_,rfl⟩ := List.mem_map.mp ha
    exact attempt_explains env.cores wf o c same b

theorem inspect_accepted (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (src : Source) (p : Package) (o : Obligation) :
    (inspect env roles wf src p o).accepted =
      CommonRoleEvidenceDischarge.runOne env roles wf src p o := by
  simp only [inspect,Row.accepted,List.any_map,Function.comp_def,attempt_accepted,
    CommonRoleEvidenceDischarge.runOne]

def output (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (src : Source) (p : Package) : Report :=
  ⟨CommonRoleOpenPropagation.consistent (finish env roles wf src p),
    p.obligations.map (inspect env roles wf src p)⟩

def run (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (src : Source) : Option Report :=
  (check roles src).map (output env roles wf src)

/-- Erasure is literal list equality, including source order and multiplicity. -/
theorem output_rows (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (src : Source) (p : Package)
    (checked : check roles src = some p) :
    (output env roles wf src p).rows.map Row.obligation = src.clauses.map raw := by
  simpa only [output,List.map_map,Function.comp_def,inspect] using
    ((CommonRoleSourceRoleObligations.check_exact roles src.clauses p).mp checked).1

theorem output_explains (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (src : Source) (p : Package) (checked : check roles src = some p)
    (r : Row) (member : r ∈ (output env roles wf src p).rows)
    (c : Clause) (same : r.obligation = raw c) : Explains env roles src c r := by
  obtain ⟨o,_,rfl⟩ := List.mem_map.mp member
  exact inspect_explains env roles wf awf src p checked o c same

/-- Observation erasure recovers cycle105 without any new acceptance rule. -/
theorem observation_projection (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (src : Source) :
    (run env roles wf src).map Report.observation =
      CommonRoleEvidenceDischarge.run env roles wf src := by
  simp only [run,Option.map_map,Function.comp_def,output,Report.observation,List.all_map,
    inspect_accepted,CommonRoleEvidenceDischarge.run,CommonRoleEvidenceDischarge.runRoles]

/-- Unconditional outer specification for every computed report. The report's
source rows and every failed child are retained without assumed role success. -/
theorem run_spec (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (src : Source) (r : Report) (computed : run env roles wf src = some r) :
    ValidSource roles src.clauses ∧ r.rows.map Row.obligation = src.clauses.map raw ∧
      (r.ordinary = true ↔ Models env roles src) ∧
      ∀ row ∈ r.rows, ∀ c, row.obligation = raw c → Explains env roles src c row := by
  cases checked : check roles src with
  | none =>
    simp only [run,checked,Option.map_none] at computed
    cases computed
  | some p =>
    have eq : output env roles wf src p = r := by
      simpa only [run,checked,Option.map_some,Option.some.injEq] using computed
    subst r
    refine ⟨((CommonRoleSourceRoleObligations.check_exact roles src.clauses p).mp checked).2.2,
      output_rows env roles wf src p checked, ?_,
      output_explains env roles wf awf src p checked⟩
    simp only [output]
    exact CommonRoleCheckedMixedSource.checked_solver_exact env roles wf awf src p checked

/-- The outer checker constructs a report for every valid finite source; no
role success or model existence is needed for diagnostic availability. -/
theorem run_exists_iff (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (src : Source) :
    (∃ r, run env roles wf src = some r) ↔ ValidSource roles src.clauses := by
  have accepts := CommonRoleSourceRoleObligations.check_accepts roles src.clauses
  change (check roles src).isSome = true ↔ _ at accepts
  rw [← accepts]
  cases checked : check roles src <;> simp [run,checked]

/-- Acceptance still needs ordinary consistency and all retained obligations. -/
theorem run_success_iff (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles) (src : Source) :
    (run env roles wf src).map Report.observation = some (true,true) ↔
      ValidSource roles src.clauses ∧ Models env roles src ∧
        CommonRoleEvidenceDischarge.AllDischarged env roles src := by
  rw [observation_projection,CommonRoleEvidenceDischarge.run_success_iff env roles wf awf src]

/-- Complete tree payloads are exactly generated materializations, not merely
any tree with an equivalent success bit. -/
theorem attempt_materialized_iff (impls : List Roles.Impl) (wf : Roles.WellFormed impls)
    (o : Obligation) (c : Clause) (same : erase o = raw c)
    (a b : Inference.Base) (t : Tree) :
    attempt impls wf o a = .materialized b t ↔
      a = b ∧ ∃ g, Materializes c b g ∧ diagnose impls wf g = t := by
  constructor
  · intro eq
    dsimp only [attempt] at eq
    split at eq
    · rename_i closed
      have both := Attempt.materialized.inj eq
      rcases both with ⟨rfl,rfl⟩
      exact ⟨rfl,_,(materializes_iff o c same a _).mpr ⟨closed,rfl⟩,rfl⟩
    · cases eq
  · rintro ⟨rfl,g,material,tree⟩
    have generated := (materializes_iff o c same a g).mp material
    simp only [attempt,generated.1,ite_true]
    rw [generated.2,tree]

theorem inspect_materialized_exact (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (src : Source) (p : Package) (checked : check roles src = some p)
    (o : Obligation) (c : Clause) (same : erase o = raw c)
    (b : Inference.Base) (t : Tree) :
    Attempt.materialized b t ∈ (inspect env roles wf src p o).attempts ↔
      Derives env roles src c.receiver b ∧
        ∃ g, Materializes c b g ∧ diagnose env.cores wf g = t := by
  have receiver := congrArg RawObligation.receiver same
  change o.receiver = c.receiver at receiver
  simp only [inspect,List.mem_map,attempt_materialized_iff env.cores wf o c same,
    CommonRoleEvidenceDischarge.heads_exact env roles wf awf src p checked,receiver]
  constructor
  · rintro ⟨a,derived,rfl,material⟩; exact ⟨derived,material⟩
  · rintro ⟨derived,material⟩; exact ⟨b,derived,rfl,material⟩

/-- Exact payload characterization at the public source entry. -/
theorem run_materialized_exact (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (src : Source) (r : Report) (computed : run env roles wf src = some r)
    (row : Row) (member : row ∈ r.rows) (c : Clause) (same : row.obligation = raw c)
    (b : Inference.Base) (t : Tree) :
    Attempt.materialized b t ∈ row.attempts ↔ Derives env roles src c.receiver b ∧
      ∃ g, Materializes c b g ∧ diagnose env.cores wf g = t := by
  cases checked : check roles src with
  | none => simp only [run,checked,Option.map_none] at computed; cases computed
  | some p =>
    have eq : output env roles wf src p = r := by
      simpa only [run,checked,Option.map_some,Option.some.injEq] using computed
    subst r
    obtain ⟨o,_,rfl⟩ := List.mem_map.mp member
    exact inspect_materialized_exact env roles wf awf src p checked o c same b t

/-- Every original occurrence has a retained diagnostic row, even if it has no
scalar evidence or has no associated equations. -/
theorem run_clause_retained (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (src : Source) (r : Report) (computed : run env roles wf src = some r)
    (c : Clause) (member : c ∈ src.clauses) :
    ∃ row ∈ r.rows, row.obligation = raw c := by
  have exactRows := (run_spec env roles wf awf src r computed).2.1
  have present : raw c ∈ src.clauses.map raw := List.mem_map.mpr ⟨c,member,rfl⟩
  rw [← exactRows] at present
  exact List.mem_map.mp present

/-- Source-to-recursive-child exactness, in both directions, for arbitrary depth.
The right side uses source derivation, structural filling and declaration paths;
it has no computed slots, candidate table, fuel, resolver success or state input. -/
theorem run_path_exact (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (src : Source) (r : Report) (computed : run env roles wf src = some r)
    (c : Clause) (member : c ∈ src.clauses) (b : Inference.Base)
    (path : List Nat) (target : Roles.Goal) :
    (∃ row ∈ r.rows, row.obligation = raw c ∧ ∃ t,
      Attempt.materialized b t ∈ row.attempts ∧
      ∃ child, t.follow path = some child ∧ child.goal = target) ↔
      Derives env roles src c.receiver b ∧ ∃ g, Materializes c b g ∧
        CommonRoleRecursiveDiagnostics.Path env.cores g path target := by
  constructor
  · rintro ⟨row,hr,same,t,ht,child,found,goal⟩
    obtain ⟨derived,g,material,rfl⟩ :=
      (run_materialized_exact env roles wf awf src r computed row hr c same b t).mp ht
    obtain ⟨endGoal,route,eq⟩ :=
      (CommonRoleRecursiveDiagnostics.diagnose_follow_exact env.cores wf g path child).mp found
    have targetEq : endGoal = target := by
      rw [← CommonRoleRecursiveDiagnostics.diagnose_goal env.cores wf endGoal,eq,goal]
    exact ⟨derived,g,material,targetEq ▸ route⟩
  · rintro ⟨derived,g,material,route⟩
    obtain ⟨row,hr,same⟩ := run_clause_retained env roles wf awf src r computed c member
    refine ⟨row,hr,same,diagnose env.cores wf g,?_,diagnose env.cores wf target,?_,
      CommonRoleRecursiveDiagnostics.diagnose_goal env.cores wf target⟩
    · exact (run_materialized_exact env roles wf awf src r computed row hr c same b _).mpr
        ⟨derived,g,material,rfl⟩
    · exact (CommonRoleRecursiveDiagnostics.diagnose_follow_exact env.cores wf g path _).mpr
        ⟨target,route,rfl⟩

end Yulang.CommonRoleSourceDiagnosticForest
