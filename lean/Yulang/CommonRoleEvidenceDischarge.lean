import Yulang.CommonRoleCheckedMixedSource

/-! Retained source roles consume the actual mixed closure's scalar evidence.
The caller supplies neither a scalar head map nor a computed state. Two separate
observations retain ordinary consistency and evidence-backed role discharge.
False discharge is not a language-visible final classification. This finite
fragment keeps scope-resolved names, explicit paired evidence and the existing
int/str encoder; it is not general source inference or B4. -/
namespace Yulang.CommonRoleEvidenceDischarge
open CommonRoleCheckedMixedSource (Source Derives Models check table name finish)
open CommonRoleAssociatedClauseExtraction (Clause)
open CommonRoleSourceRoleObligations (Package Obligation ValidSource erase raw Discharges)
open CommonRoleOrdinaryKnownness (candidates)

/-- Declarative role discharge uses source derivations, not computed slots. -/
def Discharged (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (src : Source) (c : Clause) : Prop :=
  ∃ b, Derives env roles src c.receiver b ∧ Discharges env.cores (fun _ => b) c

def AllDischarged (env : Roles.AssocEnv) (roles : Roles.RoleDecls) (src : Source) : Prop :=
  ∀ c ∈ src.clauses, Discharged env roles src c

/-- Even a bare role needs no extra caller allocation: any derivable receiver is
already in the ordinary/equation domain. An unseeded bare receiver has no fact. -/
theorem derived_support (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (src : Source) (p : Package) (checked : check roles src = some p)
    (a : Nat) (b : Inference.Base) (h : Derives env roles src a b) :
    ∃ i : Fin (table src p).length, name src p i = a := by
  have named := (CommonRoleCheckedMixedSource.checked_derives_exact env roles src p checked a b).mpr h
  have allocated := CommonRoleNamedOrdinaryInputs.named_to_allocated env roles p.equations
    src.ordinary a b named
  exact CommonRoleAmbientMixedSource.named_support env roles p.equations _ _ a b allocated

def heads (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (src : Source) (p : Package) (a : Nat) :
    List Inference.Base :=
  (List.finRange (table src p).length).flatMap fun i =>
    if name src p i = a then candidates (finish env roles wf src p).atoms i else []

theorem heads_exact (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (src : Source) (p : Package) (checked : check roles src = some p)
    (a : Nat) (b : Inference.Base) :
    b ∈ heads env roles wf src p a ↔ Derives env roles src a b := by
  simp only [heads,List.mem_flatMap]
  constructor
  · rintro ⟨i,_,h⟩
    split at h
    · rename_i same
      have evidence := (CommonRoleOrdinaryKnownness.candidates_exact _ i b).mp h
      simpa only [same] using
        (CommonRoleCheckedMixedSource.checked_evidence_exact env roles wf awf src p checked i b).mp evidence
    · simp at h
  · intro h
    obtain ⟨i,same⟩ := derived_support env roles src p checked a b h
    refine ⟨i,by simp,?_⟩
    rw [ite_eq_left same,CommonRoleOrdinaryKnownness.candidates_exact]
    exact (CommonRoleCheckedMixedSource.checked_evidence_exact env roles wf awf src p checked i b).mpr
      (by simpa only [same] using h)

def runOne (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (src : Source) (p : Package) (o : Obligation) : Bool :=
  (heads env roles wf src p o.receiver).any fun b =>
    CommonRoleSourceRoleObligations.runOne env.cores wf (fun _ => b) o

theorem run_one_exact (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (src : Source) (p : Package) (checked : check roles src = some p)
    (o : Obligation) (c : Clause) (same : erase o = raw c) :
    runOne env roles wf src p o = true ↔ Discharged env roles src c := by
  have receiver : o.receiver = c.receiver := congrArg
    CommonRoleSourceRoleObligations.RawObligation.receiver same
  simp only [runOne,List.any_eq_true,heads_exact env roles wf awf src p checked,
    CommonRoleSourceRoleObligations.run_one_exact env.cores wf _ o c same,receiver,Discharged]

def runRoles (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (src : Source) (p : Package) : Bool :=
  p.obligations.all (runOne env roles wf src p)

theorem run_roles_exact (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (src : Source) (p : Package) (checked : check roles src = some p) :
    runRoles env roles wf src p = true ↔ AllDischarged env roles src := by
  simp only [runRoles,List.all_eq_true,AllDischarged]
  constructor
  · intro h c hc
    obtain ⟨o,ho,same⟩ := (CommonRoleSourceRoleObligations.checked_occurs roles
      src.clauses p checked (raw c)).mpr ⟨c,hc,rfl⟩
    exact (run_one_exact env roles wf awf src p checked o c same).mp (h o ho)
  · intro h o ho
    obtain ⟨c,hc,same⟩ := (CommonRoleSourceRoleObligations.checked_occurs roles
      src.clauses p checked (erase o)).mp ⟨o,ho,rfl⟩
    exact (run_one_exact env roles wf awf src p checked o c same.symm).mpr (h c hc)

/-- First component is ordinary consistency, second is evidence-backed role
resolution. They remain separate even on inconsistent or unseeded input. -/
def run (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (src : Source) : Option (Bool × Bool) :=
  (check roles src).map fun p =>
    (CommonRoleOpenPropagation.consistent (finish env roles wf src p),runRoles env roles wf src p)

theorem run_none_iff (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (src : Source) :
    run env roles wf src = none ↔ ¬ ValidSource roles src.clauses := by
  simp [run,check,CommonRoleSourceRoleObligations.check]

/-- Ordinary observation agrees with the established checked mixed source entry. -/
theorem ordinary_projection (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (src : Source) :
    (run env roles wf src).map Prod.fst = CommonRoleCheckedMixedSource.run env roles wf src := by
  simp [run,CommonRoleCheckedMixedSource.run,Option.map_map,Function.comp_def]

/-- All premises at the outer entry are declaration well-formedness and source.
No checker, head-map, State, derivation or role success premise is required. -/
theorem run_success_iff (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles) (src : Source) :
    run env roles wf src = some (true,true) ↔
      ValidSource roles src.clauses ∧ Models env roles src ∧ AllDischarged env roles src := by
  cases checked : check roles src with
  | none =>
    have invalid : ¬ ValidSource roles src.clauses := by
      have h := CommonRoleSourceRoleObligations.check_accepts roles src.clauses
      change (check roles src).isSome = true ↔ _ at h
      simp only [checked,Option.isSome_none,Bool.false_eq_true,false_iff] at h
      exact h
    simp [run,checked,invalid]
  | some p =>
    have valid := ((CommonRoleSourceRoleObligations.check_exact roles src.clauses p).mp checked).2.2
    simp only [run,checked,Option.map_some,Option.some.injEq,Prod.mk.injEq,valid,true_and]
    rw [CommonRoleCheckedMixedSource.checked_solver_exact env roles wf awf src p checked,
      run_roles_exact env roles wf awf src p checked]

/-- Reordering or repeating source clauses/inequalities changes neither the
independent evidence-backed role predicate nor its conjunction. -/
theorem discharged_congr (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (left right : Source) (cs : ∀ c, c ∈ left.clauses ↔ c ∈ right.clauses)
    (os : ∀ q, q ∈ left.ordinary ↔ q ∈ right.ordinary) (c : Clause) :
    Discharged env roles left c ↔ Discharged env roles right c := by
  simp only [Discharged,CommonRoleCheckedMixedSource.derives_congr env roles left right cs os]

theorem all_discharged_congr (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (left right : Source) (cs : ∀ c, c ∈ left.clauses ↔ c ∈ right.clauses)
    (os : ∀ q, q ∈ left.ordinary ↔ q ∈ right.ordinary) :
    AllDischarged env roles left ↔ AllDischarged env roles right := by
  simp only [AllDischarged,cs,discharged_congr env roles left right cs os]

/-- Complete pair-observation invariance, not merely successful-case invariance. -/
theorem run_congr (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (left right : Source) (cs : ∀ c, c ∈ left.clauses ↔ c ∈ right.clauses)
    (os : ∀ q, q ∈ left.ordinary ↔ q ∈ right.ordinary) :
    run env roles wf left = run env roles wf right := by
  have valid : ValidSource roles left.clauses ↔ ValidSource roles right.clauses := by
    simp only [ValidSource,cs]
  have models := CommonRoleCheckedMixedSource.models_congr env roles left right cs os
  have discharge := all_discharged_congr env roles left right cs os
  cases lc : check roles left with
  | none =>
    have invalid := (run_none_iff env roles wf left).mp (by simp [run,lc])
    rw [show run env roles wf left = none by simp [run,lc]]
    exact ((run_none_iff env roles wf right).mpr (fun h => invalid (valid.mpr h))).symm
  | some p =>
    have vl := ((CommonRoleSourceRoleObligations.check_exact roles left.clauses p).mp lc).2.2
    cases rc : check roles right with
    | none =>
      have invalid := (run_none_iff env roles wf right).mp (by simp [run,rc])
      exact False.elim (invalid (valid.mp vl))
    | some q =>
      have ordinary : CommonRoleOpenPropagation.consistent (finish env roles wf left p) =
          CommonRoleOpenPropagation.consistent (finish env roles wf right q) := by
        have h := (CommonRoleCheckedMixedSource.checked_solver_exact env roles wf awf left p lc).trans
          (models.trans (CommonRoleCheckedMixedSource.checked_solver_exact env roles wf awf right q rc).symm)
        cases hl : CommonRoleOpenPropagation.consistent (finish env roles wf left p) <;>
          cases hr : CommonRoleOpenPropagation.consistent (finish env roles wf right q) <;> simp_all
      have rolesEq : runRoles env roles wf left p = runRoles env roles wf right q := by
        have h := (run_roles_exact env roles wf awf left p lc).trans
          (discharge.trans (run_roles_exact env roles wf awf right q rc).symm)
        cases hl : runRoles env roles wf left p <;> cases hr : runRoles env roles wf right q <;> simp_all
      simp only [run,lc,rc,Option.map_some,ordinary,rolesEq]

end Yulang.CommonRoleEvidenceDischarge
