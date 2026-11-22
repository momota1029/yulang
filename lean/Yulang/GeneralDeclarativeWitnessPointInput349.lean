import Yulang.GeneralDeclarativeWitnessGround349
import Yulang.GeneralDeclarativeWitnessClassify334

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessPointInput349
open GeneralDeclarations (Declaration Registry)
open GeneralDeclarativeWitnessProblem349 (Problem)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeOpaqueNominal328 (point)
open GeneralCandidateInspection (Primitive)
open GeneralSourceMetadataBundle291 (SourceBundle registry)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralDeclarativeWitnessGround349 (isRow is_row occurs safeRows)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralDeclarationPatterns (Pattern normalize)

/-- This small input portal is supplied by the caller's source manifest.
The solver's finite report cannot supply or replace the anchor. -/
structure PointProblem where
  problem : Problem
  atName : Nat
  kind : Primitive

abbrev lit (p : PointProblem) := point p.atName

def captureIs (p : PointProblem) (a : Capture) : Bool :=
  decide (a.lower = p.atName ∧ a.center = p.atName ∧ a.upper = p.atName)

theorem capture_exact {p : PointProblem} {a : Capture} (yes : captureIs p a = true) :
    a = lit p := by
  obtain ⟨l,c,u⟩ := of_decide_eq_true yes
  cases a
  subst_vars
  rfl

def pointArgs (p : PointProblem) : Bool :=
  match p.problem.demand.arguments with
  | [a] => captureIs p a
  | _ => false

theorem args_exact {p : PointProblem} (yes : pointArgs p = true) :
    p.problem.demand.arguments = [lit p] := by
  unfold pointArgs at yes
  split at yes
  · rename_i a eq
    exact eq.trans (congrArg (fun x => [x]) (capture_exact yes))
  · cases yes

def candidates (p : PointProblem) (s : SourceBundle) : List Declaration :=
  (registry s).declarations.filter (fun d => decide (d.role = p.problem.demand.role))

def pick (p : PointProblem) (s : SourceBundle) : Option Declaration :=
  match candidates p s with
  | [d] => some d
  | _ => none

theorem picked {p : PointProblem} {s : SourceBundle} {d : Declaration}
    (h : pick p s = some d) :
    d ∈ (registry s).declarations ∧ d.role = p.problem.demand.role ∧
      ∀ x ∈ (registry s).declarations, x.role = p.problem.demand.role → x = d := by
  unfold pick at h
  split at h
  · rename_i only eq
    have equal : only = d := Option.some.inj h
    subst d
    have member : only ∈ candidates p s := eq.symm ▸ List.mem_cons_self
    obtain ⟨there,role⟩ := List.mem_filter.mp member
    refine ⟨there,of_decide_eq_true role,?_⟩
    intro x present fits
    have new : x ∈ candidates p s := List.mem_filter.mpr ⟨present,decide_eq_true fits⟩
    exact List.mem_singleton.mp (eq ▸ new)
  · cases h

def printed (p : PointProblem) (s : SourceBundle) (d : Declaration) : Option Nat :=
  match d.head with
  | [.app name []] =>
    match translate (registry s).constructors (interpretation s.snapshot) (.app name []) with
    | none => none
    | some e => if isRow 0 p.kind ⟨0,e⟩ then some name else none
  | _ => none

theorem head_exact {p : PointProblem} {s : SourceBundle} {d : Declaration} {n : Nat}
    (yes : printed p s d = some n) :
    d.head = [.app n []] ∧ translate (registry s).constructors (interpretation s.snapshot)
      (normalize (.app n [])) = some (.primitive p.kind []) := by
  unfold printed at yes
  split at yes
  · rename_i name eq
    cases read : translate (registry s).constructors (interpretation s.snapshot) (.app name []) with
    | none =>
      rw [read] at yes
      cases yes
    | some e =>
      rw [read] at yes
      change (if isRow 0 p.kind ⟨0,e⟩ then some name else none) = some n at yes
      by_cases rowYes : isRow 0 p.kind ⟨0,e⟩ = true
      · rw [ite_eq_left rowYes] at yes
        have same : name = n := Option.some.inj yes
        subst n
        have code := congrArg GeneralDeclarativeHead320.Equation.right (is_row.mp rowYes)
        exact ⟨eq,read.trans (congrArg some code.symm)⟩
      · rw [ite_eq_right rowYes] at yes
        cases yes
  · cases yes

def anchorChecks (p : PointProblem) : Bool :=
  (pointArgs p && safeRows p.problem.state) && occurs p.problem.state p.atName p.kind

end Yulang.GeneralDeclarativeWitnessPointInput349
