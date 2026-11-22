import Yulang.GeneralDeclarativeWitnessRetainedCut355
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessWhereFresh355
open GeneralDeclarativeSparseWhere325 (atPosition plan planned compound_job)
open GeneralDeclarativeClauseBatch327 (Port make prepare)
open GeneralDeclarativeFreshWhere325 (seed)
open GeneralDeclarativeFootprint321 (stateNames)
open GeneralDeclarativeNewNames321 (before_after)
open GeneralDeclarativeHead320 (State)
open GeneralNominalCenteredHeadMatExpressions (Expr translateMany)
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralDeclarativeEmissionOperands322 (Compound)
open GeneralDeclarativeSourceEmission322 (Names useArg)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeGrowth327 (Extends)
open GeneralDeclarations (Clause Declaration)
open CommonRoleOutermostResolver (All₂)

theorem compound_center_above_start {jobs : List (Option Expr)} {start slot : Nat} {e : Expr}
    (has : jobs[slot]? = some (some e)) :
    start < (atPosition start jobs slot).center := by
  induction slot generalizing jobs start with
  | zero =>
    cases jobs with
    | nil => cases has
    | cons one tail =>
      have same : one = some e := Option.some.inj has
      subst one
      change start < start + 1
      omega
  | succ slot ih =>
    cases jobs with
    | nil => cases has
    | cons one tail =>
      cases one with
      | none => exact ih has
      | some prev =>
        exact Nat.lt_trans (by omega : start < start + 3)
          (ih (start := start + 3) has)

theorem actual_job_is_fresh {s : State} {keep : List Nat} {cap : Nat → Capture}
    {jobs : List (Option Expr)} {slot n : Nat} {e : Expr}
    (work : jobs[slot]? = some (some e)) (reserved : n ∈ stateNames s ++ keep) :
    n < (atPosition (seed s keep cap jobs) jobs slot).center :=
  Nat.lt_trans (before_after (List.mem_append_left _ reserved)) (compound_center_above_start work)

def FreshFrom (start : State) (keep : List Nat) (cl : Clause) (p : Port) : Prop :=
  ∀ i pat e, cl.arguments[i]? = some pat → p.code[i]? = some e → Compound pat →
    ∀ n ∈ stateNames start ++ keep, n < (p.input i).center

theorem fresh_make (s : State) (keep : List Nat) (cap : Nat → Capture) (cl : Clause) (codes : List Expr) :
    FreshFrom s keep cl (make s keep cap cl codes) := by
  intro i pat e source found compound
  have actual := planned source found
  rw [compound_job compound] at actual
  exact fun n old => actual_job_is_fresh actual old

theorem fresh_weakening {begin later : State} (keep : List Nat) {c : Clause} {p : Port}
    (grow : Extends begin later) (stored : FreshFrom later keep c p) : FreshFrom begin keep c p := by
  intro i pat e source found compound n old
  apply stored i pat e source found compound n
  rcases List.mem_append.mp old with prior|keep
  · exact List.mem_append_left _ (GeneralDeclarativeOpaqueConserve328.stateGrows grow prior)
  · exact List.mem_append_right _ keep

theorem weaken_ports {begin later : State} (keep : List Nat) {cs : List Clause} {ps : List Port}
    (grow : Extends begin later) (aligned : All₂ (FreshFrom later keep) cs ps) : All₂ (FreshFrom begin keep) cs ps := by
  induction aligned with
  | nil => exact .nil
  | cons a _ step => exact .cons (fresh_weakening keep grow a) step

theorem actual_ports {s t : State} {keep : List Nat} {cap : Nat → Capture}
    {cs : List Clause} {registry interpretation} {ports : List Port}
    (ran : prepare registry interpretation keep cap s cs = some (t,ports)) :
    All₂ (FreshFrom s keep) cs ports := by
  induction cs generalizing s t ports with
  | nil =>
    have eq := (Prod.mk.inj (Option.some.inj ran)).2
    subst ports
    exact .nil
  | cons first rest ih =>
    cases looked : translateMany registry interpretation (first.arguments.map normalize) with
    | none => simp [prepare,looked] at ran
    | some codes =>
      let jobs := plan first.arguments codes
      let stage := GeneralDeclarativeFreshInputs325.prepared s keep cap jobs
      cases later : prepare registry interpretation keep cap stage rest with
      | none =>
        have no : prepare registry interpretation keep cap
            (GeneralDeclarativeFreshInputs325.prepared s keep cap (plan first.arguments codes)) rest = none := later
        simp [prepare,looked,no] at ran
      | some result =>
        obtain ⟨done,other⟩ := result
        have yes : prepare registry interpretation keep cap
            (GeneralDeclarativeFreshInputs325.prepared s keep cap (plan first.arguments codes)) rest =
            some (done,other) := later
        have output : (done,make s keep cap first codes :: other) = (t,ports) := by
          simpa [prepare,looked,yes] using ran
        cases output
        have tail := ih later
        have cover := GeneralDeclarativeClauseBatch327.make_grows s keep cap jobs
        exact .cons (fresh_make s keep cap first codes) (weaken_ports keep cover tail)

theorem count_translations {r i} {args : List Pattern} {out : List Expr}
    (h : translateMany r i args = some out) : args.length = out.length := by
  induction args generalizing out with
  | nil => cases Option.some.inj h; rfl
  | cons a tail ih =>
    have ⟨first,_,remaining⟩ := GeneralSourceMetadataExprDomain291.bind_success h
    have ⟨rest,made,exact⟩ := GeneralSourceMetadataExprDomain291.bind_success remaining
    cases Option.some.inj exact
    simp only [List.length_cons,ih made]

open GeneralDeclarativeClausePlacement327 (portAt placement located)
open GeneralDeclarativeEmissionForest322 (Placement)

theorem emitted_compound_not_any_protected_name {s t : State} {keep : List Nat} {cap : Nat → Capture}
    {cs : List Clause} {registry interpretation} {ports : List Port}
    (ran : prepare registry interpretation keep cap s cs = some (t,ports))
    (unique : (cs.map Clause.id).Nodup) {cl : Clause} (used : cl ∈ cs)
    {i : Nat} {p : Pattern} (source : cl.arguments[i]? = some p) (compound : Compound p)
    {names : Names} {n : Nat} (old : n ∈ stateNames s ++ keep) (targets : Clause → Nat → Nat) :
    n < (useArg names ((placement cs ports targets).compound cl i) p).center := by
  have fill := (GeneralDeclarativeClauseBatch327.read_order ran).2
  obtain ⟨digit,seen,known⟩ := located fill unique used
  obtain ⟨actual,found,age⟩ := located (actual_ports ran) unique used
  have same := Option.some.inj (found.symm.trans seen)
  subst actual
  have existsExpr : ∃ e, digit.code[i]? = some e := by
    have count := count_translations known.1
    have count2 : cl.arguments.length = digit.code.length := by simpa using count
    obtain ⟨valid,_⟩ := List.getElem?_eq_some_iff.mp source
    have atCode : i < digit.code.length := count2 ▸ valid
    exact ⟨digit.code[i],List.getElem?_eq_getElem atCode⟩
  obtain ⟨e,code⟩ := existsExpr
  have exact := age i p e source code compound n old
  unfold useArg
  cases h : normalize p with
  | var binder => exact False.elim (compound binder h)
  | app | record | variant | join => simpa [placement,seen] using exact

end Yulang.GeneralDeclarativeWitnessWhereFresh355
