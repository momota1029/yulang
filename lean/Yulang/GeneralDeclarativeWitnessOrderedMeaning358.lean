import Yulang.GeneralDeclarativeWitnessOrderedReplay358

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessOrderedMeaning358
open GeneralDeclarativeWitnessOrderedReplay358 (Local Tree Forest)
open GeneralDeclarativeWitnessDeclaredState357 (Current authoredRegistry ModelsCurrent Views)
open GeneralDeclarativeWitnessClassifyVariance357 (SourceChecked roleView roleView_span)
open GeneralDeclarativeWitnessProjectionRule358 (Rule Evidence dictionary_sound root_declared)
open GeneralDeclarativeWitnessModeCoverage357 (Coverage)
open GeneralDeclarativeWitnessCompiler350 (printDemand DemandCode)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeEntailment320 (Holds)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (All₂ Classify Dictionary Resolves Summarizes Result)

theorem local_rule {a s d} (l : Local a s d) : Rule a s d (.selected l.key l.kids) := by
  cases l with
  | joined read => exact .prior (GeneralDeclarativeWitnessJoinedCheck357.replay_rule read)
  | projection reached => exact GeneralDeclarativeWitnessProjectionCheck358.rule reached

theorem local_declared {a s d} (l : Local a s d) (checked : SourceChecked s) :
    Declared (authoredRegistry s) d := by
  cases l with
  | joined read =>
    have member : read.impl ∈ (roleView s d.role).declarations := by
      rw [read.localRead.single]
      exact List.mem_cons_self
    have here := (roleView_span s d.role read.impl).mp member
    have legal := checked.2 read.impl here.1
    exact GeneralDeclarativeWitnessRootDeclared357.written_root_declared read.localRead.body legal.signature
      legal.identified.2.2.1 here.2
  | projection read => exact root_declared read.chosen checked

mutual
def diag {a s path d} (t : Tree a s path d) : CommonRoleOutermostResolver.Tree :=
  match t with | .node l rest => .selected l.key (diags rest)
termination_by sizeOf t

def diags {a s path i ds} (t : Forest a s path i ds) : List CommonRoleOutermostResolver.Tree :=
  match t with
  | .nil => []
  | .cons node rest => diag node :: diags rest
termination_by sizeOf t
end

mutual
def dict {a s path d} (t : Tree a s path d) : Dictionary :=
  match t with | .node l rest => .node l.key (dicts rest)
termination_by sizeOf t

def dicts {a s path i ds} (t : Forest a s path i ds) : List Dictionary :=
  match t with
  | .nil => []
  | .cons node rest => dict node :: dicts rest
termination_by sizeOf t
end

theorem declarative_tree {a s path d} (t : Tree a s path d) :
    Resolves (Rule a s) d (diag t) ∧ Summarizes (diag t) (.selected (dict t)) := by
  refine @Tree.rec a s
    (fun _ d node => Resolves (Rule a s) d (diag node) ∧ Summarizes (diag node) (.selected (dict node)))
    (fun _ _ ds more => All₂ (Resolves (Rule a s)) ds (diags more) ∧
      All₂ Summarizes (diags more) ((dicts more).map Result.selected))
    ?_ ?_ ?_ path d t
  · intro d p l more obtained
    rw [diag.eq_def,dict.eq_def]
    exact ⟨.selected (local_rule l) obtained.1,.selected obtained.2 (.selected rfl)⟩
  · intro p i
    rw [diags.eq_def,dicts.eq_def]
    exact ⟨.nil,.nil⟩
  · intro p i d ds node more read tail
    rw [diags.eq_def,dicts.eq_def]
    exact ⟨.cons read.1 tail.1,.cons read.2 tail.2⟩

theorem classify {a s path d} (t : Tree a s path d) :
    Classify (Rule a s) d (.selected (dict t)) :=
  ⟨diag t,(declarative_tree t).1,(declarative_tree t).2⟩

theorem declared_tree {a s path d} (t : Tree a s path d) (cert : SourceChecked s) :
    Declared (authoredRegistry s) d := by
  cases t with
  | node l rest => exact local_declared l cert

def fixed {a s d} : Local a s d → List Equation
  | .joined a => a.localRead.body.finished.fixed
  | .projection a => a.chosen.body.finished.fixed

theorem local_fixed {a s d} (l : Local a s d) (m : Assignment) (v : Views) (fit : ModelsCurrent s m v) :
    (fixed l).map Equation.left = d.outputs.map GeneralSourceState.Output.target ∧
      ∀ row ∈ fixed l,Holds m row := by
  cases l with
  | joined a => exact GeneralDeclarativeWitnessDeclaredState357.output_meaning a.localRead.body m fit.1
  | projection a => exact GeneralDeclarativeWitnessDeclaredState357.output_meaning a.chosen.body m fit.1

structure Entry where
  path : List Nat
  request : DemandCode
  equations : List Equation

def entry {a s d} (p : List Nat) (l : Local a s d) : Entry :=
  ⟨p,printDemand d,fixed l⟩

mutual
def ledger {a s p d} (t : Tree a s p d) : List Entry :=
  match t with | .node l more => entry p l :: ledgerList more
termination_by sizeOf t

def ledgerList {a s p i ds} (t : Forest a s p i ds) : List Entry :=
  match t with
  | .nil => []
  | .cons node rest => ledger node ++ ledgerList rest
termination_by sizeOf t
end

def Entry.Holds (m : Assignment) (e : Entry) : Prop :=
  e.equations.map Equation.left = e.request.2.2.map Prod.snd ∧ ∀ row ∈ e.equations,GeneralDeclarativeEntailment320.Holds m row

theorem entry_exact {a s d} (p : List Nat) (l : Local a s d) (m : Assignment) (v : Views)
    (fit : ModelsCurrent s m v) : (entry p l).Holds m := by
  have got := local_fixed l m v fit
  change (fixed l).map Equation.left =
     (d.outputs.map GeneralDeclarativeWitnessCompiler350.pair).map Prod.snd ∧ _
  rw [List.map_map]
  exact got

theorem ledger_exact {a s p d} (t : Tree a s p d) (m : Assignment) (v : Views)
    (fit : ModelsCurrent s m v) :
    ∀ row ∈ ledger t,row.Holds m := by
  refine @Tree.rec a s
    (fun _ _ node => ∀ x ∈ ledger node,x.Holds m)
    (fun _ _ _ more => ∀ x ∈ ledgerList more,x.Holds m) ?_ ?_ ?_ p d t
  · intro d p l more ih row here
    rw [ledger.eq_def] at here
    rcases List.mem_cons.mp here with rfl|later
    · exact entry_exact p l m v fit
    · exact ih row later
  · intro p i row here
    rw [ledgerList.eq_def] at here
    cases here
  · intro p i d ds node rest first later row used
    rw [ledgerList.eq_def] at used
    exact (List.mem_append.mp used).elim (first row) (later row)

end Yulang.GeneralDeclarativeWitnessOrderedMeaning358
