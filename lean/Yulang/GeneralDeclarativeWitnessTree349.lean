import Yulang.GeneralDeclarativeWitnessHeader349

namespace Yulang.GeneralDeclarativeWitnessTree349
open CommonRoleOutermostResolver (Tree Dictionary Result All₂ Resolves Classify classification classification_exact)
open GeneralDeclarativeWitnessProblem349 (Problem)
open GeneralDeclarativeWitnessHeader349 (Header check)

mutual
def eqTree : Tree → Tree → Bool
  | .pending,.pending | .ambiguous,.ambiguous | .rejected,.rejected => true
  | .selected k xs,.selected l ys => decide (k = l) && eqForest xs ys
  | _,_ => false
termination_by x _ => sizeOf x

def eqForest : List Tree → List Tree → Bool
  | [],[] => true
  | x::xs,y::ys => eqTree x y && eqForest xs ys
  | _,_ => false
termination_by xs _ => sizeOf xs
end

mutual
theorem eq_tree (a b : Tree) : eqTree a b = true ↔ a = b := by
  cases a <;> cases b
  case selected.selected ak xs bk ys =>
    rw [eqTree.eq_def,Bool.and_eq_true,decide_eq_true_eq,eq_forest xs ys,Tree.selected.injEq]
  all_goals simp [eqTree.eq_def]
termination_by sizeOf a

theorem eq_forest (a b : List Tree) : eqForest a b = true ↔ a = b := by
  cases a <;> cases b
  case cons.cons first rest last tail =>
    rw [eqForest.eq_def,Bool.and_eq_true,eq_tree first last,eq_forest rest tail,List.cons.injEq]
  all_goals simp [eqForest.eq_def]
termination_by sizeOf a
end

mutual
def dictionaryTree : Dictionary → Tree
  | .node k kids => .selected k (dictionaryForest kids)
termination_by x => sizeOf x

def dictionaryForest : List Dictionary → List Tree
  | [] => []
  | x::xs => dictionaryTree x :: dictionaryForest xs
termination_by xs => sizeOf xs
end

mutual
theorem dictionary_injective (a b : Dictionary) (same : dictionaryTree a = dictionaryTree b) : a = b := by
  cases a with
  | node ak ac =>
    cases b with
    | node bk bc =>
      simp only [dictionaryTree,Tree.selected.injEq] at same
      rw [same.1,dictionary_list_injective ac bc same.2]
termination_by sizeOf a

theorem dictionary_list_injective (a b : List Dictionary) (same : dictionaryForest a = dictionaryForest b) : a = b := by
  cases a <;> cases b
  · rfl
  · simp [dictionaryForest] at same
  · simp [dictionaryForest] at same
  · simp only [dictionaryForest,List.cons.injEq] at same
    rw [dictionary_injective _ _ same.1,dictionary_list_injective _ _ same.2]
termination_by sizeOf a
end

def eqResult : Result → Result → Bool
  | .pending,.pending | .ambiguous,.ambiguous | .rejected,.rejected => true
  | .selected a,.selected b => eqTree (dictionaryTree a) (dictionaryTree b)
  | _,_ => false

theorem eq_result (a b : Result) : eqResult a b = true ↔ a = b := by
  cases a <;> cases b <;> simp only [eqResult,Bool.false_eq_true, eq_tree,Result.selected.injEq,reduceCtorEq] <;>
    constructor <;> intro h <;> first | exact h | rfl | contradiction | exact dictionary_injective _ _ h | exact congrArg dictionaryTree h

structure Report where
  tree : Tree
  result : Result
  outputs : List GeneralSourceState.Output

/-- Only the actual already-replayed tree is the comparison basis.
This function evaluates a finite tree; it does not decide resolution. -/
def agrees (p : Problem) (accepted : Tree) (report : Report) : Bool :=
  (eqTree report.tree accepted && eqResult report.result (classification accepted)) &&
    GeneralDeclarativeWitnessTargets349.same_requests p report.outputs

theorem exact_report {p : Problem} {accepted : Tree} {report : Report} (good : agrees p accepted report = true) :
    report.tree = accepted ∧ report.result = classification accepted ∧ report.outputs = p.demand.outputs := by
  obtain ⟨diag,targets⟩ := GeneralDeclarativeWitnessProblem349.splitAnd good
  obtain ⟨actualTree,actualResult⟩ := GeneralDeclarativeWitnessProblem349.splitAnd diag
  exact ⟨(eq_tree ..).mp actualTree,(eq_result ..).mp actualResult,
    (GeneralDeclarativeWitnessTargets349.exact_targets _ _).mp targets⟩

theorem classifies {p : Problem} {accepted : Tree} {report : Report}
    {rule : GeneralDeclarativeDemand320.Demand → CommonRoleOutermostResolver.Frontier GeneralDeclarativeDemand320.Demand → Prop}
    (worked : Resolves rule p.demand accepted) (good : agrees p accepted report = true) :
    Classify rule p.demand report.result := by
  have literal := exact_report good
  exact ⟨accepted,worked,(classification_exact _ _).mp literal.2.1.symm⟩

end Yulang.GeneralDeclarativeWitnessTree349
