import Yulang.GeneralDeclarativeI65SourceTree365
import Yulang.GeneralDeclarativeWitnessTree349

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65
open CommonRoleOutermostResolver (All₂ Tree Frontier Dictionary Classify Resolves Summarizes Result)
open GeneralDeclarativeWitnessTree349 (dictionaryTree dictionaryForest)
open GeneralDeclarations (Declaration)

/-- Next required adapter: from the actual declarative selected frontier
to the already proved model-free assembly. This interface does not
supply candidate classifications or assume semantic truth. -/
def ProvidesSource (s : State) (rule : Request → Frontier Request → Prop) : Prop :=
  ∀ q key kids, rule q (.selected key kids) →
    ∃ row : Declaration, row.id = key ∧ Nonempty (SourceNode s q row kids)

variable {s : State} {rule : Request → Frontier Request → Prop}

mutual
theorem lower_tree (ready : ProvidesSource s rule) (t : Tree)
    (charted : Resolves rule q t) (complete : Summarizes t (.selected dict)) :
    ∃ fixed, t = dictionaryTree dict ∧ SourceTree s q dict fixed := by
  cases charted with
  | pending _ => cases complete
  | rejected _ => cases complete
  | ambiguous _ => cases complete
  | selected h kids =>
    obtain ⟨decl,identity,⟨node⟩⟩ := ready _ _ _ h
    cases complete with
    | selected traces joined =>
      cases joined with
      | selected success =>
        subst_vars
        obtain ⟨receipts,same,proved⟩ := lower_forest ready _ _ kids traces
        exact ⟨captureReceipt node :: receipts,by simp only [dictionaryTree,same],.node node proved⟩
termination_by sizeOf t

theorem lower_forest (ready : ProvidesSource s rule) (trees : List Tree) (dictionaries : List Dictionary)
    (charted : All₂ (Resolves rule) requests trees)
    (complete : All₂ Summarizes trees (dictionaries.map Result.selected)) :
    ∃ fixed, trees = dictionaryForest dictionaries ∧ SourceForest s requests dictionaries fixed := by
  cases dictionaries with
  | nil =>
    cases complete; cases charted
    exact ⟨[],by rw [dictionaryForest],.nil⟩
  | cons dict more =>
    cases complete with
    | cons now rest =>
      cases charted with
      | cons first after =>
        obtain ⟨before,left,worked⟩ := lower_tree ready _ first now
        obtain ⟨later,right,continued⟩ := lower_forest ready _ _ after rest
        exact ⟨before ++ later,by simp only [dictionaryForest,left,right],.cons worked continued⟩
termination_by sizeOf trees
end

/-- Proven bridge on the source-assembly side of the frozen I-65
interface. The missing part is deriving ProvidesSource for the
generalized independent language classifier, not a model-side premise. -/
theorem classified_source_assembly (ready : ProvidesSource s rule)
    (found : Classify rule q (.selected dict)) :
    ∃ trace fixed, Resolves rule q trace ∧ trace = dictionaryTree dict ∧
      ∀ (m : Model), Fits s m →
        TreeEvidence s m q dict fixed ∧ ∀ c ∈ fixed, ∀ row ∈ c.rows,
          GeneralDeclarativeEntailment320.Holds m.assignment row := by
  obtain ⟨trace,charted,chosen⟩ := found
  obtain ⟨fixed,exact,lowered⟩ := lower_tree ready _ charted chosen
  refine ⟨trace,fixed,charted,exact,?_⟩
  intro m fits
  have proof := source_tree_sound lowered m fits
  exact ⟨proof,every_fixed_row_comes_from_the_same_model proof⟩

end Yulang.GeneralDeclarativeI65
