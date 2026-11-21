import Yulang.GeneralDeclarativeFreshExact321
import Yulang.GeneralDeclarativeFixtureGenerate321

namespace Yulang.Cycle321Readback

open GeneralDeclarativeExampleSource320 (registry interp state capture model valid)
open GeneralDeclarationExamples (wrap)
open GeneralDeclarativeFreshForest321 (ClauseCode allCodes children)
open GeneralDeclarativeFreshCalls321 (seed)
open GeneralDeclarativeSourceCodes321 (clauseCodes)
open GeneralDeclarativeNewNames321 (supply)
open GeneralDeclarativeFresh321 (extend)

abbrev table : List ClauseCode := [⟨[.variable 0],[(1,.variable 1)]⟩]
abbrev keep : List Nat := [1,3,5,6,55]
abbrev emitted : List GeneralDeclarativeHead320.Equation :=
  [⟨56,.variable 3⟩,⟨57,.variable 3⟩,⟨58,.variable 3⟩,⟨59,.variable 5⟩]

theorem source_table : clauseCodes registry interp wrap.requirements = some table := rfl

theorem exact_labels : children capture (seed state keep (allCodes capture table)) wrap.requirements table =
    [⟨2,[⟨56,57,58⟩],[⟨1,59⟩]⟩] := rfl

theorem literal_rows : supply state keep (allCodes capture table) = emitted := rfl

theorem actual_compiler_readback :
    GeneralDeclarativeBatch320.zipFacts
      (GeneralDeclarativeNodeFacts320.clauseFacts registry interp capture) wrap.requirements
      [⟨2,[⟨56,57,58⟩],[⟨1,59⟩]⟩] = some emitted :=
  GeneralDeclarativeFreshExact321.exact_forest source_table capture (seed state keep (allCodes capture table))

theorem old_protected_in_extended_model :
    GeneralDeclarativeHead320.Models (GeneralDeclarativeEntailment320.appendFacts state emitted)
      (extend model emitted) ∧ extend model emitted 55 = model 55 := by
  have kept := GeneralDeclarativeNewNames321.old_plus_extra state keep (allCodes capture table) model valid
  exact ⟨kept.1,kept.2 55 (List.mem_append_right _ (by decide +kernel))⟩

#print axioms source_table
#print axioms exact_labels
#print axioms literal_rows
#print axioms actual_compiler_readback
#print axioms old_protected_in_extended_model

end Yulang.Cycle321Readback
