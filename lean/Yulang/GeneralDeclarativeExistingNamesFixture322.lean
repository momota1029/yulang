import Yulang.GeneralDeclarativeExistingNames322
import Yulang.GeneralDeclarativeExistingFixtureRead322

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeExistingNamesFixture322
open GeneralDeclarativeExistingNames322 (Pools Covers recover recoverForest recovered_forest)
open GeneralDeclarativeNameFill322 (input associated zipNames)
open GeneralDeclarativeNameLookup322 (find singleton_exact)
open GeneralDeclarativeSubstitution320 (logical)
open GeneralDeclarativeExistingFixture322 (state parentCapture child equations)
open GeneralDeclarativeExistingFixtureRead322 (hit centerPath namedPath whereRead)
open GeneralDeclarativeExampleSource320 (registry interp)
open GeneralDeclarativeFreshForest321 (ClauseCode)
open GeneralDeclarationExamples (wrap)
open GeneralDeclarativeSourceCodes321 (clauseCodes)
open GeneralDeclarativeExistingClause322 (Existing)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open CommonRoleOutermostResolver (All₂)

abbrev rawCode : ClauseCode := ⟨[.variable 0],[(1,.variable 1)]⟩
abbrev names : Pools := ⟨[⟨[8],[9],[10]⟩],[[12]]⟩

theorem source_tables : clauseCodes registry interp wrap.requirements = some [rawCode] := rfl

theorem input_readback :
    input state parentCapture (.variable 0) ⟨[8],[9],[10]⟩ = some ⟨8,9,10⟩ := by
  have lo : find state [8] (logical parentCapture .lower (.variable 0)) = some 8 :=
    singleton_exact whereRead.1
  have mid : find state [9] (logical parentCapture .actual (.variable 0)) = some 9 :=
    singleton_exact whereRead.2.1
  have hi : find state [10] (logical parentCapture .upper (.variable 0)) = some 10 :=
    singleton_exact whereRead.2.2
  simp [input,lo,mid,hi]

theorem out_readback :
    associated state parentCapture (1,.variable 1) [12] = some ⟨1,12⟩ := by
  have yes : find state [12] (logical parentCapture .actual (.variable 1)) = some 12 :=
    singleton_exact namedPath
  simp [associated,yes]

theorem exact_existing_child :
    recoverForest state parentCapture wrap.requirements [(rawCode,names)] = some [child] := by
  simp [recoverForest,recover,zipNames,input_readback,out_readback]

end Yulang.GeneralDeclarativeExistingNamesFixture322
