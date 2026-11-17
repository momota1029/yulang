import Yulang.GeneralDictionaryUpper230Joint
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryUpper230Closure
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229
open GeneralDictionaryUpper230Step
open GeneralDictionaryUpper230Administrative GeneralDictionaryUpper230Joint

def EqualityClosed : Prop := ∀ first last,
  first ∈ GeneralNominalState.sources after.core.erased.current.context.state →
  last ∈ GeneralNominalState.sources after.core.erased.current.context.state →
  GeneralNominalCenteredHeadMatStepKernel.Equal after first last →
  GeneralNominalFeedbackSteps.RawEqual after.core.erased.current first last

theorem stable_of_equality_closed (closed : EqualityClosed) :
    GeneralDictionaryDefaultKernel208.Stable registry after root := by
  intro focus generated next action
  have same := generated_only focus generated
  cases action with
  | administrative action =>
    cases action with
    | enqueue linked absent => exact absent _ (List.mem_singleton_self _) same.symm
    | refresh context certificate identity member unknown known =>
      exact no_refresh context certificate member unknown known
    | reobserve revision certificate improved => exact no_reobserve revision improved
    | equate first last one two equal novel => exact novel (closed first last one two equal)
  | refresh focus context certificate identity member unknown known =>
    exact no_refresh context certificate member unknown known
  | install effect enabled novel => exact no_install effect enabled same
  | merge first last one two same novel =>
    cases List.mem_singleton.mp one
    cases List.mem_singleton.mp two
    exact novel (.refl _)

theorem equality_closed_of_stable
    (stable : GeneralDictionaryDefaultKernel208.Stable registry after root) : EqualityClosed := by
  classical
  intro first last one two equal
  apply Classical.byContradiction
  intro novel
  exact stable root .root _ (.administrative (.equate root first last one two equal novel))

theorem stable_iff_equality_closed :
    GeneralDictionaryDefaultKernel208.Stable registry after root ↔ EqualityClosed :=
  ⟨equality_closed_of_stable,stable_of_equality_closed⟩

end Yulang.GeneralDictionaryUpper230Closure
