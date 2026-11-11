import Yulang.GeneralDictionaryHeadlessExamples

/-!
# Successful dictionary preparation does not discharge root readiness

The general source state can retain unresolved lower-head observations while
exact input identities and all dictionary equations materialize successfully.
This regression prevents using the partial materializer as candidate resolution
or as a proof that the all-unnamed-heads readiness guard may be omitted.
-/
namespace Yulang.GeneralDictionaryHeadlessPendingBoundary
open GeneralDictionaryHeadlessFixture
open GeneralDictionaryHeadlessExamples (recipe tree_prepared)
open GeneralDictionaryHeadlessPreparation (prepare)
open GeneralSourceState

/-- Every unnamed input is needed, including positions whose head is a variable. -/
def allInputs : Needed rootDemand := fun _ => True

theorem root_still_pending : RootPending state rootDemand allInputs := by
  refine ⟨⟨0, by decide⟩, trivial, ?_⟩
  rintro ⟨slot, _, known⟩
  exact known rfl

/-- The full checked two-node recipe succeeds while the source demand remains
pending. This is a materialization theorem, not permission to select the impl. -/
theorem preparation_with_pending :
    prepare registry registry_checked (fun _ => frame) recipe = some tree ∧
      RootPending state rootDemand allInputs := ⟨tree_prepared, root_still_pending⟩

end Yulang.GeneralDictionaryHeadlessPendingBoundary
