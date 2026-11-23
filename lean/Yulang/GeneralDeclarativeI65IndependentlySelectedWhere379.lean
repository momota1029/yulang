import Yulang.GeneralDeclarativeI65PreparedOwnBody376
import Yulang.GeneralDeclarativeWitnessSelectedNonpointChild363

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65
open GeneralDeclarativeWitnessSeparateEndpointAuthors362 (Ordered)
open GeneralDeclarativeWitnessSelectedNonpointRoot363 (Root selectedLayout)
open GeneralDeclarativeWitnessSelectedNonpointChild363 (Child path)
open GeneralDeclarativeWitnessNonpointPort362 (frame)
open GeneralDeclarativeWitnessCrossOwnerReceiver362 (asked)
open GeneralDeclarativeWitnessCompiler350 (Finished execute fixedBatch)
open GeneralDeclarativeWitnessNativePreparation360 (context)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarativeWitnessLiteral349 (preserves_iff)
open GeneralDeclarativeEntailment320 (Holds)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarativeWitnessNativeInstall360 (Fits NativeViews)

/-- This root is already independently elected in C363. The exact
compiler body uses the chosen captures and literal where stage; its
empty fixed-output list is a source fact about this represented root. -/
theorem selected_native_root_runs_exact_where_body
    {contra : Bool} {x : Ordered contra} {env : Environment} (root : Root x env) :
    execute (context env asked root.body.impl (selectedLayout x.after.final root.chosen)) =
      some ⟨root.body.stage,[],root.body.kids⟩ := by
  have empty : fixedBatch (context env asked root.body.impl
      (selectedLayout x.after.final root.chosen)) root.body.ports = some [] := rfl
  simp [execute,root.body.ranPrepare,root.body.ranWhere,empty] <;>
    exact ⟨rfl,rfl⟩

/-- The child is the real emitted occurrence, not a reconstructed
equal demand at a different path. -/
theorem selected_native_root_keeps_literal_child_occurrence
    {contra : Bool} {x : Ordered contra} {env : Environment} (root : Root x env) :
    children ⟨frame.occurrence,asked⟩ root.body.kids =
      [⟨path.occurrence,root.occurrence⟩] := by
  rw [root.ordered]
  rfl

theorem child_fit_contains_parent_literal_where_rows
    {contra : Bool} {x : Ordered contra} {env : Environment} {root : Root x env}
    (child : Child root) (m : Assignment) (v : NativeViews)
    (fit : GeneralDeclarativeWitnessNativeInstall360.Fits child.world m v) :
    (∀ eq ∈ root.body.whereRows,eq ∈ child.body.state.equations ∧ Holds m eq) ∧
      root.body.impl = root.chosen.impl ∧ child.prepared.impl = child.chosen.impl ∧
      child.binder.center = root.span.center := by
  have stays := (preserves_iff ..).mp child.stays
  refine ⟨?_,root.actual,child.actual,child.center⟩
  intro eq added
  have inParent : eq ∈ root.world.ordinary.equations := List.mem_append_right _ added
  have inChild := stays.equations inParent
  exact ⟨inChild,fit.1.2 _ inChild⟩

/-- The nonempty physical input comes from independent earlier writers.
The selected parent and actual selected child preserve their ordinary
footprint and literal board, not just a conveniently equal value. -/
theorem both_selected_occurrences_keep_original_native_world
    {contra : Bool} {x : Ordered contra} {env : Environment} {root : Root x env}
    (child : Child root) :
    GeneralDeclarativeGrowth327.Extends x.after.final.ordinary child.world.ordinary ∧
      child.world.board = x.after.final.board := by
  have stayed : GeneralDeclarativeGrowth327.Extends x.after.final.ordinary root.world.ordinary :=
    (preserves_iff ..).mp root.body.retained
  exact ⟨GeneralDeclarativeGrowth327.trans stayed ((preserves_iff ..).mp child.stays),rfl⟩

theorem child_fit_keeps_all_three_released_originals
    {contra : Bool} {x : Ordered contra} {env : Environment} {root : Root x env}
    (origin : GeneralDeclarativeWitnessSeparateEndpointAuthors362.run contra = some x)
    (child : Child root) (m : Assignment) (v : NativeViews)
    (fit : GeneralDeclarativeWitnessNativeInstall360.Fits child.world m v) :
    ∃ lo center hi, v 301 = some lo ∧ v 302 = some center ∧ v 303 = some hi := by
  have live := (GeneralDeclarativeWitnessSelectedNonpointChild363.returned_model_has_prior_author_and_child_state
    child m v fit).2
  exact (GeneralDeclarativeWitnessBackedNativeInput363.source_evidence_agrees_in_every_model
    origin root.ready m v live).2.2.2.2

end Yulang.GeneralDeclarativeI65
