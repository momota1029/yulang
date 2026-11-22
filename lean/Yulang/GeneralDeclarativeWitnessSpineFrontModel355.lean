import Yulang.GeneralDeclarativeWitnessSpineFrontFixture355
import Yulang.GeneralDeclarativeWitnessSpineDeepModel355
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65000
set_option maxHeartbeats 75000000
namespace Yulang.GeneralDeclarativeWitnessSpineFrontModel355
open GeneralDeclarativeWitnessSpineFront355 (Found Wire read root_sound exact_sources)
open GeneralDeclarativeWitnessSpineFrontFixture355 (source code test independently_parsed_entire_five_node_tree)
open GeneralDeclarativeWitnessGrandchildModel355 (model)
open GeneralDeclarativeWitnessCovariantOrigin353 (Valuation)
open GeneralDeclarativeWitnessTypedEvidence355 (Evidence)
open GeneralDeclarativeHead320 (State Models)

theorem established_model {s : State} {w : Wire} (got : code = some (s,w)) : Models s model := by
  unfold code at got
  cases built : GeneralDeclarativeWitnessSpineDeepFixture355.data with
  | none => simp [built] at got
  | some tuple =>
    obtain ⟨state,root,chain⟩ := tuple
    rw [built] at got
    have exactState := congrArg Prod.fst (Option.some.inj got)
    have same : state = s := exactState
    cases same
    exact GeneralDeclarativeWitnessSpineDeepModel355.fits built

theorem entire_authored_tree_sound_nonvacuously :
    ∃ (s : State) (w : Wire) (a : Found source s w) (v : Valuation),
      Models s model ∧
      Evidence s model v source.problem.demand a.checked.dictionary ∧
      w.report.result = .selected a.checked.dictionary ∧
      w.report.outputs = source.problem.demand.outputs ∧
      (∀ edge ∈ a.checked.hops,edge.1 = a.root.valueName ∧ edge.2.1 = a.root.valueName) := by
  have yes := independently_parsed_entire_five_node_tree
  unfold test at yes
  cases data : code with
  | none => rw [data] at yes; cases yes
  | some pair =>
    obtain ⟨s,w⟩ := pair
    have checked : (read source s w).isSome = true := by simpa [data] using yes
    cases ran : read source s w with
    | none => rw [ran] at checked; cases checked
    | some a =>
      have m := established_model data
      have sound := root_sound a model m
      obtain ⟨v,tree⟩ := sound.2.2.2
      exact ⟨s,w,a,v,m,tree,sound.2.1,sound.2.2.1,
        GeneralDeclarativeWitnessRetainedCut355.no_distinct_physical_sites_along_spine a.checked⟩

end Yulang.GeneralDeclarativeWitnessSpineFrontModel355
