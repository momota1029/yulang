import Yulang.GeneralDeclarativeTaggedFixtureModel340

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeTaggedLegacyCut340
open GeneralDeclarativeTaggedFixture340
open GeneralDeclarativeTaggedFixtureSelection340 (waiting current ranked initial_grows classification)
open GeneralDeclarativeTaggedFixtureModel340 (actual_dictionary)
open GeneralDeclarativeHiddenDecl324 (interpretation)
open GeneralDeclarativeInlineEndpoint331 (candidates)
open GeneralDeclarativeLowerKnown321 (Ready ready_iff_not_delayed)
open GeneralDeclarativeObserverGrowth330 (backed_same)
open GeneralDeclarativePriority321 (Local)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarations (Declaration)
open GeneralDeclarativeExactOverlay337 (ModelsExact)
open GeneralDeclarativeExactDictionary337 (Evidence)
open CommonRoleOutermostResolver (Classify)

theorem current_old_not_ready : ¬Ready current d := by
  intro raw
  obtain ⟨tag,row,backed,_,tells⟩ := raw a List.mem_cons_self
  have earlier := (backed_same p initial_grows row).mp backed
  have written := p.ordinary ((GeneralDeclarativeOrigins321.backed_iff p row).mp earlier).choose_spec.1
  change row ∈ [⟨0,outer⟩,⟨2,outer⟩] at written
  rcases List.mem_cons.mp written with rfl|other
  · cases tells
  · cases List.mem_singleton.mp other
    cases tells

theorem old_pending (emit : Demand → Declaration → List Demand → Prop) :
    Local endState registry interpretation current (candidates current registry interpretation waiting) emit d .pending := by
  have delayed := Classical.byContradiction fun no => current_old_not_ready
    ((ready_iff_not_delayed current d).mpr no)
  exact .unsupported delayed (GeneralDeclarativeTaggedElection340.safe ranked)

/-- Different verdict at the same inhabited final source state.
The legacy observer has not implemented the agreed same-tag grouping
at its readiness check; no actual Rust or raw operational result is
claimed here. The new positive path uses the original output compiler. -/
theorem exact_difference (emit : Demand → Declaration → List Demand → Prop) :
    Local endState registry interpretation current (candidates current registry interpretation waiting) emit d .pending ∧
    Classify (GeneralDeclarativeTaggedDictionary340.Rule current [] registry interpretation waiting)
      d (.selected (.node 97 [])) ∧
    ∃ m, ModelsExact endState [] m ∧ Evidence registry interpretation m d (.node 97 []) := by
  obtain ⟨m,fit,accepted,_,_⟩ := actual_dictionary
  exact ⟨old_pending emit,classification,m,fit,accepted⟩

end Yulang.GeneralDeclarativeTaggedLegacyCut340
