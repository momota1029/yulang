import Yulang.GeneralDeclarativeStoppedPaired341
import Yulang.GeneralDeclarativeStoppedDisplay341

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32000
set_option maxHeartbeats 15600000
namespace Yulang.GeneralDeclarativeStoppedPairedDisplay341
open GeneralNominalExamples (registry interpretation registry_checked displayRoot displayChild state intDisplay)
open GeneralDeclarationExamples (roles display)
open GeneralRebaseDisplayFrame276 (after generated no_new_request)
open GeneralRebaseDisplaySelection276 (picked_parent picked_child)
open GeneralRebaseDisplayEndpoint276 (generates_only)
open GeneralRebaseDisplayExecutor276 (run raw run_exact)
open GeneralNominalVersionedMixedBoundary234 (boundary Local)
open GeneralNominalCenters (rootSite)
open GeneralNominalNonleafPlan193 (centerSite)
open GeneralStoppedDisplayProjection335 (parentDemand childDemand)
open GeneralStoppedDisplayCut335 (reminted)
open GeneralStoppedDisplayExtended335 (expanded augmented placement)
open GeneralStoppedDisplayGuard335 (waiting)
open GeneralDeclarativeTaggedDictionary340 (Rule)
open GeneralDeclarativeStoppedPaired341 (Bridge Placement activeDemand exact)
open GeneralNominalSaturationState (Generated)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeLowerKnown321 (alias_refl)
open GeneralSourceDictionaries (Occurrence)
open CommonRoleOutermostResolver (Resolves Summarizes)

inductive Rel : Occurrence roles → Demand → Prop where
  | root : Rel displayRoot parentDemand
  | leaf : Rel displayChild reminted

theorem actual_placement (h : Rel a d) : Placement after expanded a d := by
  cases h with
  | root =>
    refine ⟨rootSite (state true).seed displayRoot,?_,rfl,?_⟩
    · rw [GeneralRebaseDisplayEvidence276.center_sites]
      exact List.mem_cons_self
    · have form : activeDemand after (rootSite (state true).seed displayRoot) = parentDemand := by
        unfold activeDemand
        rw [show (rootSite (state true).seed displayRoot).occurrence = displayRoot from rfl,no_new_request]
        rfl
      rw [form]
      exact ⟨rfl,.cons ⟨alias_refl _,alias_refl _,alias_refl _⟩ .nil,rfl⟩
  | leaf =>
    refine ⟨centerSite,?_,rfl,?_⟩
    · rw [GeneralRebaseDisplayEvidence276.center_sites]
      exact List.mem_cons_of_mem _ List.mem_cons_self
    · have form : activeDemand after centerSite = childDemand := by
        unfold activeDemand
        rw [show centerSite.occurrence = displayChild from rfl,no_new_request]
        rfl
      rw [form]
      exact placement

theorem actual_children {a} (arrived : Generated after.core.erased.current displayRoot a)
    (raw : Local registry after a (.selected key kids)) :
    ∀ child ∈ kids, Generated after.core.erased.current displayRoot child := by
  intro child seen
  rcases generates_only arrived with rfl|rfl
  · have same := B4TargetV8.local_functional raw picked_parent
    cases same
    cases List.mem_singleton.mp seen
    exact generated
  · have same := B4TargetV8.local_functional raw picked_child
    cases same
    cases seen

theorem paired (done : Nat → Prop) :
    Bridge (boundary roles) registry after displayRoot expanded Rel
      (Rule (augmented done) [] registry interpretation waiting) := by
  refine ⟨fun _ _ => actual_placement,fun _ arrived _ _ picked => actual_children arrived picked,?_⟩
  intro raw logical h _ key kids classified
  cases h with
  | root =>
    have same := B4TargetV8.local_functional classified picked_parent
    cases same
    exact ⟨[reminted],.whole (GeneralDeclarativeStoppedDisplayModern341.parent done),.cons .leaf .nil⟩
  | leaf =>
    have same := B4TargetV8.local_functional classified picked_child
    cases same
    exact ⟨[],.whole (GeneralDeclarativeStoppedDisplayModern341.child done),.nil⟩

/-- The actual two-node solved example retains its exact successful
diagnostic, even though the ordinary child has two freshly minted
endpoints. Exact ordered targets come from physical registered sites. -/
theorem exact_diagnostic (done : Nat → Prop) (finished : run key = some (phase,payload)) :
    Resolves (Local registry (raw phase)) displayRoot (.selected 1 [.selected 3 []]) ∧
    Resolves (Rule (augmented done) [] registry interpretation waiting) parentDemand (.selected 1 [.selected 3 []]) ∧
    Summarizes (.selected 1 [.selected 3 []]) (.selected payload) ∧
    parentDemand.outputs = GeneralNominalCenteredHeadOutputs.requests (raw phase).core displayRoot := by
  obtain ⟨_,rfl,rfl⟩ := (run_exact key phase payload).mp finished
  have resolved : Resolves (Local registry after) displayRoot (.selected 1 [.selected 3 []]) :=
    .selected picked_parent (.cons (.selected picked_child .nil) .nil)
  have summary : Summarizes (.selected 1 [.selected 3 []]) (.selected (.node 1 [.node 3 []])) :=
    .selected (.cons (.selected .nil (.selected rfl)) .nil) (.selected rfl)
  obtain ⟨targets,translated,_⟩ := GeneralDeclarativeStoppedPaired341.exact (paired done) Rel.root resolved summary
  exact ⟨resolved,translated,summary,targets⟩

end Yulang.GeneralDeclarativeStoppedPairedDisplay341
