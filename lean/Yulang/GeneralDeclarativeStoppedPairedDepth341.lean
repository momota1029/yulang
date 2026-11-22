import Yulang.GeneralDeclarativeStoppedPaired341
import Yulang.GeneralDeclarativeStoppedReports341

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 33000
set_option maxHeartbeats 15600000
namespace Yulang.GeneralDeclarativeStoppedPairedDepth341
open GeneralDictionaryOutputDepth252 (sourceRegistry roles root interpretation plan)
open GeneralRebaseDepthScalar285 (refreshed)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary Local local_functional)
open GeneralRebaseDepthHaltSelection285 (selected)
open GeneralRebaseDepthCommit285 (center_sites finalPlan)
open GeneralDeclarativeStoppedRetarget340 (exact_requests exact_packet row)
open GeneralDeclarativeStoppedDepthView341 (requested waiting raw_demand exact_rhs outRow)
open GeneralDeclarativeStoppedDepthWitness341 (compiled current witness)
open GeneralDeclarativeStoppedPaired341 (Bridge Placement activeDemand)
open GeneralDeclarativeTaggedDictionary340 (Rule)
open GeneralDeclarativeLowerKnown321 (alias_refl)
open GeneralSourceDictionaries (Occurrence)
open GeneralDeclarativeDemand320 (Demand)
open CommonRoleOutermostResolver (Resolves Summarizes)

inductive Rel : Occurrence roles → Demand → Prop where
  | rootH : Rel root requested

theorem actual_placement (h : Rel a d) : Placement refreshed compiled a d := by
  cases h with
  | rootH =>
    refine ⟨plan.input,center_sites.symm ▸ List.mem_cons_self,rfl,?_⟩
    have form : activeDemand refreshed plan.input = requested := by
      unfold activeDemand
      rw [show plan.input.occurrence = root from rfl,exact_requests]
      rfl
    rw [form]
    exact ⟨rfl,.cons ⟨alias_refl _,alias_refl _,alias_refl _⟩ .nil,rfl⟩

theorem paired (done : Nat → Prop) :
    Bridge (boundary roles) sourceRegistry refreshed root compiled Rel
      (Rule (current done) [] sourceRegistry interpretation waiting) := by
  refine ⟨fun _ _ => actual_placement,?_ ,?_⟩
  · exact GeneralDeclarativeStoppedDiagnostic341.from_packets GeneralDeclarativeStoppedDepth341.terminal
  · intro raw logical pair _ key kids classified
    cases pair with
    | rootH =>
      have same := local_functional classified selected
      cases same
      exact ⟨[],.whole (witness done),.nil⟩

theorem exact_diagnostic_and_targets (done : Nat → Prop) :
    Resolves (Rule (current done) [] sourceRegistry interpretation waiting) requested (.selected 0 []) ∧
    requested.outputs = GeneralNominalCenteredHeadOutputs.requests refreshed.core root ∧
    GeneralDeclarativeStoppedOrder339.compileRequests finalPlan requested.outputs = some [outRow] := by
  obtain ⟨raw,_,summary⟩ := GeneralDeclarativeStoppedReports341.Depth.report done
  obtain ⟨targets,interpreted,_⟩ := GeneralDeclarativeStoppedPaired341.exact (paired done) Rel.rootH raw summary
  exact ⟨interpreted,targets,by rw [targets,← exact_rhs]; exact exact_packet⟩

end Yulang.GeneralDeclarativeStoppedPairedDepth341
