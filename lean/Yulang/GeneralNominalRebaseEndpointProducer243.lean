import Yulang.GeneralNominalRebaseSourceSteps243
import Yulang.GeneralNominalRebaseAggregateFinite242
namespace Yulang.GeneralNominalRebaseEndpointProducer243
open GeneralNominalRebaseSourceSteps243
open GeneralNominalRebaseStablePool243 (pool)
open GeneralNominalRebaseAggregateFinite242
open GeneralNominalAllocation (occurrences lower upper)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

theorem uniform_total (supported : bounds ⊆ pairPool) :
 ∃ pair ∈ expressionPairs pairPool, ∀ model : Assignment,
 Equivalent (pair.1.eval CommonNominalFullCarrier.model model) ((lower bounds).eval CommonNominalFullCarrier.model model) ∧
 Equivalent (pair.2.eval CommonNominalFullCarrier.model model) ((upper bounds).eval CommonNominalFullCarrier.model model) := by
 by_cases empty : bounds = []
 · subst bounds
   have member : ([] : List GeneralSourceState.Interval) ∈ subsets pairPool := by
     have found := canonical_enumerated pairPool []
     have nil : canonical pairPool [] = [] := by
       induction pairPool with
       | nil => rfl
       | cons head tail ih => simp_all [canonical]
     rw [nil] at found
     exact found
   refine ⟨(lower [],upper []),List.mem_map.mpr ⟨[],member,rfl⟩,?_⟩
   intro model
   exact ⟨⟨subtype_refl _,subtype_refl _⟩,⟨subtype_refl _,subtype_refl _⟩⟩
 · exact uniform_representative supported empty

theorem report_endpoints
 (path : B4Target.Steps (Step registry initial root budget) initial.state state)
 (report : GeneralNominalRecursiveInspection.Report state) :
 GeneralNominalAllocationSupport.Endpoints (GeneralNominalRecursiveInspection.bindings state report)
   (pool registry initial root budget) := by
 intro entry member
 have bounded := GeneralNominalAllocationSupport.report_endpoints state report entry member
 exact ⟨trace_supported path bounded.1,trace_supported path bounded.2⟩

theorem report_occurrences
 (path : B4Target.Steps (Step registry initial root budget) initial.state state)
 (report : GeneralNominalRecursiveInspection.Report state) (name : Nat) :
 occurrences (GeneralNominalRecursiveInspection.bindings state report) name ⊆ endpointPairs (pool registry initial root budget) := by
 intro pair member
 exact endpointPairs_mem.mpr (GeneralNominalAllocationSupport.occurrences_endpoints (report_endpoints path report) name pair member)

theorem aggregate_uniform
 (path : B4Target.Steps (Step registry initial root budget) initial.state state)
 (report : GeneralNominalRecursiveInspection.Report state) (name : Nat) :
 ∃ pair ∈ expressionPairs (endpointPairs (pool registry initial root budget)), ∀ model : Assignment,
 Equivalent (pair.1.eval CommonNominalFullCarrier.model model)
   ((lower (occurrences (GeneralNominalRecursiveInspection.bindings state report) name)).eval CommonNominalFullCarrier.model model) ∧
 Equivalent (pair.2.eval CommonNominalFullCarrier.model model)
   ((upper (occurrences (GeneralNominalRecursiveInspection.bindings state report) name)).eval CommonNominalFullCarrier.model model) :=
 uniform_total (report_occurrences path report name)

theorem representative_count (registry initial root budget) :
 (expressionPairs (endpointPairs (pool registry initial root budget))).length =
 2 ^ ((pool registry initial root budget).length * (pool registry initial root budget).length) := by
 rw [expressionPairs_length,endpointPairs_length]
end Yulang.GeneralNominalRebaseEndpointProducer243
