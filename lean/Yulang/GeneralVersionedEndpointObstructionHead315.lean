import Yulang.GeneralVersionedEndpointCuts315
import Yulang.GeneralDictionaryCompoundFeasible238
import Yulang.GeneralMixedCompoundUpperOutcome307
import Yulang.GeneralDeferredLadderTransport302

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
set_option maxRecDepth 20000
/-! The known compound reobservation obstruction has an actually feasible
current head. This establishes the exact non-replay cut counterexample,
not a failure of recursive evidence with selected children. -/
namespace Yulang.GeneralVersionedEndpointObstructionHead315
open GeneralDictionaryJournalRefinement228Source (roles root snapshot interpretation)
open GeneralDictionaryCompoundSource238 (registry sourceRegistry declaration declaration_checked checked source)
open GeneralDictionaryCompoundSites238 (childSite root_center root_raw)
open GeneralDictionaryCompoundPoint238 (point allocated reserved ordinary)
open GeneralDictionaryCompoundRefresh239 (refreshed models_iff)
open GeneralMixedCompoundUpperRefresh307 (upperState)
open GeneralMixedCompoundUpperSnapshot307 (snap context desc)
open GeneralMixedCompoundUpperRoot307 (plan packet located bindings_exact report_exact)
open GeneralMixedCompoundUpperHalt307 (centers raw_sites stable)
open GeneralMixedCompoundUpperChild307 (reachable)
open GeneralDictionaryCompoundPointModel238 (extended)
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatPlanData (Same)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedPlans231 (HeadModels SchemaHolds)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedCandidates231 (inputs Prepared Survivor Unique)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedDiagnostic232 (HeadEquations)

noncomputable abbrev beforePlan := GeneralDictionaryCompoundObstruction238.currentPlan

theorem read_eq : Same beforePlan plan := by
  refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,?_⟩
  change GeneralNominalReportErasure.erase _ (GeneralNominalRecursiveCandidates.report _ declaration [(0,0)]) =
    GeneralNominalReportErasure.erase _ (GeneralNominalRecursiveCandidates.report _ declaration [(0,0)])
  rw [GeneralDictionaryCompoundCurrent238.report_exact,report_exact]
  rfl

theorem valid : Models upperState extended :=
  (GeneralMixedCompoundUpperRefresh307.models_iff _).mpr
    ((models_iff _).mpr GeneralDictionaryCompoundPointModel238.model)

theorem head : HeadModels plan.packet extended := by
  have old := GeneralDictionaryCompoundPrepared238.head_model
  exact ⟨(GeneralNominalVersionedPlans231.private_models_iff _ _).mpr ⟨valid.1.1,
    (GeneralDeferredLadderTransport302.ordinary_iff read_eq _).mp
      ((GeneralNominalVersionedPlans231.private_models_iff _ _).mp old.1).2⟩,
    (GeneralNominalCenteredHeadMatPlanData.projections read_eq _).mp old.2⟩

theorem schema : SchemaHolds plan plan.headSchema extended := by
  have old := GeneralDictionaryCompoundFeasible238.head_equations.2.2
  rw [GeneralNominalCenteredHeadMatPlanData.head_schema read_eq] at old
  unfold SchemaHolds at old ⊢
  simp only [GeneralDeferredLadderTransport302.binder_eq read_eq,
    GeneralDeferredLadderTransport302.capture_eq read_eq] at old
  exact old

theorem fresh : GeneralNominalVersionedAllocation231.Fresh snap registry root.identity packet.bindings := by
  rw [bindings_exact]
  intro key member collision
  change key ∈ [GeneralNominalAggregateVersion231.key root.identity declaration.id 0 0 [(0,2,2),(0,2,2)],
    GeneralNominalAggregateVersion231.key root.identity declaration.id 1 0 [(0,2,2),(0,2,2)],
    GeneralNominalAggregateVersion231.key root.identity declaration.id 0 0 [(0,2,2),(0,2,2)],
    GeneralNominalAggregateVersion231.key root.identity declaration.id 1 0 [(0,2,2),(0,2,2)],
    GeneralNominalAllocation.origin root.identity declaration.id 6 0 0,
    GeneralNominalAllocation.origin root.identity declaration.id 3 0 0,
    GeneralNominalAllocation.origin root.identity declaration.id 4 0 0] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact False.elim ((by decide +kernel : GeneralDictionaryCompoundPointModel238.nextName 0 ∉ GeneralNominalState.sources snap) collision)
    | exact False.elim ((by decide +kernel : GeneralDictionaryCompoundPointModel238.nextName 1 ∉ GeneralNominalState.sources snap) collision)
    | decide +kernel

theorem prepared : Prepared registry context root declaration := by
  refine ⟨source.metadata,⟨?_,by intro output member; cases member⟩,[(0,0)],located,fresh,?_,extended,head⟩
  · intro index
    constructor <;> exact GeneralNominalAllocationSupport.slot_source snap (0 : Fin 8)
  · rw [report_exact]
    exact ⟨rfl,rfl,rfl⟩

theorem frame : Frame registry upperState.core root declaration.id plan := by
  refine ⟨rfl,rfl,rfl,rfl,?_,?_,List.mem_singleton_self _,rfl,located,prepared⟩
  · rw [raw_sites]; exact List.mem_cons_self ..
  · rw [centers]; exact List.mem_cons_self ..

theorem head_eq : HeadEquations plan extended := by
  refine ⟨valid.1.2.2.2.1 plan.input frame.center_recorded,?_,schema⟩
  intro name named
  exact GeneralNominalVersionedCurrentHead237.capture_fits plan frame valid head schema name (.inl named)

theorem known : ¬ GeneralNominalState.RootPending snap (inputs root).demand := by
  rintro ⟨i,h⟩
  have zero : i = 0 := Fin.ext (by exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (show i.val < 1 from i.isLt)))
  subst i
  exact h ⟨0,rfl,Or.inr ⟨_,rfl⟩⟩

theorem unique : Unique registry context root declaration.id (GeneralNominalVersionedFrame231.children packet) := by
  have chosen : Survivor registry context root declaration.id (GeneralNominalVersionedFrame231.children packet) :=
    ⟨known,declaration,List.mem_singleton_self _,declaration_checked,rfl,rfl,[(0,0)],located,prepared,rfl⟩
  refine ⟨chosen,?_⟩
  intro key kids other
  have copy := other
  obtain ⟨_,d,visible,_,eq,_⟩ := copy
  cases List.mem_singleton.mp visible
  subst key
  exact ⟨rfl,GeneralNominalVersionedCandidates231.survivor_children_functional checked other chosen⟩

end Yulang.GeneralVersionedEndpointObstructionHead315
