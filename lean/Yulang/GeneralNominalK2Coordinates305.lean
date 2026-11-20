import Yulang.GeneralNominalK2CoordinateEdges305
import Yulang.GeneralNominalVersionedCandidateCoordinates305

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalK2Coordinates305
open GeneralNominalRecursiveCandidates (Context arguments report)
open GeneralNominalReportContext305 (EquivalentContexts arguments_exact report_exact)
open GeneralNominalReportSourceTransport (moveBounds moveReport)
open GeneralNominalK2CoordinateEdges305 (recurs_forward)
open GeneralNominalInverseCoordinates305 (reverse)
open GeneralNominalCandidateReplayModels305 (linked_iff pending_iff)
open GeneralNominalVersionedCandidateCoordinates305 (prepared_iff)
open GeneralNominalCycleK2 (RootK2)
open GeneralNominalVersionedCycles232 (RawCandidateK2)
open GeneralSourceDictionaries (Occurrence)
open GeneralSourceState (Demand)
open GeneralDeclarations (Registry)
variable {old next : Context}

theorem root_forward (eq : EquivalentContexts old next) (demand : Demand roles)
    (found : RootK2 old.state demand) : RootK2 next.state demand := by
  obtain ⟨linked,known,index,slot,source,recurs⟩ := found
  exact ⟨GeneralNominalRefinements.linked eq.forward demand linked,
    fun newer => known (GeneralNominalRefinements.pending_backwards eq.forward demand newer),
    index,eq.geometry.slot slot,(eq.geometry.source_eq slot).trans source,recurs_forward eq recurs⟩

theorem root_iff (eq : EquivalentContexts old next) (demand : Demand roles) :
    RootK2 old.state demand ↔ RootK2 next.state demand :=
  ⟨root_forward eq demand,root_forward (reverse eq) demand⟩

theorem candidate_forward (eq : EquivalentContexts old next) (r : Registry) (root : Occurrence roles)
    (oldBad : RawCandidateK2 r old root) : RawCandidateK2 r next root := by
  obtain ⟨known,d,vis,check,role,ok,bounds,loc,visited,listed,bad⟩ := oldBad
  refine ⟨(not_congr (pending_iff eq root)).mp known,d,vis,check,role,(prepared_iff eq r root d).mp ok,
    bounds.map (moveBounds eq.geometry.slot),?_,moveBounds eq.geometry.slot visited,?_,recurs_forward eq bad⟩
  · rw [arguments_exact eq,loc]; rfl
  · rw [report_exact eq]
    exact List.mem_map.mpr ⟨visited,listed,rfl⟩

theorem candidate_iff (eq : EquivalentContexts old next) (r : Registry) (root : Occurrence roles) :
    RawCandidateK2 r old root ↔ RawCandidateK2 r next root :=
  ⟨candidate_forward eq r root,candidate_forward (reverse eq) r root⟩

end Yulang.GeneralNominalK2Coordinates305
