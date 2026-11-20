import Yulang.GeneralNominalInverseCoordinates305
import Yulang.GeneralNominalCycleK2

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalK2CoordinateEdges305
open GeneralNominalState (State)
open GeneralNominalReportCoordinates305 (HeadData observed Coordinates)
open GeneralNominalRecursiveCandidates (Context)
open GeneralNominalReportContext305 (EquivalentContexts model_iff same_embedding)
open GeneralNominalCycleK2 (DirectArgument DirectEdge DirectPath DirectCycle RecursAt)
open GeneralNominalMixedRecurrence (ActualArgument Edge Path Cycle)
open CommonRoleRegularGraph (successors)
variable {old next : Context}

def childSlots : HeadData α → List α
  | .structural _ slots => slots
  | _ => []

theorem child_slots (s : State) (i : Fin s.base.slots) :
    childSlots (observed s i) = successors s.view.graph i := by
  unfold observed successors GeneralNormalizedObservation.Snapshot.graph
  cases s.view.heads i <;> rfl

theorem moved_slots (h : HeadData α) (f : α → β) :
    childSlots (h.move f) = (childSlots h).map f := by
  cases h <;> rfl

theorem structural_forward (rel : Coordinates a b) (path : GeneralSourceK2.Child a.view i j) :
    GeneralSourceK2.Child b.view (rel.slot i) (rel.slot j) := by
  have old := (GeneralSourceK2.child_graph_iff a.view i j).mp path
  apply (GeneralSourceK2.child_graph_iff b.view ..).mpr
  rw [← child_slots,rel.normalized,moved_slots,child_slots]
  exact List.mem_map.mpr ⟨j,old,rfl⟩

theorem descriptor_moved (iso : EquivalentContexts old next)
    (listed : old.state.nominals i = some d) :
    next.state.nominals (iso.geometry.slot i) =
      some (GeneralNominalRefinements.renameDescriptor iso.geometry.slot d) := by
  rw [same_embedding iso]
  exact iso.forward.nominals i d listed

theorem direct_argument_forward (iso : EquivalentContexts old next) (arg : DirectArgument old.state i j) :
    DirectArgument next.state (iso.geometry.slot i) (iso.geometry.slot j) := by
  obtain ⟨d,listed,index,atIndex⟩ := arg
  refine ⟨_,descriptor_moved iso listed,index,?_⟩
  simp [GeneralNominalRefinements.renameDescriptor,List.getElem?_map,atIndex,
    GeneralNominalRefinements.renameParameter]

theorem actual_argument_forward (iso : EquivalentContexts old next) (arg : ActualArgument old.state i j) :
    ActualArgument next.state (iso.geometry.slot i) (iso.geometry.slot j) := by
  obtain ⟨d,listed,index,held⟩ := arg
  refine ⟨_,descriptor_moved iso listed,index,?_⟩
  intro m nextModel
  have origin := held m ((model_iff iso m).mpr nextModel)
  simpa [iso.geometry.source_eq,GeneralNominalRefinements.renameDescriptor] using origin

theorem direct_edge_forward (iso : EquivalentContexts old next) (edge : DirectEdge old.state i j) :
    DirectEdge next.state (iso.geometry.slot i) (iso.geometry.slot j) :=
  edge.elim (Or.inl ∘ structural_forward iso.geometry) (Or.inr ∘ direct_argument_forward iso)

theorem mixed_edge_forward (iso : EquivalentContexts old next) (edge : Edge old.state i j) :
    Edge next.state (iso.geometry.slot i) (iso.geometry.slot j) :=
  edge.elim (Or.inl ∘ structural_forward iso.geometry) (Or.inr ∘ actual_argument_forward iso)

theorem direct_path_forward (iso : EquivalentContexts old next) (path : DirectPath old.state i j) :
    DirectPath next.state (iso.geometry.slot i) (iso.geometry.slot j) := by
  induction path with
  | nil => exact .nil _
  | cons first _ ih => exact .cons (direct_edge_forward iso first) ih

theorem mixed_path_forward (iso : EquivalentContexts old next) (path : Path old.state i j) :
    Path next.state (iso.geometry.slot i) (iso.geometry.slot j) := by
  induction path with
  | nil => exact .nil _
  | cons first _ ih => exact .cons (mixed_edge_forward iso first) ih

theorem recurs_forward (iso : EquivalentContexts old next) (recurs : RecursAt old.state i) :
    RecursAt next.state (iso.geometry.slot i) := by
  rcases recurs with ⟨child,edge,path⟩ | ⟨⟨child,edge,path⟩,m,holds⟩
  · exact Or.inl ⟨_,direct_edge_forward iso edge,direct_path_forward iso path⟩
  · exact Or.inr ⟨⟨_,mixed_edge_forward iso edge,mixed_path_forward iso path⟩,m,(model_iff iso m).mp holds⟩

theorem recurs_iff (iso : EquivalentContexts old next) (i : Fin old.state.base.slots) :
    RecursAt old.state i ↔ RecursAt next.state (iso.geometry.slot i) := by
  refine ⟨recurs_forward iso,?_⟩
  intro new
  have back := recurs_forward (GeneralNominalInverseCoordinates305.reverse iso) new
  change RecursAt old.state (iso.backward.base.embed (iso.geometry.slot i)) at back
  rwa [GeneralNominalInverseCoordinates305.left_inverse iso] at back

end Yulang.GeneralNominalK2CoordinateEdges305
