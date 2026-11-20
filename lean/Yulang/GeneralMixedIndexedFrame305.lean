import Yulang.GeneralNominalK2Coordinates305
import Yulang.GeneralDeferredLadderOperationalView304

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralMixedIndexedFrame305
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalCenters (Plan)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalReportContext305 (EquivalentContexts movePlan same_plan arguments_exact)
open GeneralNominalCenteredHeadMatPlanData (Same)
open GeneralDeferredLadderOperationalView304 (View)
open GeneralNominalVersionedCandidateCoordinates305 (prepared_iff)
open GeneralNominalReportSourceTransport (moveBounds moveReport)
open GeneralNominalInspection (queries)
variable {roles : Roles.RoleDecls} {a b : State roles}

structure IndexedView (a b : State roles) where
  raw : View a b
  centers : a.core.sites = b.core.sites
  ctx : EquivalentContexts a.core.erased.current.context b.core.erased.current.context

def reverse (view : IndexedView a b) : IndexedView b a :=
  ⟨view.raw.symm,view.centers.symm,GeneralNominalInverseCoordinates305.reverse view.ctx⟩

def coordinates (view : IndexedView a b) {p : Plan roles} (frame : Frame r a.core root key p) :
    EquivalentContexts p.packet.context b.core.erased.current.context :=
  frame.context_eq.symm ▸ view.ctx

def relocate (view : IndexedView a b) {p : Plan roles} (frame : Frame r a.core root key p) :
    Plan roles :=
  movePlan p (coordinates view frame)

theorem relocated_same (view : IndexedView a b) {p : Plan roles} (frame : Frame r a.core root key p) :
    Same p (relocate view frame) := same_plan p (coordinates view frame)

theorem relocated_frame (view : IndexedView a b) {p : Plan roles} (f : Frame r a.core root key p) :
    Frame r b.core root key (relocate view f) := by
  refine ⟨f.registry_eq,rfl,f.occurrence_eq,f.key_eq,view.raw.sites ▸ f.raw_recorded,
    view.centers ▸ f.center_recorded,f.visible,f.role_eq,?_,?_⟩
  · have eq := arguments_exact (coordinates view f) (GeneralNominalVersionedCandidates231.inputs root)
    rw [f.located] at eq
    exact eq
  · exact (prepared_iff view.ctx r root p.packet.declaration).mp f.prepared

theorem inspection_move {p : Plan roles} (eq : EquivalentContexts p.packet.context next) :
    GeneralNominalCenteredSteps.inspection (movePlan p eq) =
      moveReport eq.geometry.slot (GeneralNominalCenteredSteps.inspection p) := by
  have q : queries next.state next.interpretation p.packet.declaration =
      queries p.packet.context.state p.packet.context.interpretation p.packet.declaration := by
    unfold queries
    rw [eq.forward.constructors,← eq.interpretation]
  unfold GeneralNominalCenteredSteps.inspection
  change GeneralNominalRecursiveInspection.inspectMany next.state
    (queries next.state next.interpretation p.packet.declaration)
    (p.packet.bounds.map (moveBounds eq.geometry.slot)) _ 0 = _
  rw [q,GeneralNominalReportRecompute305.many_exact eq.geometry]
  rfl

theorem inspected_tests {p : Plan roles} (eq : EquivalentContexts p.packet.context next) :
    (GeneralNominalCenteredSteps.inspection (movePlan p eq)).tests =
      (GeneralNominalCenteredSteps.inspection p).tests := by
  rw [inspection_move eq]
  rfl

theorem inspected_sizes {p : Plan roles} (eq : EquivalentContexts p.packet.context next) :
    (GeneralNominalCenteredSteps.inspection (movePlan p eq)).inspected.length =
      (GeneralNominalCenteredSteps.inspection p).inspected.length := by
  rw [inspection_move eq]
  exact List.length_map ..

end Yulang.GeneralMixedIndexedFrame305
