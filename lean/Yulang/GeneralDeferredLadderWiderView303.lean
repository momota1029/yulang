import Yulang.GeneralCanonicalObservations
import Yulang.GeneralNominalRefinements

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeferredLadderWiderView303
open GeneralNormalizedObservation (Snapshot Head Shape)
open GeneralNominalState (State Known)

def widenedHead {shapes : Fin kinds → Shape} (none : kinds = 0)
    (head : Head shapes slots) : Head (fun _ : Fin 1 => .exactEmpty) slots :=
  match head with
  | .deferred reason => .deferred reason
  | .scalar name => .scalar name
  | .structural kind _ => Fin.elim0 (none ▸ kind)

theorem widened_term {shapes : Fin kinds → Shape} (none : kinds = 0) (head : Head shapes slots) :
    (widenedHead none head).term = head.term := by
  cases head with
  | deferred => rfl
  | scalar => rfl
  | structural k _ => exact Fin.elim0 (none ▸ k)

theorem widened_node {shapes : Fin kinds → Shape} (none : kinds = 0) (head : Head shapes slots) :
    (widenedHead none head).node = head.node := by
  cases head with
  | deferred => rfl
  | scalar => rfl
  | structural k _ => exact Fin.elim0 (none ▸ k)

def widenedView (view : Snapshot base) (none : view.kinds = 0) : Snapshot base where
  kinds := 1
  shapes := fun _ => .exactEmpty
  shapes_injective := fun i j _ => Subsingleton.elim i j
  canonical := fun _ => trivial
  heads := fun slot => widenedHead none (view.heads slot)
  checked := by
    intro slot term found
    exact view.checked slot term ((widened_term none _).symm.trans found)

def wider (s : State) (none : s.view.kinds = 0) : State where
  base := s.base
  view := widenedView s.view none
  constructors := s.constructors
  nominals := s.nominals
  catalogue := s.catalogue
  bodies_opaque := by
    intro slot desc record
    change widenedHead none (s.view.heads slot) = _
    rw [s.bodies_opaque slot desc record]
    rfl
  seed := s.seed
  allocated := s.allocated
  reserved := s.reserved
  ordinary := s.ordinary

theorem same_graph (s : State) (none : s.view.kinds = 0) (slot : Fin s.base.slots) :
    (wider s none).view.graph slot = s.view.graph slot :=
  widened_node none (s.view.heads slot)

theorem known_iff (s : State) (none : s.view.kinds = 0) (source : Nat) :
    Known (wider s none) source ↔ Known s source := by
  constructor
  · rintro ⟨slot,id,seen⟩
    refine ⟨slot,id,?_⟩
    rw [same_graph s none slot] at seen
    exact seen
  · rintro ⟨slot,id,seen⟩
    refine ⟨slot,id,?_⟩
    rw [same_graph s none slot]
    exact seen

theorem recorded (s : State) (none : s.view.kinds = 0) (obs)
    (seen : GeneralCanonicalObservations.Recorded (wider s none) obs) :
    GeneralCanonicalObservations.Recorded s obs := by
  cases seen with
  | scalar slot scalar same =>
    change widenedHead none (s.view.heads slot) = _ at same
    cases h : s.view.heads slot with
    | deferred => rw [h] at same; cases same
    | scalar name =>
      rw [h] at same
      cases same
      exact GeneralCanonicalObservations.Recorded.scalar (snapshot := s) slot _ h
    | structural k _ => exact Fin.elim0 (none ▸ k)
  | structural slot kind kids same =>
    change widenedHead none (s.view.heads slot) = _ at same
    cases h : s.view.heads slot with
    | deferred => rw [h] at same; cases same
    | scalar => rw [h] at same; cases same
    | structural k _ => exact Fin.elim0 (none ▸ k)
  | nominal slot desc found => exact GeneralCanonicalObservations.Recorded.nominal (snapshot := s) slot desc found

/-- A catalogue entry can be added without introducing any structural
observation. This is not an assertion that normalized heads were arbitrary. -/
def widen_refines {old new : State} (r : GeneralNominalRefinements.Refines old new)
    (none : new.view.kinds = 0) : GeneralNominalRefinements.Refines old (wider new none) :=
  ⟨r.base,r.heads,r.nominals,r.ordinary,fun source known => (known_iff new none source).mpr (r.known source known),
    r.reserved,r.allocated,r.seed,r.constructors⟩

end Yulang.GeneralDeferredLadderWiderView303
