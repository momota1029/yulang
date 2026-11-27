import Yulang.GeneralDeclarativeI65I74CanonicalCertificateErasure461

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.EligibleFieldStart461
open WrittenPattern460
open RecordTraversal455 (RawSnapshot termInspects)
open RecordTraversal455.MixedQA (MixedPath)
open AuthenticatedHop458 (Policy)
open InlineStructuralPolicy458 (policy emptyPolicy)
open RetainedFull445 (FullProblem)
open SplitEscape446 (splitCheck446)

def addUnitPlacement {p : Policy} :
    AuthenticatedHop458.Wire p → JointWire p inheritedCompilerPlacement
  | .stop => .stop ()
  | .down hop safe rest => .down () hop safe (addUnitPlacement rest)

theorem erase_added_placement_is_same_raw_certificate {p : Policy} (w : AuthenticatedHop458.Wire p) :
    rawPlacement (addUnitPlacement w) = w := by
  induction w with
  | stop => rfl
  | down hop safe rest ih => simp [addUnitPlacement,rawPlacement,ih]

theorem added_placement_reconstructs_entire_unit_wire {p : Policy}
    (w : JointWire p inheritedCompilerPlacement) :
    addUnitPlacement (rawPlacement w) = w := by
  induction w with
  | stop loc => cases loc; rfl
  | down loc hop safe rest ih => cases loc; simp [addUnitPlacement,rawPlacement,ih]

theorem erase_lift_preserves_old_ticket_data (s : CoreState)
    (w : AuthenticatedHop458.Wire emptyPolicy) :
    InlineStructuralPolicy458.erase s (InlineStructuralPolicy458.lift s w) = w := by
  induction w with
  | stop => rfl
  | down hop safe rest ih =>
    cases hop
    simp [InlineStructuralPolicy458.erase,InlineStructuralPolicy458.lift,ih]

def fromPriorCertificate (p : FullProblem) (w : HomogeneousClosedEntry459.FieldWire) :
    EligibleWire (exactHeaderReader (alreadyHomogeneous p.old)) :=
  let route := InlineStructuralPolicy458.liftCycle p.old.state.core w.cursor
  ⟨w.emptyKey,⟨addUnitPlacement route.trail,route.cycle⟩⟩

theorem same_earlier_header_key_and_entire_raw_wire_roundtrip (p : FullProblem)
    (w : HomogeneousClosedEntry459.FieldWire) :
    toPriorCertificate p (fromPriorCertificate p w) = w := by
  rcases w with ⟨key,⟨trail,cycle⟩⟩
  simp [toPriorCertificate,fromPriorCertificate,InlineStructuralPolicy458.liftCycle,
    InlineStructuralPolicy458.eraseCycle,erase_added_placement_is_same_raw_certificate,
    erase_lift_preserves_old_ticket_data]

theorem same_eligible_ticket_and_entire_unit_wire_roundtrip (p : FullProblem)
    (w : EligibleWire (exactHeaderReader (alreadyHomogeneous p.old))) :
    fromPriorCertificate p (toPriorCertificate p w) = w := by
  rcases w with ⟨key,⟨trail,cycle⟩⟩
  simp [toPriorCertificate,fromPriorCertificate,InlineStructuralPolicy458.liftCycle,
    InlineStructuralPolicy458.eraseCycle,InlineStructuralPolicy458.lift_erase458,
    added_placement_reconstructs_entire_unit_wire]

/-- This reads syntax only *along an actual route already read separately*.
Its input vertices are not evidence for a raw graph, which always comes
from the unchanged authenticated raw reader with the same real wire. -/
def readCoordinates (keys : Nat → KeyRead) (root : Nat) (t : Term) : MixedPath → Option Term
  | [] => some t
  | (a,n)::rest => do
    readCoordinates keys n (← WrittenPattern460.readStep (keys root) t (writtenAddress a)) rest

def lastCoordinate (root : Nat) : MixedPath → Nat
  | [] => root
  | (_,n)::rest => lastCoordinate n rest

theorem selected_coordinates_iff_independent_walk {keys : Nat → KeyRead}
    {root t path terminal last}
    (terminalExact : lastCoordinate root path = terminal) :
    readCoordinates keys root t path = some last ↔ CoordinateWalk keys root t path terminal last := by
  induction path generalizing root t terminal with
  | nil =>
    have equal : root = terminal := terminalExact
    subst terminal
    constructor
    · intro h
      have e : t = last := Option.some.inj h
      subst last
      exact .stop
    · intro yes
      cases yes
      rfl
  | cons step tail ih =>
    obtain ⟨a,n⟩ := step
    have endAt : lastCoordinate n tail = terminal := terminalExact
    constructor
    · intro h
      change ((WrittenPattern460.readStep (keys root) t (writtenAddress a)).bind
        fun u => readCoordinates keys n u tail) = some last at h
      obtain ⟨u,found,walk⟩ := Option.bind_eq_some_iff.mp h
      exact .down (read_step_sound found) ((ih endAt).mp walk)
    · intro h
      cases h with
      | down wrote rest =>
        have child := (ih endAt).mpr rest
        simp [readCoordinates,read_step_complete wrote,Option.bind,child]

private theorem neutralPlacement (site : Nat) (t : Term) (q : GeneralNominalCenteredHeadMatExpressions.Expr) :
    inheritedCompilerPlacement.checks site t q () = true := rfl

/-- On every input, the interleaved reader is exactly the same raw run
followed by the selected written positions. The old raw reader and its
failure/used outputs are not modified. -/
theorem interleaved_read_factors_through_the_identical_raw_run
    (s : RawSnapshot) (pol : Policy) (keys : Nat → KeyRead)
    (root : Nat) (t : Term) (q : GeneralNominalCenteredHeadMatExpressions.Expr)
    (w : AuthenticatedHop458.Wire pol) :
    readJoint s pol keys inheritedCompilerPlacement root t q (addUnitPlacement w) =
      (do
        let (path,n,used) ← AuthenticatedHop458.readTrail s pol root q w
        let last ← readCoordinates keys root t path
        pure (path,n,last,used)) := by
  induction w generalizing root t q with
  | stop =>
    by_cases inspect : termInspects q = true <;>
      simp [addUnitPlacement,readJoint,neutralPlacement,
        AuthenticatedHop458.readTrail,inspect,readCoordinates,Option.bind]
  | down hop cut tail ih =>
    cases select : AuthenticatedHop458.readStep s pol root q hop with
    | none =>
      by_cases safe : splitCheck446 s root cut = true <;>
        simp [addUnitPlacement,readJoint,neutralPlacement,AuthenticatedHop458.readTrail,
          select,safe,Option.bind]
    | some next =>
      obtain ⟨step,c,child,used⟩ := next
      by_cases safe : splitCheck446 s root cut = true
      · cases inner : AuthenticatedHop458.readTrail s pol c child tail with
        | none =>
          cases code : WrittenPattern460.readStep (keys root) t (writtenAddress step) <;>
            simp [addUnitPlacement,readJoint,neutralPlacement,AuthenticatedHop458.readTrail,
              select,safe,inner,code,ih,Option.bind]
        | some out =>
          obtain ⟨as,n,stamp⟩ := out
          cases code : WrittenPattern460.readStep (keys root) t (writtenAddress step) with
          | none =>
            simp [addUnitPlacement,readJoint,neutralPlacement,AuthenticatedHop458.readTrail,
              select,safe,inner,code,readCoordinates,Option.bind]
          | some x =>
            cases choose : readCoordinates keys c x as <;>
              simp [addUnitPlacement,readJoint,neutralPlacement,AuthenticatedHop458.readTrail,
                select,safe,inner,code,ih,readCoordinates,choose,Option.bind]
      · simp [addUnitPlacement,readJoint,neutralPlacement,AuthenticatedHop458.readTrail,
          select,safe,Option.bind]

end Yulang.GeneralDeclarativeI65.I72.EligibleFieldStart461
