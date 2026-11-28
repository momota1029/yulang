import Yulang.GeneralDeclarativeI65I74PairedInteriorSequence483
import Yulang.GeneralDeclarativeI65I74AuthoredInterior483

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
open RetainedFull445 (FullProblem)
open Producer479 (Site Hop Trail TrailWire readTrail)
open LiteralVisits473 (StepWire Checkpoint readCheck)
open ObservationAlternatives473 (Positions oldPosition graphOf)
open GeneralDeclarativeWitnessOrigins350 (Table Attached)
open GeneralDeclarativeRepeatedActual323 (eqAt)
open GeneralDeclarativeTermWalk322 (Walk)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeOrigins321 (Supported)
open InputCoordinates475 (rawAt)
open QuotientObservation471 (ReturnsUpToEquality)

inductive InteriorMeaning {p : FullProblem} {pos : Positions n} (table : Table) :
    Site p.old.state.core pos → Site p.old.state.core pos → ReadCard → List (InteriorMove n) →
    List (Site p.old.state.core pos × Site p.old.state.core pos) → Prop where
  | nil : InteriorMeaning table left right card [] []
  | cons (read : PairedFocusedHop (p := p) table left right move.step card move.author move.ambient) :
      (∃ rebuilt : Expr,
        (∀ m : Model, FitsFull p.state m → eqAt m.assignment read.author.after.term rebuilt) ∧
        Walk .actual rebuilt read.author.after.query read.author.uses) →
      InteriorMeaning table read.author.after read.ambient read.author.childCard tail rest →
      InteriorMeaning table left right card (move :: tail) ((read.author.after,read.ambient) :: rest)

theorem paired_path_retains_the_independent_source_typing_at_each_read_origin
    {p : FullProblem} {pos : Positions n} {table : Table}
    {left right : Site p.old.state.core pos} {card : ReadCard} {moves path}
    {done : Nat → Prop} {support : Supported (rawAt p) done}
    (attached : Attached (rawAt p) table)
    (authored : ∀ row ∈ table.authored, support.derivesFrom row .source)
    (chain : InteriorSequence (p := p) table left right card moves path) :
    InteriorMeaning (p := p) table left right card moves path := by
  induction chain with
  | nil => exact .nil
  | cons read _ _ _ ih =>
    exact .cons read (scoped_selected_arrival_uses_same_original_fits_and_compiled_child attached authored read.author) ih

def readPairedIndices {n : Nat} (path : List (Fin n × Checkpoint n × StepWire)) : List (InteriorMove n) :=
  path.map (fun x => ⟨x.2.2,x.1,x.2.1.which⟩)

structure SignedInteriorWire (n : Nat) where
  first : Checkpoint n
  moves : List (Fin n × Checkpoint n × StepWire)

def SignedInteriorWire.ambient (w : SignedInteriorWire n) : TrailWire n :=
  ⟨w.first,w.moves.map (fun x => (x.2.2,x.2.1))⟩

structure SignedInteriorPath {p : FullProblem} {pos : Positions n} (table : Table)
    (left right : Site p.old.state.core pos) (card : ReadCard) (rel : List (Fin n × Fin n))
    (w : SignedInteriorWire n) where
  sites : InteriorSequenceRead (p := p) table left right card (readPairedIndices w.moves)
  terminal : Site p.old.state.core pos
  bit : Bool
  exactAmbient : readTrail rel right w.ambient = some (terminal,bit)

def readSignedInteriorPath {p : FullProblem} {pos : Positions n} (table : Table)
    (left right : Site p.old.state.core pos) (card : ReadCard) (rel : List (Fin n × Fin n))
    (w : SignedInteriorWire n) : Option (SignedInteriorPath (p := p) table left right card rel w) := do
  let sites ← readInteriorSequence (p := p) table left right card (readPairedIndices w.moves)
  let signed ← collectedForInterior (readTrail rel right w.ambient)
  some ⟨sites,signed.val.1,signed.val.2,signed.property⟩

theorem signed_interior_is_at_the_exact_ambient_path_with_source_side_unchanged
    {p : FullProblem} {pos : Positions n} {table : Table}
    {left right : Site p.old.state.core pos} {card : ReadCard} {rel : List (Fin n × Fin n)}
    {w : SignedInteriorWire n} {done : Nat → Prop} {support : Supported (rawAt p) done}
    (attached : Attached (rawAt p) table)
    (authored : ∀ row ∈ table.authored, support.derivesFrom row .source)
    (out : SignedInteriorPath (p := p) table left right card rel w) :
    w.first.which = right.index ∧
    Trail p.old.state.core pos rel right (w.ambient.tail.map Prod.fst)
      (w.ambient.tail.map (fun e => e.2.which)) out.terminal out.bit ∧
    out.sites.path.map (fun e => (e.1.index,e.2.index)) =
      (readPairedIndices w.moves).map (fun e => (e.author,e.ambient)) ∧
    InteriorMeaning (p := p) table left right card (readPairedIndices w.moves) out.sites.path := by
  have ambient := Producer479.finite_trail_wire_reflects_exact_selected_path479 out.exactAmbient
  exact ⟨ambient.1,ambient.2,
    (every_visited_paired_edge_stays_at_the_literal_coordinates_and_authored_pose out.sites.actual).1,
    paired_path_retains_the_independent_source_typing_at_each_read_origin attached authored out.sites.actual⟩

end Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
