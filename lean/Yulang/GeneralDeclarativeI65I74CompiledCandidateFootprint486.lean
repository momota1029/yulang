import Yulang.GeneralDeclarativeI65I74AuthorizedCandidatePlan486
import Yulang.GeneralDeclarativeI65I74CandidateWiresFromGeometry486
import Yulang.GeneralDeclarativeI65I74ExactComputedCandidateReplay486

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable PrecheckedHead)
open ObservationAlternatives473 (Positions oldPosition)
open Producer479 (Site Trail)

def selectAuthorizedGeometries486 {n : Nat} {s : GeneralDeclarativeI65.State} {pos : Positions n}
    (argument : Nat) (first : Site s pos) (permit : CandidateVisitKey485 n → Bool) :
    List (GeometricVisit486 s pos) → List (GeometricVisit486 s pos) :=
  List.filter fun visit => !(visit.moves.isEmpty || !permit (exactGeometryKey486 argument first visit))

def computeCandidatePacket486 {n : Nat} {s : GeneralDeclarativeI65.State} {pos : Positions n}
    (palette : SignedPalette486 n) (argument : Nat) (first : Site s pos) (visit : GeometricVisit486 s pos) :
    Option (CandidatePathWire485 n) :=
  (wireFromGeometry486 palette first visit).map (fun trail => ⟨argument,trail⟩)

/-- Both the planned keys and all checkpoints are generated from the
same original head position. Permission and certified cones remain
separate inputs. -/
def computeCandidateFootprint486 {n : Nat} {s : GeneralDeclarativeI65.State} {pos : Positions n}
    (rel : List (Fin n × Fin n)) (palette : SignedPalette486 n) (argument : Nat) (first : Site s pos)
    (permit : CandidateVisitKey485 n → Bool) :
    Option (List (CandidateVisitKey485 n) × List (CandidatePathWire485 n)) := do
  let selected := selectAuthorizedGeometries486 argument first permit
    (enumerateGuardedGeometry486 rel palette (originalNodeBudget486 first.pattern) first)
  let wires ← selected.mapM (computeCandidatePacket486 palette argument first)
  pure (selected.map (exactGeometryKey486 argument first),wires)

private theorem selected_geometry_projection_has_exactly_the_previously_checked_keys486
    {n : Nat} {s : GeneralDeclarativeI65.State} {pos : Positions n}
    (argument : Nat) (first : Site s pos) (permit : CandidateVisitKey485 n → Bool)
    (traces : List (GeometricVisit486 s pos)) :
    (selectAuthorizedGeometries486 argument first permit traces).map (exactGeometryKey486 argument first) =
      traces.filterMap (fun visit => if visit.moves.isEmpty || !permit (exactGeometryKey486 argument first visit)
        then none else some (exactGeometryKey486 argument first visit)) := by
  induction traces with
  | nil => rfl
  | cons visit tail ih =>
    unfold selectAuthorizedGeometries486 at ih ⊢
    generalize same : (visit.moves.isEmpty || !permit (exactGeometryKey486 argument first visit)) = b
    simp only [List.filter_cons,List.filterMap_cons,same]
    cases b with
    | false => exact congrArg (List.cons (exactGeometryKey486 argument first visit)) ih
    | true => exact ih

private theorem every_checked_geometry_compiles_a_single_exact_candidate_packet486
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {palette : SignedPalette486 n}
    (complete : CompletePalette486 p.old.state.core pos rel palette)
    (i ord : Nat) (head : PrecheckedHead (p := p.old) gd)
    (atIndex : head.orig.location.visibleOrdinal = i)
    (cell : OriginalRosterCell485 p i (ord,head.orig.declaration))
    (first : Site p.old.state.core pos)
    (patternOK : first.pattern = head.orig.original) (queryOK : first.query = head.orig.code)
    (root : oldPosition pos first.index = .logical head.orig.capture.lower)
    (visit : GeometricVisit486 p.old.state.core pos) (actual : Trail p.old.state.core pos rel first
      visit.moves visit.points visit.last visit.bit) (proper : visit.moves ≠ []) :
    ∃ w : CandidatePathWire485 n, ∃ read : CandidatePath485 p gd pos rel i w,
      computeCandidatePacket486 palette head.orig.location.headArgument first visit = some w ∧
      readCandidatePath485 p gd pos rel i w = some read ∧ read.terminalBit = visit.bit ∧
      candidateVisitKey485 w = exactGeometryKey486 head.orig.location.headArgument first visit ∧
      w.trail.tail ≠ [] := by
  have unpack : (⟨visit.moves,visit.points,visit.last,visit.bit⟩ : GeometricVisit486 p.old.state.core pos) = visit := by
    cases visit
    rfl
  obtain ⟨wire,checked,_,_,cursor,moves,points,ran⟩ :=
    direct_geometry_wire_computes_and_checks_the_same_original_signed_trail486 complete actual
  rw [unpack] at checked
  let w : CandidatePathWire485 n := ⟨head.orig.location.headArgument,wire⟩
  obtain ⟨read,replay,_,_,_,_,sign⟩ :=
    the_exact_computed_wire_replays_on_the_same_original_candidate_slot486 p gd pos rel i ord head
      atIndex cell first visit.last visit.bit wire patternOK queryOK root cursor ran
  refine ⟨w,read,by simp [computeCandidatePacket486,checked,w],replay,sign,?_,?_⟩
  · unfold candidateVisitKey485 exactGeometryKey486
    change CandidateVisitKey485.mk _ _ (wire.cursor.which :: _) = _
    have exactMoves := congrArg (List.map (fun step : LiteralVisits473.StepWire => (step.action,step.written))) moves
    simp only [List.map_map,Function.comp_def] at exactMoves
    rw [cursor,exactMoves,points]
  · intro gone
    change wire.tail = [] at gone
    rw [gone] at moves
    exact proper moves.symm

theorem computed_candidate_footprint_replays_all_its_original_authorized_sites486
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {palette : SignedPalette486 n}
    (complete : CompletePalette486 p.old.state.core pos rel palette)
    (i ord : Nat) (head : PrecheckedHead (p := p.old) gd)
    (atIndex : head.orig.location.visibleOrdinal = i)
    (cell : OriginalRosterCell485 p i (ord,head.orig.declaration))
    (first : Site p.old.state.core pos)
    (patternOK : first.pattern = head.orig.original) (queryOK : first.query = head.orig.code)
    (root : oldPosition pos first.index = .logical head.orig.capture.lower)
    (permit : CandidateVisitKey485 n → Bool) (Authorized : CandidateVisitKey485 n → Prop)
    (authority : ∀ k, permit k = true → Authorized k) :
    ∃ keys wires bits,
      computeCandidateFootprint486 rel palette head.orig.location.headArgument first permit = some (keys,wires) ∧
      keys = finiteAuthorizedVisitPlan486 rel palette head.orig.location.headArgument first permit ∧
      ExactCandidateFootprint485 p gd pos rel i Authorized keys wires bits ∧
      readCandidateFootprint485 p gd pos rel i permit keys wires = some bits := by
  let arg := head.orig.location.headArgument
  let all := enumerateGuardedGeometry486 rel palette (originalNodeBudget486 first.pattern) first
  let selected := selectAuthorizedGeometries486 arg first permit all
  have real : ∀ x ∈ selected,
      Trail p.old.state.core pos rel first x.moves x.points x.last x.bit ∧
      x.moves ≠ [] ∧ permit (exactGeometryKey486 arg first x) = true ∧
      Authorized (exactGeometryKey486 arg first x) := by
    intro x member
    obtain ⟨included,accepted⟩ := List.mem_filter.mp member
    have notEmpty : x.moves ≠ [] := by
      intro gone
      simp [gone] at accepted
    have issued : permit (exactGeometryKey486 arg first x) = true := by
      cases h : permit (exactGeometryKey486 arg first x) with
      | false => simp [h] at accepted
      | true => rfl
    exact ⟨every_enumerated_geometry_is_the_original_independent_guarded_trail486 _ _ _ included,
      notEmpty,issued,authority _ issued⟩
  have build (pieces : List (GeometricVisit486 p.old.state.core pos))
      (each : ∀ x ∈ pieces,
        Trail p.old.state.core pos rel first x.moves x.points x.last x.bit ∧
        x.moves ≠ [] ∧ permit (exactGeometryKey486 arg first x) = true ∧
        Authorized (exactGeometryKey486 arg first x)) :
      ∃ ws bits,
        pieces.mapM (computeCandidatePacket486 palette arg first) = some ws ∧
        ExactCandidateFootprint485 p gd pos rel i Authorized
          (pieces.map (exactGeometryKey486 arg first)) ws bits ∧
        readCandidateFootprint485 p gd pos rel i permit (pieces.map (exactGeometryKey486 arg first)) ws =
          some bits := by
    induction pieces with
    | nil => exact ⟨[],[],rfl,.nil,rfl⟩
    | cons x xs ih =>
      obtain ⟨actual,proper,allowed,auth⟩ := each x (List.mem_cons_self ..)
      obtain ⟨w,read,compiled,replay,_,key,deep⟩ :=
        every_checked_geometry_compiles_a_single_exact_candidate_packet486 complete i ord head atIndex cell
          first patternOK queryOK root x actual proper
      obtain ⟨tail,bits,later,independent,accepted⟩ := ih (fun x h => each x (List.mem_cons_of_mem _ h))
      change computeCandidatePacket486 palette arg first x = some w at compiled
      change candidateVisitKey485 w = exactGeometryKey486 arg first x at key
      refine ⟨w::tail,read.terminalBit::bits,by simp [List.mapM_cons,compiled,later,Option.bind],?_,?_⟩
      · simp only [List.map_cons,←key]
        exact .cons read (key ▸ auth) deep independent
      · have nonempty : w.trail.tail.isEmpty = false := by
          cases h : w.trail.tail with
          | nil => exact False.elim (deep h)
          | cons => rfl
        simp [readCandidateFootprint485,key,allowed,nonempty,replay,accepted,Option.bind]
  obtain ⟨wires,bits,built,exact,accepted⟩ := build selected real
  refine ⟨selected.map (exactGeometryKey486 arg first),wires,bits,?_,?_,exact,accepted⟩
  · change (do
      let ws ← selected.mapM (computeCandidatePacket486 palette arg first)
      some (selected.map (exactGeometryKey486 arg first),ws)) = _
    simp [built,Option.bind]
  · exact selected_geometry_projection_has_exactly_the_previously_checked_keys486 arg first permit all

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
