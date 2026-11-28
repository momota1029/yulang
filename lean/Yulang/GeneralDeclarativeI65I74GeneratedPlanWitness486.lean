import Yulang.GeneralDeclarativeI65I74CoveredCandidateReification485
import Yulang.GeneralDeclarativeI65I74AuthorizedCandidatePlan486

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable PrecheckedHead)
open ObservationAlternatives473 (Positions oldPosition)
open Producer479 (Site)
open GeneralDeclarations (Declaration)

theorem a_generated_exact_proper_visit_has_an_authorized_candidate_packet486
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)}
    (i ord : Nat) (head : PrecheckedHead (p := p.old) gd)
    (atIndex : head.orig.location.visibleOrdinal = i)
    (cell : OriginalRosterCell485 p i (ord,head.orig.declaration))
    (first : Site p.old.state.core pos)
    (startPattern : first.pattern = head.orig.original) (sameQuery : first.query = head.orig.code)
    (root : oldPosition pos first.index = .logical head.orig.capture.lower)
    (Approved : CandidateVisitKey485 n → Prop) (key : CandidateVisitKey485 n)
    (authorized : IndependentAuthorizedVisit486 rel head.orig.location.headArgument first Approved key) :
    ∃ (w : CandidatePathWire485 n) (r : CandidatePath485 p gd pos rel i w),
      candidateVisitKey485 w = key ∧ w.trail.tail ≠ [] ∧
      Approved (candidateVisitKey485 w) ∧ readCandidatePath485 p gd pos rel i w = some r := by
  obtain ⟨visit,actual,proper,sameKey,auth⟩ := authorized
  obtain ⟨wire,read,checked,pinnedOrdinal,pinnedHead,pinnedStart,pinnedEnd,pinnedSign,moves,points⟩ :=
    independently_guarded_candidate_path_has_a_finite_wire_at_its_same_roster_slot485
      p gd pos rel i ord head atIndex cell first visit.last visit.moves visit.points visit.bit startPattern sameQuery root actual
  have arg : wire.headArgument = head.orig.location.headArgument := by
    have loc := congrArg (·.headArgument) read.exactAddress
    rw [pinnedHead] at loc
    exact loc.symm
  have start : wire.trail.cursor.which = first.index :=
    read.originalCursor.trans (congrArg (·.index) pinnedStart)
  have keyIs : candidateVisitKey485 wire = key := by
    rw [←sameKey]
    unfold candidateVisitKey485 exactGeometryKey486
    have sameMoves := congrArg
      (List.map (fun a : LiteralVisits473.StepWire => (a.action,a.written))) moves
    simp only [List.map_map,Function.comp_def] at sameMoves
    rw [arg,start,sameMoves,points]
  refine ⟨wire,read,keyIs,?_,keyIs ▸ auth,checked⟩
  intro empty
  rw [empty] at moves
  exact proper moves.symm

theorem the_generated_plan_has_independent_original_data_for_every_candidate_visit486
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} (palette : SignedPalette486 n)
    (complete : CompletePalette486 p.old.state.core pos rel palette)
    (i ord : Nat) (head : PrecheckedHead (p := p.old) gd)
    (atIndex : head.orig.location.visibleOrdinal = i)
    (cell : OriginalRosterCell485 p i (ord,head.orig.declaration))
    (first : Site p.old.state.core pos)
    (startPattern : first.pattern = head.orig.original) (sameQuery : first.query = head.orig.code)
    (root : oldPosition pos first.index = .logical head.orig.capture.lower)
    (Approved : CandidateVisitKey485 n → Prop) (permit : CandidateVisitKey485 n → Bool)
    (matchesPrior : ∀ k, permit k = true ↔ Approved k) :
    ∃ wires bits, ExactCandidateFootprint485 p gd pos rel i Approved
      (finiteAuthorizedVisitPlan486 rel palette head.orig.location.headArgument first permit) wires bits := by
  let plan := finiteAuthorizedVisitPlan486 rel palette head.orig.location.headArgument first permit
  have each : ∀ key ∈ plan, ∃ (w : CandidatePathWire485 n) (r : CandidatePath485 p gd pos rel i w),
      candidateVisitKey485 w = key ∧ w.trail.tail ≠ [] ∧ Approved (candidateVisitKey485 w) := by
    intro key inPlan
    have good := (generated_plan_keys_are_exactly_the_authorized_existing_proper_visits486
      palette complete head.orig.location.headArgument first permit Approved matchesPrior key).mp inPlan
    obtain ⟨wire,read,exact,proper,auth,_⟩ := a_generated_exact_proper_visit_has_an_authorized_candidate_packet486
      i ord head atIndex cell first startPattern sameQuery root Approved key good
    exact ⟨wire,read,exact,proper,auth⟩
  have make (keys : List (CandidateVisitKey485 n))
      (every : ∀ key ∈ keys, ∃ (w : CandidatePathWire485 n) (r : CandidatePath485 p gd pos rel i w),
        candidateVisitKey485 w = key ∧ w.trail.tail ≠ [] ∧ Approved (candidateVisitKey485 w)) :
      ∃ wires bits, ExactCandidateFootprint485 p gd pos rel i Approved keys wires bits := by
    induction keys with
    | nil => exact ⟨[],[],.nil⟩
    | cons key keys ih =>
      obtain ⟨wire,read,rfl,proper,auth⟩ := every key (List.mem_cons_self ..)
      obtain ⟨wires,bits,tail⟩ := ih (fun k yes => every k (List.mem_cons_of_mem _ yes))
      exact ⟨wire::wires,read.terminalBit::bits,.cons read auth proper tail⟩
  exact make plan each

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
