import Yulang.GeneralDeclarativeI65I74CandidateSignedPath485

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions graphOf)
open WrittenPattern460 (Address)
open WrittenPattern460.PhysicalOrigin (Pose)
open QuotientObservation471 (ReturnsUpToEquality)

structure CandidateVisitKey485 (n : Nat) where
  argument : Nat
  original : List (Address × List Pose)
  points : List (Fin n)
  deriving DecidableEq

def candidateVisitKey485 {n : Nat} (w : CandidatePathWire485 n) : CandidateVisitKey485 n :=
  ⟨w.headArgument,w.trail.tail.map (fun a => (a.1.action,a.1.written)),
    w.trail.cursor.which :: w.trail.tail.map (fun a => a.2.which)⟩

/-- Check every explicitly required candidate-local original action and
old coordinate. A permitted plan is external. A wire does not choose
the plan against which it is checked. -/
def readCandidateFootprint485 {n : Nat} (p : FullProblem)
    (gd : CheckedTable p.old.state.core.current) (pos : Positions n) (rel : List (Fin n × Fin n))
    (visibleIndex : Nat) (permit : CandidateVisitKey485 n → Bool) :
    List (CandidateVisitKey485 n) → List (CandidatePathWire485 n) → Option (List Bool)
  | [],[] => some []
  | a::as,w::ws => do
      if a ≠ candidateVisitKey485 w ∨ !permit a || w.trail.tail.isEmpty then none else
        let read ← readCandidatePath485 p gd pos rel visibleIndex w
        let rest ← readCandidateFootprint485 p gd pos rel visibleIndex permit as ws
        pure (read.terminalBit::rest)
  | _,_ => none

/-- Exact independent local meaning. In particular every packet is a
proper constructor visit, not the requested argument itself. -/
inductive ExactCandidateFootprint485 {n : Nat} (p : FullProblem)
    (gd : CheckedTable p.old.state.core.current) (pos : Positions n) (rel : List (Fin n × Fin n))
    (visibleIndex : Nat) (Authorized : CandidateVisitKey485 n → Prop) :
    List (CandidateVisitKey485 n) → List (CandidatePathWire485 n) → List Bool → Prop where
  | nil : ExactCandidateFootprint485 p gd pos rel visibleIndex Authorized [] [] []
  | cons {w : CandidatePathWire485 n} (read : CandidatePath485 p gd pos rel visibleIndex w) :
      Authorized (candidateVisitKey485 w) → w.trail.tail ≠ [] →
      ExactCandidateFootprint485 p gd pos rel visibleIndex Authorized keys ws rest →
      ExactCandidateFootprint485 p gd pos rel visibleIndex Authorized
        (candidateVisitKey485 w::keys) (w::ws) (read.terminalBit::rest)

/-- Absent, reordered, unapproved, empty or invalid visits are not
silently changed to negative tests. -/
theorem finite_candidate_footprint_reflects_each_exact_permitted_visit485
    {n : Nat} (p : FullProblem) (gd : CheckedTable p.old.state.core.current) (pos : Positions n)
    (rel : List (Fin n × Fin n)) (i : Nat) (permit : CandidateVisitKey485 n → Bool)
    (Authorized : CandidateVisitKey485 n → Prop)
    (authority : ∀ key, permit key = true → Authorized key)
    (keys : List (CandidateVisitKey485 n)) (wires : List (CandidatePathWire485 n)) (out : List Bool)
    (run : readCandidateFootprint485 p gd pos rel i permit keys wires = some out) :
    ExactCandidateFootprint485 p gd pos rel i Authorized keys wires out := by
  induction keys generalizing wires out with
  | nil =>
    cases wires with
    | nil =>
      have empty : [] = out := Option.some.inj run
      cases empty
      exact .nil
    | cons => simp [readCandidateFootprint485] at run
  | cons key keys ih =>
    cases wires with
    | nil => simp [readCandidateFootprint485] at run
    | cons w ws =>
      unfold readCandidateFootprint485 at run
      split at run
      · cases run
      · rename_i notBad
        have same : key = candidateVisitKey485 w := by
          by_cases equal : key = candidateVisitKey485 w
          · exact equal
          · exact False.elim (notBad (Or.inl equal))
        have issued : permit key = true := by
          cases ok : permit key with
          | false => exact False.elim (notBad (.inr (by simp [ok])))
          | true => rfl
        have deep : w.trail.tail ≠ [] := by
          intro empty
          exact notBad (.inr (by simp [empty]))
        subst key
        cases got : readCandidatePath485 p gd pos rel i w with
        | none => simp [got] at run
        | some seen =>
          cases later : readCandidateFootprint485 p gd pos rel i permit keys ws with
          | none => simp [got,later] at run
          | some rest =>
            have ordered : seen.terminalBit::rest = out := Option.some.inj (by simpa [got,later] using run)
            cases ordered
            exact .cons seen (authority _ issued) deep (ih _ _ later)

theorem exact_positive_footprint_bit_has_a_genuine_permitted_terminal485
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current} {pos : Positions n}
    {rel : List (Fin n × Fin n)} {i : Nat} {Auth : CandidateVisitKey485 n → Prop}
    {keys wires bits}
    (checked : ExactCandidateFootprint485 p gd pos rel i Auth keys wires bits)
    {index : Nat} (atBit : bits[index]? = some true) :
    ∃ w : CandidatePathWire485 n, ∃ path : CandidatePath485 p gd pos rel i w,
      wires[index]? = some w ∧ keys[index]? = some (candidateVisitKey485 w) ∧
      Auth (candidateVisitKey485 w) ∧ w.trail.tail ≠ [] ∧
      ReturnsUpToEquality (graphOf p.old.state.core pos) path.last.index := by
  induction checked generalizing index with
  | nil => simp at atBit
  | cons read auth proper tail ih =>
    cases index with
    | zero =>
      have yes : read.terminalBit = true := Option.some.inj atBit
      exact ⟨_,read,rfl,rfl,auth,proper,
        (reported_candidate_positive_owns_the_exact_original_ordinal_and_site485 read yes proper).2.2.1⟩
    | succ k => exact ih atBit

theorem every_independently_permitted_plan_reifies_same_keys_and_signed_results485
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current} {pos : Positions n}
    {rel : List (Fin n × Fin n)} {i : Nat} {Auth : CandidateVisitKey485 n → Prop}
    (permit : CandidateVisitKey485 n → Bool) (recognizes : ∀ key, Auth key → permit key = true)
    {keys wires bits} (independent : ExactCandidateFootprint485 p gd pos rel i Auth keys wires bits) :
    ∃ newWires, newWires.map candidateVisitKey485 = keys ∧
      readCandidateFootprint485 p gd pos rel i permit keys newWires = some bits := by
  induction independent with
  | nil => exact ⟨[],rfl,rfl⟩
  | @cons keys' oldWires restBits w read authorized nonempty later ih =>
    obtain ⟨others,keysMatch,restRan⟩ := ih
    have index : read.head.orig.location.visibleOrdinal = i := congrArg (·.visibleOrdinal) read.exactAddress
    obtain ⟨new,out,ran,ord,head,start,finish,bit,moves,points⟩ :=
      independently_guarded_candidate_path_has_a_finite_wire_at_its_same_roster_slot485
        p gd pos rel i read.authoredOrdinal read.head index read.exactSlot
        read.first read.last _ _ _ read.samePattern read.sameQuery read.atPoint read.visited
    have sameArgument : new.headArgument = w.headArgument := by
      have newArg := congrArg (·.headArgument) out.exactAddress
      have oldArg := congrArg (·.headArgument) read.exactAddress
      exact newArg.symm.trans ((congrArg (fun r : PreparedDeclarations463.PrecheckedHead (p := p.old) gd =>
        r.orig.location.headArgument) head).trans oldArg)
    have sameCursor : new.trail.cursor.which = w.trail.cursor.which :=
      out.originalCursor.trans ((congrArg (·.index) start).trans read.originalCursor.symm)
    have sameLabel : candidateVisitKey485 new = candidateVisitKey485 w := by
      unfold candidateVisitKey485
      have actionEq := congrArg
        (List.map (fun a : LiteralVisits473.StepWire => (a.action,a.written))) moves
      simp only [List.map_map,Function.comp_def] at actionEq
      rw [sameArgument,sameCursor,points,actionEq]
    have valid : new.trail.tail ≠ [] := by
      intro gone
      have impossible : w.trail.tail = [] := by
        rw [gone] at moves
        cases h : w.trail.tail with
        | nil => rfl
        | cons a as => simp [h] at moves
      exact nonempty impossible
    refine ⟨new::others,by simp only [List.map_cons,sameLabel,keysMatch],?_⟩
    have good := recognizes _ authorized
    have nonzero : new.trail.tail.isEmpty = false := by
      cases h : new.trail.tail with
      | nil => exact False.elim (valid h)
      | cons => rfl
    simp [readCandidateFootprint485,sameLabel,good,nonzero,ran,restRan,bit,Option.bind]

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
