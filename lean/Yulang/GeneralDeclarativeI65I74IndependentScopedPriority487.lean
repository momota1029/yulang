import Yulang.GeneralDeclarativeI65I74IndependentScopedRosterCoverage487

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions graphOf)
open QuotientObservation471 (ReturnsUpToEquality)
open LiteralVisits473 (Checkpoint)

def IndependentScopedReturn487 {n : Nat} (p : FullProblem)
    (gd : CheckedTable p.old.state.core.current) (pos : Positions n)
    (rel : List (Fin n × Fin n)) (roots : List (Fin n))
    (Allowed : Nat → CandidateVisitKey485 n → Prop) (i : Nat) : Prop :=
  ∃ ord d, OriginalRosterCell485 p i (ord,d) ∧
    ∃ root argument, (root,argument) ∈ roots.zipIdx ∧
      ∃ head : OriginalArgumentStart486 p gd pos i argument root,
        ∃ key, IndependentScopedVisit487 rel argument head.site (Allowed ord) key ∧
          ∃ j, key.points.getLast? = some j ∧ ReturnsUpToEquality (graphOf p.old.state.core pos) j

theorem compiled_scoped_tape_covers_its_independent_original_recursion_predicate487
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {palette : SignedPalette486 n}
    {roots : List (Fin n)} {permit : Nat → CandidateVisitKey485 n → Bool}
    {rows : List (ComputedOriginalCandidate486 n)}
    (ran : compileScopedRoster487 p gd pos rel palette roots permit = some rows)
    (Allowed : Nat → CandidateVisitKey485 n → Prop)
    (lawful : ∀ ord key, permit ord key = true ↔ Allowed ord key) :
    IndependentCoverage485 p pos (rows.map ComputedOriginalCandidate486.keys)
      (IndependentScopedReturn487 p gd pos rel roots Allowed) := by
  intro i keys atRow
  obtain ⟨row,d,stored,scope,_,each⟩ :=
    successful_scoped_roster_reads_every_actual_visible_slot_and_its_exact_independent_visits487
      ran i Allowed lawful
  have same : row.keys = keys := Option.some.inj (by simpa [List.getElem?_map,stored] using atRow)
  subst keys
  constructor
  · rintro ⟨ord,rowDecl,exactRoot,root,arg,belongs,head,key,reach,j,atEnd,recurs⟩
    have left := (roster_cell_reads_exactly_its_two_original_slots485 _ _ _).mpr exactRoot
    have right := (roster_cell_reads_exactly_its_two_original_slots485 _ _ _).mpr scope
    have eq : ord = row.authoredOrdinal := congrArg Prod.fst (Option.some.inj (left.symm.trans right))
    subst ord
    exact ⟨key,(each key).mpr ⟨root,arg,belongs,head,reach⟩,j,atEnd,recurs⟩
  · rintro ⟨key,used,j,ending,recursive⟩
    obtain ⟨root,arg,exactWhere,head,reached⟩ := (each key).mp used
    exact ⟨row.authoredOrdinal,d,scope,root,arg,exactWhere,head,key,reached,j,ending,recursive⟩

def IndependentlyAuthorizedAtVisibleSlot487 {n : Nat} (p : FullProblem)
    (Allowed : Nat → CandidateVisitKey485 n → Prop) (i : Nat) (key : CandidateVisitKey485 n) : Prop :=
  ∃ ord d, OriginalRosterCell485 p i (ord,d) ∧ Allowed ord key

theorem permit_at_original_slot_only_uses_authority_from_its_actual_original_ordinal487
    {n : Nat} {p : FullProblem} {permit : Nat → CandidateVisitKey485 n → Bool}
    {Allowed : Nat → CandidateVisitKey485 n → Prop}
    (sound : ∀ ord key, permit ord key = true → Allowed ord key)
    (i : Nat) (key : CandidateVisitKey485 n)
    (ok : permitAtOriginalVisibleSlot486 p permit i key = true) :
    IndependentlyAuthorizedAtVisibleSlot487 p Allowed i key := by
  unfold permitAtOriginalVisibleSlot486 at ok
  cases entry : rosterCell485 p i with
  | none => simp [entry] at ok
  | some pair =>
    obtain ⟨ord,d⟩ := pair
    exact ⟨ord,d,(roster_cell_reads_exactly_its_two_original_slots485 _ _ _).mp entry,
      sound ord key (by simpa [entry] using ok)⟩

theorem scoped_pre_election_bits_are_exactly_the_independent_prefix_authorized_old_returns487
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {palette : SignedPalette486 n}
    {roots : List (Checkpoint n)} {permit : Nat → CandidateVisitKey485 n → Bool}
    {out : PreElection485}
    (ran : readScopedPreElection487 p gd pos rel palette roots permit = some out)
    (Allowed : Nat → CandidateVisitKey485 n → Prop)
    (lawful : ∀ ord key, permit ord key = true ↔ Allowed ord key) :
    ∃ bits, gate485 bits = out ∧
      ∀ i : Fin (visible485 p).length, ∃ ord d bit,
        OriginalRosterCell485 p i.val (ord,d) ∧ bits[i.val]? = some (ord,bit) ∧
          (bit = true ↔ IndependentScopedReturn487 p gd pos rel (roots.map Checkpoint.which) Allowed i) := by
  obtain ⟨_,rows,compiled,replayed⟩ :=
    scoped_election_checks_unchanged_safe_original_roots_and_full_packet_tape487 ran
  apply verified_whole_planned_tape_marks_exactly_the_independently_covered_recursions485
    (IndependentlyAuthorizedAtVisibleSlot487 p Allowed) _
    (IndependentScopedReturn487 p gd pos rel (roots.map Checkpoint.which) Allowed) _ replayed
  · exact permit_at_original_slot_only_uses_authority_from_its_actual_original_ordinal487
      (fun ord key => (lawful ord key).mp)
  · exact compiled_scoped_tape_covers_its_independent_original_recursion_predicate487 compiled Allowed lawful

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
