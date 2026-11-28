import Yulang.GeneralDeclarativeI65I74G05SignedReceipt489
import Yulang.GeneralDeclarativeI65I74TypedConeQuotientSound474
import Yulang.GeneralDeclarativeI65I74G05PreflightCompatibility489

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions oldPosition graphOf readAlternatives interpretedAt)
open LiteralVisits473 (StepWire Checkpoint GuardedObservationInput readCheck)
open Producer479 (Site Trail)
open CommonRoleRegularGraph (successors)
open QuotientObservation471 (ReturnsUpToEquality cone classOf embedded)
open CommonNominalFullCarrier (Equivalent)

private theorem g05_trail_ends_at_the_guarded_last_original_coordinate489
    {n : Nat} {s : GeneralDeclarativeI65.State} {pos : Positions n} {rel : List (Fin n × Fin n)}
    {first last : Site s pos} {moves : List StepWire} {points : List (Fin n)} {bit : Bool}
    (trail : Trail s pos rel first moves points last bit) :
    GuardedObservationInput s pos rel last.index ∧
      (first.index::points).getLast? = some last.index := by
  induction trail with
  | stop guard _ => exact ⟨guard,rfl⟩
  | step _ _ _ _ ih => exact ⟨ih.1,by simpa using ih.2⟩

/-- One checked finite constructor walk serves every model of the
original state. This does not use a new model or a local verdict. -/
def G05CheckedSameFitReturn489 {n : Nat} (p : FullProblem) (pos : Positions n)
    (rel : List (Fin n × Fin n)) (whereAt : Fin n) : Prop :=
  ∃ cp : Checkpoint n, cp.which = whereAt ∧
    readAlternatives p.old.state.core pos rel cp.which cp.scope cp.partition = some true ∧
    ∃ first last : Fin cp.m,
      first ∈ successors (cone cp.scope) cp.scope.site ∧
      FiniteWorklist.Path (successors (cone cp.scope)) first last ∧
      classOf cp.partition last = classOf cp.partition cp.scope.site ∧
      ∀ m : Model, FitsFull p.state m →
        Equivalent (interpretedAt p.old.state.core pos m.assignment (embedded cp.scope last))
          (interpretedAt p.old.state.core pos m.assignment (embedded cp.scope cp.scope.site))

private theorem guarded_original_return_produces_a_finite_same_fit_k2_return489
    {n : Nat} {p : FullProblem} {pos : Positions n} {rel : List (Fin n × Fin n)} {j : Fin n}
    (original : GuardedObservationInput p.old.state.core pos rel j)
    (cycles : ReturnsUpToEquality (graphOf p.old.state.core pos) j) :
    G05CheckedSameFitReturn489 p pos rel j := by
  obtain ⟨cp,atPoint,read⟩ := LiteralVisits473.independent_checkpoint_reifies_the_exact_site_and_sign
    original true (by simp [cycles])
  have checked : readAlternatives p.old.state.core pos rel cp.which cp.scope cp.partition = some true := by
    simpa [readCheck,atPoint] using read
  exact ⟨cp,atPoint,checked,
    ObservationAlternatives473.actual_quotient_k2_gives_a_nonempty_constructor_walk_and_same_type_in_every_fit checked⟩

theorem every_independent_g05_visit_has_prior_authority_for_its_exact_terminal_key489
    {n : Nat} {s : GeneralDeclarativeI65.State} {pos : Positions n}
    {rel : List (Fin n × Fin n)} {argument : Nat} {first : Site s pos}
    {Allowed : CandidateVisitKey485 n → Prop} {key : CandidateVisitKey485 n}
    (actual : IndependentScopedVisit487 rel argument first Allowed key) :
    Allowed key := by
  classical
  obtain ⟨v,_,proper,independent,identity⟩ := actual
  let read : CandidateVisitKey485 n → Bool := fun k => decide (Allowed k)
  have law : ∀ k, read k = true ↔ Allowed k := fun k => by simp [read]
  have passed := (finite_prefix_check_is_iff_the_independent_ordered_permissions487
    law (originalVisitAnchor487 argument first) v.moves v.points).mpr independent
  have terminal := (law _).mp (an_approved_suffix_has_its_exact_terminal_permission487
    read (originalVisitAnchor487 argument first) v.moves v.points proper passed)
  change Allowed (exactGeometryKey486 argument first v) at terminal
  exact identity ▸ terminal

theorem independent_original_k2_has_finite_constructor_return_evidence_in_every_fit489
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {coords : List (Fin n)}
    {Allowed : Nat → CandidateVisitKey485 n → Prop} {i : Nat}
    (cyclic : IndependentScopedReturn487 p gd pos rel coords Allowed i) :
    ∃ ord d, OriginalRosterCell485 p i (ord,d) ∧
      ∃ root argument, (root,argument) ∈ coords.zipIdx ∧
        ∃ head : OriginalArgumentStart486 p gd pos i argument root,
          ∃ key last, IndependentScopedVisit487 rel argument head.site (Allowed ord) key ∧
            key.points.getLast? = some last ∧ G05CheckedSameFitReturn489 p pos rel last := by
  obtain ⟨ord,d,cell,root,arg,atArg,head,key,visited,last,lastAt,cycles⟩ := cyclic
  obtain ⟨v,trail,proper,permitted,exactKey⟩ := visited
  obtain ⟨terminal,terminalIndex⟩ := g05_trail_ends_at_the_guarded_last_original_coordinate489 trail
  have index : v.last.index = last := by
    rw [←exactKey] at lastAt
    change (head.site.index::v.points).getLast? = some last at lastAt
    exact Option.some.inj (terminalIndex.symm.trans lastAt)
  exact ⟨ord,d,cell,root,arg,atArg,head,key,last,⟨v,trail,proper,permitted,exactKey⟩,lastAt,
    guarded_original_return_produces_a_finite_same_fit_k2_return489 (index ▸ terminal) cycles⟩

def G05OriginalK2SlotProof489 {n : Nat} (p : FullProblem)
    (gd : CheckedTable p.old.state.core.current) (pos : Positions n)
    (rel : List (Fin n × Fin n)) (coords : List (Fin n))
    (Allowed : Nat → CandidateVisitKey485 n → Prop) (ord : Nat) : Prop :=
  ∃ (i : Fin (visible485 p).length) (d : GeneralDeclarations.Declaration), OriginalRosterCell485 p i.val (ord,d) ∧
    ∃ root argument, (root,argument) ∈ coords.zipIdx ∧
      ∃ head : OriginalArgumentStart486 p gd pos i.val argument root,
        ∃ key last, IndependentScopedVisit487 rel argument head.site (Allowed ord) key ∧
          Allowed ord key ∧ key.points.getLast? = some last ∧ G05CheckedSameFitReturn489 p pos rel last

private theorem exact_signed_original_g05_hit_crosses_a_finite_same_fit_constructor_return489
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {coords : List (Fin n)}
    {Allowed : Nat → CandidateVisitKey485 n → Prop} {bits : List (Nat × Bool)}
    (ledger : G05ExactSignedRoster489 p (IndependentScopedReturn487 p gd pos rel coords Allowed) bits)
    (ord : Nat) (listed : ord ∈ positiveOrdinals485 bits) :
    G05OriginalK2SlotProof489 p gd pos rel coords Allowed ord := by
  obtain ⟨i,⟨d,cell⟩,cyclic⟩ :=
    (an_original_ordinal_is_positive_exactly_when_its_visible_slot_really_recurs489 ledger ord).mp listed
  obtain ⟨other,e,again,root,arg,atArg,head,key,last,recorded,terminal,allFits⟩ :=
    independent_original_k2_has_finite_constructor_return_evidence_in_every_fit489 cyclic
  have sameOrd : other = ord := congrArg Prod.fst (Option.some.inj
    (((roster_cell_reads_exactly_its_two_original_slots485 _ _ _).mpr again).symm.trans
      ((roster_cell_reads_exactly_its_two_original_slots485 _ _ _).mpr cell)))
  have actual : IndependentScopedVisit487 rel arg head.site (Allowed ord) key := sameOrd ▸ recorded
  exact ⟨i,d,cell,root,arg,atArg,head,key,last,actual,
    every_independent_g05_visit_has_prior_authority_for_its_exact_terminal_key489 actual,terminal,allFits⟩

theorem every_early_g05_hit_has_same_fit_constructor_return_at_its_actual_original_slot489
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {coords : List (Fin n)}
    {permit : Nat → CandidateVisitKey485 n → Bool} {hits : List Nat}
    (scan : readG05Preflight489 p gd pos rel coords permit = some (.recursive hits))
    (Allowed : Nat → CandidateVisitKey485 n → Prop)
    (lawful : ∀ ord key, permit ord key = true ↔ Allowed ord key)
    (ord : Nat) (listed : ord ∈ hits) :
    G05OriginalK2SlotProof489 p gd pos rel coords Allowed ord := by
  obtain ⟨_,bits,ledger,gate⟩ := g05_preflight_has_the_actual_roots_and_independent_ordered_signs489 scan Allowed lawful
  rw [(signed_gate_recursive_iff_it_returns_the_nonempty_exact_positive_subsequence489.mp gate).1] at listed
  exact exact_signed_original_g05_hit_crosses_a_finite_same_fit_constructor_return489 ledger ord listed

theorem every_supplied_signed_g05_hit_has_same_fit_constructor_return_without_local_tokens489
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {coords : List (Fin n)}
    {permit : Nat → CandidateVisitKey485 n → Bool} {receipt : G05SignedReceipt489 n} {hits : List Nat}
    (replayed : readG05SignedReceipt489 p gd pos rel coords permit receipt = some (.recursive hits))
    (Allowed : Nat → CandidateVisitKey485 n → Prop)
    (lawful : ∀ ord key, permit ord key = true ↔ Allowed ord key)
    (ord : Nat) (listed : ord ∈ hits) :
    G05OriginalK2SlotProof489 p gd pos rel coords Allowed ord := by
  obtain ⟨_,bits,ledger,gate⟩ :=
    any_checked_signed_g05_receipt_has_its_full_independent_original_signed_roster489 replayed Allowed lawful
  rw [(signed_gate_recursive_iff_it_returns_the_nonempty_exact_positive_subsequence489.mp gate).1] at listed
  exact exact_signed_original_g05_hit_crosses_a_finite_same_fit_constructor_return489 ledger ord listed

theorem every_replayed_g05_full_report_k2_has_same_fit_constructor_return_independent_of_local_checker489
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {coords : List (Fin n)}
    {permit : Nat → CandidateVisitKey485 n → Bool} {test : G05LocalChecker487}
    {r : G05Report487 n} {w : G05FiniteWitness487 n} {hits : List Nat}
    (Accepted : checkFlatWithDemandScopedG05Tag488 p gd pos rel coords permit test (.inr r) (.inr w) = true)
    (priority : r.priority = .recursive hits)
    (Allowed : Nat → CandidateVisitKey485 n → Prop)
    (scope : G05ExactVisitInputs487 p gd pos rel coords permit Allowed)
    (ord : Nat) (listed : ord ∈ hits) :
    G05OriginalK2SlotProof489 p gd pos rel coords Allowed ord := by
  obtain ⟨rechecked,ordered⟩ :=
    every_accepted_g05_full_report_has_original_signed_projection_without_local_protocol489 Allowed scope Accepted
  have hitList := ((recursive_report_keeps_the_whole_original_ordered_hit_list488 r hits ordered).mp priority).1
  rw [hitList,←positive_signs_of_g05_report_are_its_whole_original_ordered_hit_list489] at listed
  exact exact_signed_original_g05_hit_crosses_a_finite_same_fit_constructor_return489 rechecked ord listed

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
