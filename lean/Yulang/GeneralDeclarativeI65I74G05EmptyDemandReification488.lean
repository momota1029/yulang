import Yulang.GeneralDeclarativeI65I74G05EmptyDemand488

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions)
open TypedRootSafety482 (requestRootCheck)
open GeneralDeclarations (Declaration)

def readNoArgumentG05Report488 {n : Nat} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n))
    (permit : Nat → CandidateVisitKey485 n → Bool) (test : G05LocalChecker487)
    (wire : G05FiniteWitness487 n) : Option (G05Report487 n) :=
  if wire.roots.isEmpty && requestRootCheck p pos rel wire.roots then do
    let rows ← compileNoArgumentRoster488 p
    let signed ← readTape485 p
      (readPlannedLocal485 p gd pos rel (rows.map ComputedOriginalCandidate486.keys)
        (permitAtOriginalVisibleSlot486 p permit)) wire.tape
    let report ← readG05OrderedRows487 p test 0 rows signed wire.localTokens
    pure ⟨report,G05PriorityOfRows487 report⟩
  else none

theorem every_independent_zero_argument_report_reifies_without_an_arity_assumption488
    {n : Nat} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n))
    (permit : Nat → CandidateVisitKey485 n → Bool) (test : G05LocalChecker487)
    (Allowed : Nat → CandidateVisitKey485 n → Prop) (meaning : G05LocalMeaning487)
    (scope : G05ExactVisitInputs487 p gd pos rel [] permit Allowed)
    (protocol : G05ExactLocalProtocol487 test meaning) (r : G05Report487 n)
    (report : G05ExactCandidateReport487 p gd pos rel [] Allowed meaning r) :
    ∃ wire : G05FiniteWitness487 n, wire.roots = [] ∧
      readNoArgumentG05Report488 p gd pos rel permit test wire = some r := by
  obtain ⟨computed,compiled,length,replay,each⟩ :=
    zero_demand_arg_roster_generates_exactly_one_empty_wire_per_visible_slot488 p gd pos rel permit
  let signed := computed.map fun x => (x.authoredOrdinal,false)
  have cLen := length.trans report.2.1.symm
  have sLen : signed.length = r.rows.length := by simpa [signed] using cLen
  have every : ∀ (j : Nat) (candidate : ComputedOriginalCandidate486 n) (bit : Nat × Bool)
      (row : G05CandidateRow487 n), computed[j]? = some candidate → signed[j]? = some bit →
      r.rows[j]? = some row → ∃ token, readG05OneRow487 p test (0+j) candidate bit token = some row := by
    intro j candidate bit row present atBit atRow
    have b := (List.getElem?_eq_some_iff.mp atRow).1
    let i : Fin (visible485 p).length := ⟨j,report.2.1 ▸ b⟩
    obtain ⟨d0,ord,source,actual⟩ := each i
    have canonical : candidate = ⟨ord,[],⟨j,[]⟩⟩ := Option.some.inj (present.symm.trans actual)
    subst candidate
    have filled : signed[j]? = some (ord,false) := by
      simp [signed,List.getElem?_map,present]
    have eq := Option.some.inj (atBit.symm.trans filled)
    subst bit
    obtain ⟨there,d,stored,real,visits,decision⟩ := report.2.2 i
    have hrow := Option.some.inj (stored.symm.trans atRow)
    subst there
    have primary := (roster_cell_reads_exactly_its_two_original_slots485 _ _ _).mpr real
    have secondary := (roster_cell_reads_exactly_its_two_original_slots485 _ _ _).mpr source
    have ordinal : row.ordinal = ord := congrArg Prod.fst (Option.some.inj (primary.symm.trans secondary))
    have emptyKeys := (the_exact_observation_list_is_empty_without_original_argument_coordinates488
      p gd pos rel (Allowed row.ordinal) i.val row.observed).mp visits
    cases flag : row.mark with
    | requiredCycle =>
      rw [flag] at decision
      exact False.elim (no_scoped_original_return_when_there_are_no_demanded_coordinates488 p gd pos rel Allowed i.val decision)
    | nonrecursive v =>
      rw [flag] at decision
      obtain ⟨data,permitCheck⟩ := protocol.2 i.val row.ordinal d v decision.2
      have read : rosterCell485 p j = some (row.ordinal,d) := primary
      have exactRow : (⟨row.ordinal,[],.nonrecursive v⟩ : G05CandidateRow487 n) = row := by
        cases row
        simp_all
      have verdict : test j row.ordinal d data = some v := permitCheck
      refine ⟨some data,?_⟩
      rw [Nat.zero_add,readG05OneRow487]
      simp only [read,bind,Option.bind]
      have seats : (decide (row.ordinal = ord) && decide (row.ordinal = ord) && decide True) = true := by
        simp [ordinal]
      rw [ite_eq_left seats]
      change (do
        let status ← readG05LocalMark487 test j row.ordinal d false (some data)
        pure (⟨row.ordinal,[],status⟩ : G05CandidateRow487 n)) = _
      have got : readG05LocalMark487 test j row.ordinal d false (some data) = some (.nonrecursive v) :=
        (a_local_nonrecursive_mark_requires_a_real_local_receipt_not_failed_read487).mpr
        ⟨rfl,data,rfl,verdict⟩
      rw [got]
      exact congrArg some exactRow
  obtain ⟨tokens,assembled⟩ := exact_locally_available_marks_reify_one_finite_ordered_local_receipt_list487
    p test 0 computed signed r.rows cLen sLen every
  let wire : G05FiniteWitness487 n := ⟨[],computed.map fun x => (x.authoredOrdinal,x.packet),tokens⟩
  have noRoot := empty_safe_coordinate_list_has_no_hidden_requested_lower488 scope.2.2.1
  have realRoot : requestRootCheck p pos rel wire.roots = true := by
    simp [requestRootCheck,wire,noRoot,TypedRootSafety482.noRootReturnBool]
  have exactReport : (⟨r.rows,G05PriorityOfRows487 r.rows⟩ : G05Report487 n) = r := by
    cases r
    simp_all [G05ExactCandidateReport487]
  refine ⟨wire,rfl,?_⟩
  have guard : (wire.roots.isEmpty && requestRootCheck p pos rel wire.roots) = true := by
    simp [realRoot,wire]
  rw [readNoArgumentG05Report488,ite_eq_left guard]
  simp [wire,compiled,replay,assembled,Option.bind,signed,exactReport]

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
