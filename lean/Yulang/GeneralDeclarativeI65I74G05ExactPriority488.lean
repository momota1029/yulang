import Yulang.GeneralDeclarativeI65I74G05CoordinateDispatch488

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions)

def reportedOriginalG05Cycles488 {n : Nat} (rows : List (G05CandidateRow487 n)) : List Nat :=
  rows.filterMap fun row => match row.mark with
    | .requiredCycle => some row.ordinal
    | .nonrecursive _ => none

theorem original_g05_cycle_ordinals_are_exactly_the_cyclic_rows488
    {n : Nat} (rows : List (G05CandidateRow487 n)) (ord : Nat) :
    ord ∈ reportedOriginalG05Cycles488 rows ↔
      ∃ row ∈ rows, row.ordinal = ord ∧ row.mark = .requiredCycle := by
  unfold reportedOriginalG05Cycles488
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨row,found,reported⟩
    cases state : row.mark with
    | requiredCycle => exact ⟨row,found,by simpa only [state,Option.some.injEq] using reported,state⟩
    | nonrecursive v => simp [state] at reported
  · rintro ⟨row,found,eq,state⟩
    exact ⟨row,found,by simp [state,eq]⟩

theorem independent_original_g05_recursion_is_listed_at_its_exact_authored_ordinal488
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {coords : List (Fin n)}
    {Allowed : Nat → CandidateVisitKey485 n → Prop} {meaning : G05LocalMeaning487}
    {r : G05Report487 n}
    (exact : G05ExactCandidateReport487 p gd pos rel coords Allowed meaning r) (ord : Nat) :
    ord ∈ reportedOriginalG05Cycles488 r.rows ↔
      ∃ i : Fin (visible485 p).length, (∃ d, OriginalRosterCell485 p i.val (ord,d)) ∧
        IndependentScopedReturn487 p gd pos rel coords Allowed i := by
  rw [original_g05_cycle_ordinals_are_exactly_the_cyclic_rows488]
  constructor
  · rintro ⟨real,atList,identity,flag⟩
    obtain ⟨j,less,indexed⟩ := List.mem_iff_getElem.mp atList
    let i : Fin (visible485 p).length := ⟨j,exact.2.1 ▸ less⟩
    have inRow : r.rows[i.val]? = some real := by
      rw [List.getElem?_eq_getElem less,indexed]
    obtain ⟨row,d,here,original,_,classification⟩ := exact.2.2 i
    have same := Option.some.inj (here.symm.trans inRow)
    subst row
    rw [flag] at classification
    exact ⟨i,⟨d,identity ▸ original⟩,classification⟩
  · rintro ⟨i,⟨d,origin⟩,cyclic⟩
    obtain ⟨row,d',here,original,_,classification⟩ := exact.2.2 i
    have identity : row.ordinal = ord := congrArg Prod.fst (Option.some.inj
      (((roster_cell_reads_exactly_its_two_original_slots485 _ _ _).mpr original).symm.trans
        ((roster_cell_reads_exactly_its_two_original_slots485 _ _ _).mpr origin)))
    cases flag : row.mark with
    | requiredCycle => exact ⟨row,List.mem_of_getElem? here,identity,flag⟩
    | nonrecursive v =>
      rw [flag] at classification
      exact False.elim (classification.1 cyclic)

theorem eligible_report_excludes_every_independently_visited_k2_cycle488
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {coords : List (Fin n)}
    {Allowed : Nat → CandidateVisitKey485 n → Prop} {meaning : G05LocalMeaning487}
    {r : G05Report487 n} {marks : List (Nat × G05LocalVerdict487)}
    (exact : G05ExactCandidateReport487 p gd pos rel coords Allowed meaning r)
    (ready : r.priority = .eligible marks) :
    ∀ i : Fin (visible485 p).length, ¬ IndependentScopedReturn487 p gd pos rel coords Allowed i := by
  intro i recurs
  obtain ⟨row,d,_,cell,_,_⟩ := exact.2.2 i
  have listed := (independent_original_g05_recursion_is_listed_at_its_exact_authored_ordinal488
    exact row.ordinal).mpr ⟨i,⟨d,cell⟩,recurs⟩
  have h : (reportedOriginalG05Cycles488 r.rows) ≠ [] := by
    intro empty
    simp [empty] at listed
  have computed := exact.1.symm.trans ready
  change (match reportedOriginalG05Cycles488 r.rows with
    | [] => G05Priority487.eligible (r.rows.filterMap fun row => match row.mark with
      | .requiredCycle => none
      | .nonrecursive v => some (row.ordinal,v))
    | a::tail => G05Priority487.recursive (a::tail)) = G05Priority487.eligible marks at computed
  cases cycles : reportedOriginalG05Cycles488 r.rows with
  | nil => exact h cycles
  | cons i rest => rw [cycles] at computed; cases computed

theorem recursive_report_keeps_the_whole_original_ordered_hit_list488
    {n : Nat} (r : G05Report487 n) (hits : List Nat)
    (correct : r.priority = G05PriorityOfRows487 r.rows) :
    r.priority = .recursive hits ↔
      hits = reportedOriginalG05Cycles488 r.rows ∧ hits ≠ [] := by
  rw [correct]
  change (match reportedOriginalG05Cycles488 r.rows with
    | [] => G05Priority487.eligible (r.rows.filterMap fun row => match row.mark with
      | .requiredCycle => none
      | .nonrecursive v => some (row.ordinal,v))
    | head::tail => G05Priority487.recursive (head::tail)) = G05Priority487.recursive hits ↔ _
  cases got : reportedOriginalG05Cycles488 r.rows with
  | nil => simp
  | cons a rest =>
    constructor
    · intro h
      have eq := (G05Priority487.recursive.inj h).symm
      exact ⟨eq,by rw [eq]; exact List.cons_ne_nil _ _⟩
    · rintro ⟨rfl,_⟩
      rfl

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
