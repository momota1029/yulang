import Yulang.GeneralDeclarativeI65I74G05EquivalentReification488

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions)
open TypedRootSafety482 (AllRootSafe)

theorem no_scoped_original_return_when_there_are_no_demanded_coordinates488
    {n : Nat} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n))
    (Allowed : Nat → CandidateVisitKey485 n → Prop) (i : Nat) :
    ¬ IndependentScopedReturn487 p gd pos rel [] Allowed i := by
  simp [IndependentScopedReturn487]

theorem the_exact_observation_list_is_empty_without_original_argument_coordinates488
    {n : Nat} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n))
    (Allowed : CandidateVisitKey485 n → Prop) (i : Nat) (keys : List (CandidateVisitKey485 n)) :
    G05OriginalVisitsExact487 p gd pos rel [] i Allowed keys ↔ keys = [] := by
  cases keys with
  | nil => simp [G05OriginalVisitsExact487]
  | cons a rest =>
    simp only [G05OriginalVisitsExact487,List.zipIdx_nil,List.not_mem_nil,false_and,
      exists_false,iff_false,reduceCtorEq,iff_false]
    intro impossible
    exact impossible a (List.mem_cons_self ..)

theorem empty_safe_coordinate_list_has_no_hidden_requested_lower488
    {n : Nat} {p : FullProblem} {pos : Positions n}
    (roots : AllRootSafe p.old.state.core pos (p.old.root.demand.arguments.map (·.lower)) []) :
    p.old.root.demand.arguments = [] := by
  cases args : p.old.root.demand.arguments with
  | nil => rfl
  | cons a rest => simp [args,AllRootSafe] at roots

def originalNoArgumentCandidate488 {n : Nat} (p : FullProblem) (i : Nat) :
    Option (ComputedOriginalCandidate486 n) :=
  (rosterCell485 p i).map fun row => ⟨row.1,[],⟨i,[]⟩⟩

def compileNoArgumentRoster488 {n : Nat} (p : FullProblem) :
    Option (List (ComputedOriginalCandidate486 n)) :=
  (List.range (visible485 p).length).mapM (originalNoArgumentCandidate488 p)

theorem no_argument_candidate_uses_the_same_visible_and_origin_slots_without_a_local_decision488
    {n : Nat} (p : FullProblem) (i : Fin (visible485 p).length) :
    ∃ d ord, OriginalRosterCell485 p i.val (ord,d) ∧
      @originalNoArgumentCandidate488 n p i.val = some ⟨ord,[],⟨i.val,[]⟩⟩ := by
  obtain ⟨⟨ord,d⟩,ranked⟩ := no_visible_slot_is_lost_in_the_exact_roster485 p i
  exact ⟨d,ord,(roster_cell_reads_exactly_its_two_original_slots485 _ _ _).mp ranked,
    by simp [originalNoArgumentCandidate488,ranked]⟩

private theorem mapM_reads_every_real_visible_replay488
    {α β : Type} (input : List α) (f : α → Option β) (P : α → β → Prop)
    (every : ∀ x ∈ input, ∃ y, f x = some y ∧ P x y) :
    ∃ out : List β, input.mapM (m := Option) f = some out ∧ input.length = out.length ∧
      ∀ (j : Nat) (x : α), input[j]? = some x → ∃ y, out[j]? = some y ∧ P x y := by
  induction input with
  | nil => exact ⟨[],rfl,rfl,by simp⟩
  | cons top tail ih =>
    obtain ⟨first,ran,known⟩ := every top (List.mem_cons_self ..)
    obtain ⟨rest,next,count,each⟩ := ih (fun x inTail => every x (List.mem_cons_of_mem _ inTail))
    refine ⟨first::rest,by simp [List.mapM_cons,ran,next,Option.bind],congrArg Nat.succ count,?_⟩
    intro j x what
    cases j with
    | zero =>
      have same : top = x := Option.some.inj what
      subst x
      exact ⟨first,rfl,known⟩
    | succ j => exact each j x what

private theorem signless_declared_slots_replay_if_every_input_is_checked488
    {Wire : Type} (p : FullProblem) (check : CandidateCheck Wire)
    (slots : List Nat) (packets : List (Nat × Wire))
    (count : slots.length = packets.length)
    (prepare : ∀ (j : Nat) (i : Nat) (w : Nat × Wire),
      slots[j]? = some i → packets[j]? = some w →
      ∃ d, OriginalRosterCell485 p i (w.1,d) ∧ check w.1 d w.2 = some false) :
    replaySlots485 p check slots packets = some (packets.map (fun x => (x.1,false))) := by
  induction slots generalizing packets with
  | nil =>
    cases packets with
    | nil => rfl
    | cons => simp at count
  | cons point rest ih =>
    cases packets with
    | nil => simp at count
    | cons w next =>
      obtain ⟨d,whereAt,mark⟩ := prepare 0 point w rfl rfl
      obtain ⟨ordinal,body⟩ := w
      have known := (roster_cell_reads_exactly_its_two_original_slots485 _ _ _).mpr whereAt
      have endResult := ih next (Nat.succ.inj count)
        (fun j k row num packet => prepare (j+1) k row num packet)
      simp [replaySlots485,known,mark,endResult,Option.bind]

theorem zero_demand_arg_roster_generates_exactly_one_empty_wire_per_visible_slot488
    {n : Nat} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n))
    (permit : Nat → CandidateVisitKey485 n → Bool) :
    ∃ rows : List (ComputedOriginalCandidate486 n),
      compileNoArgumentRoster488 p = some rows ∧ rows.length = (visible485 p).length ∧
      readTape485 p
        (readPlannedLocal485 p gd pos rel (rows.map ComputedOriginalCandidate486.keys)
          (permitAtOriginalVisibleSlot486 p permit)) (rows.map fun x => (x.authoredOrdinal,x.packet)) =
        some (rows.map fun x => (x.authoredOrdinal,false)) ∧
      ∀ (i : Fin (visible485 p).length), ∃ d ord,
        OriginalRosterCell485 p i.val (ord,d) ∧ rows[i.val]? = some ⟨ord,[],⟨i.val,[]⟩⟩ := by
  let ids := List.range (visible485 p).length
  let RowExpected (i : Nat) (row : ComputedOriginalCandidate486 n) : Prop :=
    ∃ d ord, OriginalRosterCell485 p i (ord,d) ∧ row = ⟨ord,[],⟨i,[]⟩⟩
  obtain ⟨rows,made,len,entries⟩ := mapM_reads_every_real_visible_replay488
      ids (originalNoArgumentCandidate488 p) RowExpected (fun i has => by
        let atI : Fin (visible485 p).length := ⟨i,List.mem_range.mp has⟩
        obtain ⟨d,ord,r,g⟩ := no_argument_candidate_uses_the_same_visible_and_origin_slots_without_a_local_decision488
          (n := n) p atI
        exact ⟨_,g,d,ord,r,rfl⟩)
  have each (i : Fin (visible485 p).length) :
      ∃ d ord, OriginalRosterCell485 p i.val (ord,d) ∧ rows[i.val]? = some ⟨ord,[],⟨i.val,[]⟩⟩ := by
    obtain ⟨row,atRow,d,ord,cell,same⟩ := entries i.val i.val (List.getElem?_range i.isLt)
    exact ⟨d,ord,cell,same ▸ atRow⟩
  refine ⟨rows,made,by simpa only [ids,List.length_range] using len.symm,?_,each⟩
  let plans := rows.map ComputedOriginalCandidate486.keys
  let packets := rows.map fun x => (x.authoredOrdinal,x.packet)
  let reader := readPlannedLocal485 p gd pos rel plans (permitAtOriginalVisibleSlot486 p permit)
  have count : ids.length = packets.length := by simpa only [packets,List.length_map] using len
  have sliced := signless_declared_slots_replay_if_every_input_is_checked488 p reader ids packets count
    (fun j i wire found address => by
      have h : j < (visible485 p).length := by
        have bound := (List.getElem?_eq_some_iff.mp found).1
        simpa only [ids,List.length_range] using bound
      have same : j = i := Option.some.inj ((List.getElem?_range h).symm.trans found)
      subst i
      obtain ⟨d,ord,cell,rowAt⟩ := each ⟨j,h⟩
      have packet : (ord,⟨j,[]⟩) = wire := Option.some.inj
        ((by simp [packets,List.getElem?_map,rowAt] : packets[j]? = some (ord,⟨j,[]⟩)).symm.trans address)
      subst wire
      have source := (roster_cell_reads_exactly_its_two_original_slots485 _ _ _).mpr cell
      have planAt : plans[j]? = some [] := by simp [plans,List.getElem?_map,rowAt]
      exact ⟨d,cell,by simp [reader,readPlannedLocal485,source,planAt,readCandidateFootprint485,Option.bind]⟩)
  simpa only [readTape485,ids,reader,packets,List.map_map,Function.comp_def] using sliced

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
