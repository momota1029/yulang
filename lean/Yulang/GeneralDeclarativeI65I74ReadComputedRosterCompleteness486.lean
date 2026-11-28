import Yulang.GeneralDeclarativeI65I74ComputedWholeRoster486

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions)
open LiteralVisits473 (Checkpoint)
open TypedRootSafety482 (AllRootSafe requestRootCheck requestRootCheckSound)
open GeneralDeclarations (Declaration)

private theorem a_finite_successful_map_keeps_each_original_slot
    {α β : Type} (xs : List α) (f : α → Option β) (holds : α → β → Prop)
    (available : ∀ a ∈ xs, ∃ b, f a = some b ∧ holds a b) :
    ∃ ys : List β, xs.mapM (m := Option) f = some ys ∧ ys.length = xs.length ∧
      ∀ (k : Nat) (a : α), xs[k]? = some a → ∃ b, ys[k]? = some b ∧ holds a b := by
  induction xs with
  | nil => exact ⟨[],rfl,rfl,by simp⟩
  | cons x xs ih =>
    obtain ⟨y,ran,holdsHere⟩ := available x (List.mem_cons_self ..)
    obtain ⟨ys,later,len,all⟩ := ih (fun a m => available a (List.mem_cons_of_mem _ m))
    refine ⟨y::ys,by simp [List.mapM_cons,ran,later,Option.bind],congrArg Nat.succ len,?_⟩
    intro k a here
    cases k with
    | zero =>
      have same : x = a := Option.some.inj here
      subst a
      exact ⟨y,rfl,holdsHere⟩
    | succ k => exact all k a here

private theorem related_exact_slots_replay_the_given_whole_candidate_tape
    {Wire : Type} (p : FullProblem) (check : CandidateCheck Wire)
    (slots : List Nat) (actual : List (Nat × Wire))
    (count : actual.length = slots.length)
    (cached : ∀ (j : Nat) (i : Nat) (w : Nat × Wire),
      slots[j]? = some i → actual[j]? = some w →
      ∃ d bit, OriginalRosterCell485 p i (w.1,d) ∧ check w.1 d w.2 = some bit) :
    ∃ bits, replaySlots485 p check slots actual = some bits := by
  induction slots generalizing actual with
  | nil =>
    cases actual with
    | nil => exact ⟨[],rfl⟩
    | cons => simp at count
  | cons i is ih =>
    cases actual with
    | nil => simp at count
    | cons first rest =>
      obtain ⟨d,bit,original,head⟩ := cached 0 i first rfl rfl
      obtain ⟨later,run⟩ := ih rest (Nat.succ.inj count)
        (fun j k w first second => cached (j+1) k w first second)
      rcases first with ⟨ord,w⟩
      have roster := (roster_cell_reads_exactly_its_two_original_slots485 _ _ _).mpr original
      exact ⟨(ord,bit)::later,by simp [replaySlots485,roster,head,run,Option.bind]⟩

theorem independently_scoped_all_canonical_head_coordinates_produce_a_rechecked_whole_tape486
    {n : Nat} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n)) (palette : SignedPalette486 n)
    (complete : CompletePalette486 p.old.state.core pos rel palette)
    (roots : List (Checkpoint n)) (permit : Nat → CandidateVisitKey485 n → Bool)
    (Authorized : Nat → CandidateVisitKey485 n → Prop)
    (permission : ∀ ord key, permit ord key = true → Authorized ord key)
    (rootsChecked : requestRootCheck p pos rel roots = true)
    (count : roots.length = p.old.root.demand.arguments.length)
    (actualArity : ∀ (i : Nat) (d : Declaration), (visible485 p)[i]? = some d →
      d.head.length = p.old.root.demand.arguments.length)
    (starts : ∀ i : Fin (visible485 p).length, ∀ argument root,
      (roots.map Checkpoint.which)[argument]? = some root →
      Nonempty (OriginalArgumentStart486 p gd pos i.val argument root)) :
    ∃ rows bits,
      compileWholeOriginalRoster486 p gd pos rel palette (roots.map Checkpoint.which) permit = some rows ∧
      readTape485 p
        (readPlannedLocal485 p gd pos rel (rows.map ComputedOriginalCandidate486.keys)
          (permitAtOriginalVisibleSlot486 p permit))
        (rows.map fun x => (x.authoredOrdinal,x.packet)) = some bits ∧
      readComputedPreElection486 p gd pos rel palette roots permit = some (gate485 bits) := by
  let coordinates := roots.map Checkpoint.which
  let compile := compileOriginalCandidate486 p gd pos rel palette coordinates permit
  let checked (i : Nat) (row : ComputedOriginalCandidate486 n) : Prop :=
    row.packet.visibleOrdinal = i ∧ ∃ d signs,
      OriginalRosterCell485 p i (row.authoredOrdinal,d) ∧
      readCandidateFootprint485 p gd pos rel i (permit row.authoredOrdinal) row.keys row.packet.paths = some signs
  have existsRow : ∀ i ∈ List.range (visible485 p).length, ∃ row, compile i = some row ∧ checked i row := by
    intro i inRange
    let atIndex : Fin (visible485 p).length := ⟨i,List.mem_range.mp inRange⟩
    obtain ⟨⟨ordinal,d⟩,read⟩ := no_visible_slot_is_lost_in_the_exact_roster485 p atIndex
    have location := (roster_cell_reads_exactly_its_two_original_slots485 _ _ _).mp read
    have arity := actualArity i d location.1
    obtain ⟨keys,wires,bits,run,_,_,replay⟩ :=
      independently_given_all_original_argument_starts_compile_one_exact_candidate_footprint486
        complete i (permit ordinal) (Authorized ordinal) (permission ordinal) coordinates 0
        (fun j root here => by
          have fit := starts atIndex j root here
          simpa using fit)
    have readWhole : computeAllActualArgumentFootprints486 p gd pos rel palette i (permit ordinal) coordinates =
        some (keys,wires) := by
      have len : coordinates.length = p.old.root.demand.arguments.length := by simpa [coordinates] using count
      simp only [computeAllActualArgumentFootprints486,len,ite_true,run]
    change rosterCell485 p i = some (ordinal,d) at read
    exact ⟨⟨ordinal,keys,⟨i,wires⟩⟩,by simp [compile,compileOriginalCandidate486,read,arity,readWhole,Option.bind],
      rfl,d,bits,location,replay⟩
  obtain ⟨rows,generated,length,exact⟩ :=
    a_finite_successful_map_keeps_each_original_slot (List.range (visible485 p).length) compile checked existsRow
  let plans := rows.map ComputedOriginalCandidate486.keys
  let packets := rows.map fun x => (x.authoredOrdinal,x.packet)
  let check := readPlannedLocal485 p gd pos rel plans (permitAtOriginalVisibleSlot486 p permit)
  have sameLength : packets.length = (List.range (visible485 p).length).length := by
    change (List.map _ rows).length = _
    simpa using length
  obtain ⟨bits,accepted⟩ :=
    related_exact_slots_replay_the_given_whole_candidate_tape p check
      (List.range (visible485 p).length) packets sameLength (fun j i w slot claim => by
        obtain ⟨row,rowAt,which,d,signs,known,proved⟩ := exact j i slot
        have ne : j < (visible485 p).length := by
          have tiny := (List.getElem?_eq_some_iff.mp slot).1
          simpa using tiny
        have eq : j = i := by
          have h : (List.range (visible485 p).length)[j]? = some j := by simp [ne]
          exact Option.some.inj (h.symm.trans slot)
        subst j
        have planAt : plans[i]? = some row.keys := by
          change (rows.map ComputedOriginalCandidate486.keys)[i]? = _
          simp [List.getElem?_map,rowAt]
        have actualClaim : (row.authoredOrdinal,row.packet) = w := Option.some.inj
          ((by simp [packets,List.getElem?_map,rowAt] : packets[i]? = some (row.authoredOrdinal,row.packet)).symm.trans claim)
        subst w
        refine ⟨d,signs.any id,known,?_⟩
        have source := (roster_cell_reads_exactly_its_two_original_slots485 _ _ _).mpr known
        have allows : permitAtOriginalVisibleSlot486 p permit i = permit row.authoredOrdinal := by
          funext key
          simp [permitAtOriginalVisibleSlot486,source]
        simp [check,readPlannedLocal485,which,source,planAt,allows,proved,Option.bind])
  change compileWholeOriginalRoster486 p gd pos rel palette coordinates permit = some rows at generated
  have ran : readTape485 p check packets = some bits := accepted
  have planLength : plans.length = (visible485 p).length := by simpa [plans] using length
  have wasChecked : readPlannedPreElection485 p gd pos rel plans (permitAtOriginalVisibleSlot486 p permit) packets =
      some (gate485 bits) := by
    simp only [readPlannedPreElection485,planLength,ite_true,beforeElection485]
    change (readTape485 p check packets).map gate485 = _
    rw [ran]
    rfl
  refine ⟨rows,bits,generated,ran,?_⟩
  unfold readComputedPreElection486
  rw [rootsChecked]
  simp only [ite_true]
  change (do
    let computed ← compileWholeOriginalRoster486 p gd pos rel palette coordinates permit
    readPlannedPreElection485 p gd pos rel (computed.map ComputedOriginalCandidate486.keys)
      (permitAtOriginalVisibleSlot486 p permit) (computed.map fun (x : ComputedOriginalCandidate486 n) => (x.authoredOrdinal,x.packet))) = _
  simp only [generated,bind,Option.bind]
  exact wasChecked

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
