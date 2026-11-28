import Yulang.GeneralDeclarativeI65I74CompiledCandidateFootprint486
import Yulang.GeneralDeclarativeI65I74OriginalArgumentStart486

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions)

def computeOrderedArgumentFootprints486 {n : Nat} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n)) (palette : SignedPalette486 n)
    (i : Nat) (permit : CandidateVisitKey485 n → Bool) :
    Nat → List (Fin n) → Option (List (CandidateVisitKey485 n) × List (CandidatePathWire485 n))
  | _,[] => some ([],[])
  | offset,root::roots => do
    let head ← readOriginalArgumentStart486 p gd pos i offset root
    let (keys,wires) ← computeCandidateFootprint486 rel palette offset head.site permit
    let (other,rest) ← computeOrderedArgumentFootprints486 p gd pos rel palette i permit (offset+1) roots
    pure (keys++other,wires++rest)

def computeAllActualArgumentFootprints486 {n : Nat} (p : FullProblem)
    (gd : CheckedTable p.old.state.core.current) (pos : Positions n) (rel : List (Fin n × Fin n))
    (palette : SignedPalette486 n) (i : Nat) (permit : CandidateVisitKey485 n → Bool)
    (roots : List (Fin n)) : Option (List (CandidateVisitKey485 n) × List (CandidatePathWire485 n)) :=
  if roots.length = p.old.root.demand.arguments.length then
    computeOrderedArgumentFootprints486 p gd pos rel palette i permit 0 roots
  else none

/-- Independent description of the whole ordered head-argument plan.
It records each checked start separately, not a winner or role matching. -/
inductive OrderedOriginalArguments486 {n : Nat} (p : FullProblem)
    (gd : CheckedTable p.old.state.core.current) (pos : Positions n) (rel : List (Fin n × Fin n))
    (palette : SignedPalette486 n) (i : Nat) (permit : CandidateVisitKey485 n → Bool) :
    Nat → List (Fin n) → List (CandidateVisitKey485 n) → Prop where
  | nil : OrderedOriginalArguments486 p gd pos rel palette i permit offset [] []
  | cons (atHead : OriginalArgumentStart486 p gd pos i offset root) :
      front = finiteAuthorizedVisitPlan486 rel palette offset atHead.site permit →
      OrderedOriginalArguments486 p gd pos rel palette i permit (offset+1) roots rest →
      OrderedOriginalArguments486 p gd pos rel palette i permit offset (root::roots) (front++rest)

theorem independent_argument_footprints_keep_all_ordered_data_with_append486
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current} {pos : Positions n}
    {rel : List (Fin n × Fin n)} {i : Nat} {Auth : CandidateVisitKey485 n → Prop}
    {k1 k2 w1 w2 b1 b2}
    (front : ExactCandidateFootprint485 p gd pos rel i Auth k1 w1 b1)
    (rear : ExactCandidateFootprint485 p gd pos rel i Auth k2 w2 b2) :
    ExactCandidateFootprint485 p gd pos rel i Auth (k1++k2) (w1++w2) (b1++b2) := by
  induction front with
  | nil => exact rear
  | cons read auth deep _ ih => exact .cons read auth deep ih


theorem exact_footprint_checker_preserves_concatenated_original_argument_data486
    {n : Nat} (p : FullProblem) (gd : CheckedTable p.old.state.core.current) (pos : Positions n)
    (rel : List (Fin n × Fin n)) (i : Nat) (permit : CandidateVisitKey485 n → Bool)
    {frontKeys rearKeys frontWires rearWires frontBits rearBits}
    (front : readCandidateFootprint485 p gd pos rel i permit frontKeys frontWires = some frontBits)
    (rear : readCandidateFootprint485 p gd pos rel i permit rearKeys rearWires = some rearBits) :
    readCandidateFootprint485 p gd pos rel i permit (frontKeys++rearKeys) (frontWires++rearWires) =
      some (frontBits++rearBits) := by
  induction frontKeys generalizing frontWires frontBits with
  | nil =>
    cases frontWires with
    | nil =>
      have one : [] = frontBits := Option.some.inj front
      subst frontBits
      exact rear
    | cons => simp [readCandidateFootprint485] at front
  | cons key tail ih =>
    cases frontWires with
    | nil => simp [readCandidateFootprint485] at front
    | cons w ws =>
      unfold readCandidateFootprint485 at front
      split at front
      · cases front
      · rename_i kept
        cases localFound : readCandidatePath485 p gd pos rel i w with
        | none => simp [localFound] at front
        | some found =>
          cases next : readCandidateFootprint485 p gd pos rel i permit tail ws with
          | none => simp [localFound,next] at front
          | some bits =>
            have exact : found.terminalBit::bits = frontBits := Option.some.inj
              (by simpa [localFound,next] using front)
            subst frontBits
            have afterwards := ih next
            change readCandidateFootprint485 p gd pos rel i permit (key::(tail++rearKeys))
              (w::(ws++rearWires)) = some (found.terminalBit::(bits++rearBits))
            rw [readCandidateFootprint485,ite_eq_right kept]
            simp [localFound,afterwards,Option.bind]

theorem independently_given_all_original_argument_starts_compile_one_exact_candidate_footprint486
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {palette : SignedPalette486 n}
    (complete : CompletePalette486 p.old.state.core pos rel palette)
    (i : Nat) (permit : CandidateVisitKey485 n → Bool) (Auth : CandidateVisitKey485 n → Prop)
    (sound : ∀ k, permit k = true → Auth k) (roots : List (Fin n)) (offset : Nat)
    (starts : ∀ j root, roots[j]? = some root → Nonempty (OriginalArgumentStart486 p gd pos i (offset+j) root)) :
    ∃ keys wires bits, computeOrderedArgumentFootprints486 p gd pos rel palette i permit offset roots =
        some (keys,wires) ∧
      OrderedOriginalArguments486 p gd pos rel palette i permit offset roots keys ∧
      ExactCandidateFootprint485 p gd pos rel i Auth keys wires bits ∧
      readCandidateFootprint485 p gd pos rel i permit keys wires = some bits := by
  induction roots generalizing offset with
  | nil => exact ⟨[],[],[],rfl,.nil,.nil,rfl⟩
  | cons root roots ih =>
    obtain ⟨head⟩ := starts 0 root rfl
    change OriginalArgumentStart486 p gd pos i offset root at head
    have seat : head.head.orig.location.visibleOrdinal = i := congrArg (·.visibleOrdinal) head.address
    have literal : head.head.orig.location.headArgument = offset := congrArg (·.headArgument) head.address
    obtain ⟨these,wires,checks,runs,keys,correct,replays⟩ :=
      computed_candidate_footprint_replays_all_its_original_authorized_sites486 complete i head.ordinal head.head
        seat head.cell head.site rfl rfl head.root permit Auth sound
    rw [literal] at runs keys
    obtain ⟨later,more,checks2,runs2,orderOK,exact,readLater⟩ :=
      ih (offset+1) (fun j pos selected => by
        have ord := starts (j+1) pos selected
        simpa [Nat.add_assoc,Nat.add_comm 1 j] using ord)
    have atHead := independently_checked_arg_start_replays_at_exact_original_roster_and_demand_coordinate486 head
    refine ⟨these++later,wires++more,checks++checks2,?_,.cons head keys orderOK,
      independent_argument_footprints_keep_all_ordered_data_with_append486 correct exact,
      exact_footprint_checker_preserves_concatenated_original_argument_data486 p gd pos rel i permit replays readLater⟩
    simp [computeOrderedArgumentFootprints486,atHead,runs,runs2,Option.bind]

theorem each_planned_key_is_an_independent_proper_visit_of_one_actual_original_argument486
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {palette : SignedPalette486 n}
    {i : Nat} {permit : CandidateVisitKey485 n → Bool} {Auth : CandidateVisitKey485 n → Prop}
    (complete : CompletePalette486 p.old.state.core pos rel palette)
    (exactPermit : ∀ key, permit key = true ↔ Auth key)
    {offset : Nat} {roots : List (Fin n)} {keys : List (CandidateVisitKey485 n)}
    (planned : OrderedOriginalArguments486 p gd pos rel palette i permit offset roots keys)
    (key : CandidateVisitKey485 n) :
    key ∈ keys ↔ ∃ root argument, (root,argument) ∈ roots.zipIdx offset ∧
      ∃ head : OriginalArgumentStart486 p gd pos i argument root,
        IndependentAuthorizedVisit486 rel argument head.site Auth key := by
  induction planned with
  | nil => simp
  | @cons offset root front roots rest head exact restPlan ih =>
    simp only [List.zipIdx_cons,List.mem_append]
    constructor
    · intro member
      rcases member with belongs|later
      · have visitProof := (generated_plan_keys_are_exactly_the_authorized_existing_proper_visits486
          palette complete offset head.site permit Auth exactPermit key).mp (exact ▸ belongs)
        exact ⟨root,offset,List.mem_cons_self ..,head,visitProof⟩
      · obtain ⟨coordinate,argument,occ,start,visitProof⟩ := ih.mp later
        exact ⟨coordinate,argument,List.mem_cons_of_mem _ occ,start,visitProof⟩
    · rintro ⟨coordinate,argument,found,original,visitProof⟩
      rcases List.mem_cons.mp found with same|more
      · cases same
        have saved := independently_checked_arg_start_replays_at_exact_original_roster_and_demand_coordinate486 head
        have observed := independently_checked_arg_start_replays_at_exact_original_roster_and_demand_coordinate486 original
        have agree := Option.some.inj (observed.symm.trans saved)
        subst original
        exact .inl (exact.symm ▸
          (generated_plan_keys_are_exactly_the_authorized_existing_proper_visits486 palette complete offset
            head.site permit Auth exactPermit key).mpr visitProof)
      · exact .inr (ih.mpr ⟨coordinate,argument,more,original,visitProof⟩)

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
