import Yulang.GeneralDeclarativeI65I74OriginalRoster485

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)
open GeneralDeclarations (Declaration)

abbrev CandidateCheck (Wire : Type) := Nat → Declaration → Wire → Option Bool
abbrev CandidateLocal (Wire : Type) := Nat → Declaration → Wire → Bool → Prop

def replaySlots485 (p : FullProblem) (check : CandidateCheck Wire) :
    List Nat → List (Nat × Wire) → Option (List (Nat × Bool))
  | [],[] => some []
  | i::is,(claim,wire)::ws => do
      let (ord,d) ← rosterCell485 p i
      if claim ≠ ord then none else
        let bit ← check ord d wire
        let rest ← replaySlots485 p check is ws
        pure ((ord,bit)::rest)
  | _,_ => none

def readTape485 (p : FullProblem) (check : CandidateCheck Wire)
    (packets : List (Nat × Wire)) : Option (List (Nat × Bool)) :=
  replaySlots485 p check (List.range (visible485 p).length) packets

/-- The independently supplied rule test accounts for the actual candidate.
An unverified slot does not imply that the candidate mismatched. -/
inductive ExactTape485 (p : FullProblem) (rule : CandidateLocal Wire) :
    List Nat → List (Nat × Wire) → List (Nat × Bool) → Prop where
  | nil : ExactTape485 p rule [] [] []
  | cons : OriginalRosterCell485 p i (ord,d) → rule ord d wire bit →
      ExactTape485 p rule is ws rest →
      ExactTape485 p rule (i::is) ((ord,wire)::ws) ((ord,bit)::rest)

theorem replay_slots_preserves_and_reflects_every_independent_local_result485
    (p : FullProblem) (check : CandidateCheck Wire) (meaning : CandidateLocal Wire)
    (localExact : ∀ ord d wire bit, check ord d wire = some bit ↔ meaning ord d wire bit)
    (slots : List Nat) (wires : List (Nat × Wire)) (out : List (Nat × Bool)) :
    replaySlots485 p check slots wires = some out ↔ ExactTape485 p meaning slots wires out := by
  constructor
  · induction slots generalizing wires out with
    | nil =>
      cases wires with
      | nil =>
        intro h
        have q : [] = out := Option.some.inj h
        subst out
        exact .nil
      | cons => simp [replaySlots485]
    | cons i is ih =>
      cases wires with
      | nil => simp [replaySlots485]
      | cons packet ws =>
        rcases packet with ⟨claim,wire⟩
        intro ran
        cases seat : rosterCell485 p i with
        | none => simp [replaySlots485,seat] at ran
        | some cell =>
          rcases cell with ⟨ord,d⟩
          by_cases eq : claim = ord
          · subst claim
            cases item : check ord d wire with
            | none => simp [replaySlots485,seat,item] at ran
            | some bit =>
              cases rest : replaySlots485 p check is ws with
              | none => simp [replaySlots485,seat,rest] at ran
              | some tail =>
                have same : (ord,bit)::tail = out :=
                  Option.some.inj (by simpa [replaySlots485,seat,item,rest] using ran)
                subst out
                exact .cons ((roster_cell_reads_exactly_its_two_original_slots485 _ _ _).mp seat)
                  ((localExact _ _ _ _).mp item) (ih _ _ rest)
          · simp [replaySlots485,seat,eq] at ran
  · intro proof
    induction proof with
    | nil => rfl
    | cons cell result _ ih =>
      have seat := (roster_cell_reads_exactly_its_two_original_slots485 _ _ _).mpr cell
      have item := (localExact _ _ _ _).mpr result
      simp [replaySlots485,seat,item,ih]

theorem whole_tape_has_exact_visible_length_and_original_slot_order485
    (p : FullProblem) (meaning : CandidateLocal Wire) {slots wires out}
    (proof : ExactTape485 p meaning slots wires out) :
    wires.length = slots.length ∧ out.length = slots.length ∧
      ∀ (i : Nat) (w : Nat × (Nat × Wire)), (slots.zip wires)[i]? = some w →
      ∃ row bit, OriginalRosterCell485 p w.1 (w.2.1,row) ∧
        meaning w.2.1 row w.2.2 bit ∧ out[i]? = some (w.2.1,bit) := by
  induction proof with
  | nil => simp
  | cons slot matched _ ih =>
    refine ⟨congrArg Nat.succ ih.1,congrArg Nat.succ ih.2.1,?_⟩
    intro i w atIndex
    cases i with
    | zero =>
      simp at atIndex
      subst w
      exact ⟨_,_,slot,matched,rfl⟩
    | succ i =>
      exact ih.2.2 i w atIndex

theorem read_tape_reflects_the_actual_entire_visible_order485
    (p : FullProblem) (check : CandidateCheck Wire) (meaning : CandidateLocal Wire)
    (localExact : ∀ ord d wire bit, check ord d wire = some bit ↔ meaning ord d wire bit)
    (wires : List (Nat × Wire)) (out : List (Nat × Bool)) :
    readTape485 p check wires = some out ↔
      ExactTape485 p meaning (List.range (visible485 p).length) wires out :=
  replay_slots_preserves_and_reflects_every_independent_local_result485
    p check meaning localExact _ wires out

theorem an_omitted_or_extra_visible_candidate_cannot_be_ignored485
    (p : FullProblem) (check : CandidateCheck Wire) (wires : List (Nat × Wire))
    (changedLength : wires.length ≠ (visible485 p).length) :
    readTape485 p check wires = none := by
  cases result : readTape485 p check wires with
  | none => rfl
  | some out =>
    have exact := (read_tape_reflects_the_actual_entire_visible_order485
      p check (fun ord r w b => check ord r w = some b) (fun _ _ _ _ => Iff.rfl) wires out).mp result
    have lengths := (whole_tape_has_exact_visible_length_and_original_slot_order485 _ _ exact).1
    exact False.elim (changedLength (by simpa using lengths))

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
