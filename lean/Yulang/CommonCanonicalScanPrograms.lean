import Yulang.CommonCanonicalReductionMachine

namespace Yulang.CommonCanonicalReductionMachine

open CanonicalRegisterMachine
open CanonicalRegisterMachine.Routine
open CommonCanonicalSerialization
open CommonCanonicalEmitters
open CommonCanonicalConstraintPrograms
open CommonCanonicalCounterConstraints
open CommonCanonicalRowTests

def scanTests {registers states : Nat} :
    (count start : Nat) → start + count ≤ states → List (Instruction registers states) →
      List (Test (registers + 1) (states + states))
  | 0, _, _, _ => []
  | count + 1, start, bound, code =>
      let pc : Fin states := ⟨start, by omega⟩
      (partitionTests registers pc ++ instructionTests pc (code.head?.getD .halt)) ++
        scanTests count (start + 1) (by omega) code.tail

def HeaderField (field : Fin 10) : Prop := 0 < field.val ∧ field.val < 5

def scan (mode : Mode) : Routine 16 := loop 14 (append (block mode) (increment 13))

/-- The actual fuel loop visits exactly the requested finite state interval.
It consumes one table entry per state, with repeated default halt after nil. -/
theorem scan_runs {registers states : Nat} (count start : Nat) (bound : start + count ≤ states)
    (code : List (Instruction registers states)) (mode : Mode) (values : Values) (prior : Word)
    (cursor : values 0 = wordCode (list instruction code)) (encoded : values 1 = wordCode prior)
    (registersEq : environment values registersField = registers)
    (statesEq : environment values statesField = states) (pcEq : values 13 = start) (fuelEq : values 14 = count) :
    ∃ finalValues, Runs (scan mode) values finalValues ∧
      finalValues 1 = wordCode ((stream mode (scanTests count start bound code)).reverse ++ prior) ∧
      finalValues 0 = wordCode (list instruction (code.drop count)) ∧
      finalValues 13 = start + count ∧ finalValues 14 = 0 ∧
      ∀ field, HeaderField field → environment finalValues field = environment values field := by
  suffices ∃ finalValues, LoopRuns 14 (append (block mode) (increment 13)) values finalValues ∧
      finalValues 1 = wordCode ((stream mode (scanTests count start bound code)).reverse ++ prior) ∧
      finalValues 0 = wordCode (list instruction (code.drop count)) ∧
      finalValues 13 = start + count ∧ finalValues 14 = 0 ∧
      ∀ field, HeaderField field → environment finalValues field = environment values field by
    obtain ⟨finalValues, execution, word, tail, pc, fuel, frame⟩ := this
    exact ⟨finalValues, loop_runs execution, word, tail, pc, fuel, frame⟩
  have streamAppend (first last : List (Test (registers + 1) (states + states))) :
      stream mode (first ++ last) = stream mode first ++ stream mode last := by
    cases mode <;> simp only [stream, fixedStream, valueStream, List.flatMap_append]
  have headerFacts (field : Fin 10) (kept : HeaderField field) :
      StableField field ∧ roster field ≠ 13 ∧ roster field ≠ 14 := by
    obtain ⟨positive, small⟩ := kept
    refine ⟨⟨by omega, Or.inl small⟩, ?_, ?_⟩
    all_goals apply Fin.ne_of_val_ne; simp only [roster]; split <;> omega
  induction count generalizing start code values prior with
  | zero =>
      refine ⟨values, .done fuelEq, ?_, ?_, ?_, fuelEq, fun _ _ => rfl⟩
      · cases mode <;> simpa only [scanTests, stream, fixedStream, valueStream, List.flatMap_nil,
          List.reverse_nil, List.nil_append] using encoded
      · simpa only [List.drop_zero] using cursor
      · simpa only [Nat.add_zero] using pcEq
  | succ count ih =>
      let pc : Fin states := ⟨start, by omega⟩
      let cut := write values 14 count
      have cutCursor : cut 0 = wordCode (list instruction code) := cursor
      have cutEncoded : cut 1 = wordCode prior := encoded
      have cutRegisters : environment cut registersField = registers := registersEq
      have cutStates : environment cut statesField = states := statesEq
      have cutPc : environment cut pcField = pc.val := pcEq
      obtain ⟨middle, blockRun, middleWord, middleCursor, middleFrame⟩ :=
        block_runs pc code mode cut prior cutCursor cutEncoded cutRegisters cutStates cutPc
      have middlePc : middle 13 = start :=
        (middleFrame pcField (by unfold StableField; decide)).trans pcEq
      have middleFuel : middle 14 = count :=
        (middleFrame 9 (by unfold StableField; decide)).trans (by rfl)
      let after := write middle 13 (middle 13 + 1)
      have incrementRun := atomic_runs (.increment (13 : Register) ()) middle
      have afterCursor : after 0 = wordCode (list instruction code.tail) := middleCursor
      have afterWord : after 1 = wordCode
          ((stream mode (partitionTests registers pc ++ instructionTests pc (code.head?.getD .halt))).reverse ++ prior) :=
        middleWord
      have afterRegisters : environment after registersField = registers :=
        (middleFrame registersField (by unfold StableField; decide)).trans cutRegisters
      have afterStates : environment after statesField = states :=
        (middleFrame statesField (by unfold StableField; decide)).trans cutStates
      have afterPc : after 13 = start + 1 := by simp only [after, write, ↓reduceIte, middlePc]
      have afterFuel : after 14 = count := middleFuel
      have remainingBound : start + 1 + count ≤ states := by omega
      obtain ⟨finalValues, remaining, finalWord, finalCursor, finalPc, finalFuel, finalFrame⟩ :=
        ih (start + 1) remainingBound code.tail after _ afterCursor afterWord afterRegisters afterStates afterPc afterFuel
      have cutEq : write values 14 (values 14 - 1) = cut := by simp only [fuelEq, Nat.add_sub_cancel, cut]
      have bodyRun : Runs (append (block mode) (increment 13)) (write values 14 (values 14 - 1)) after := by
        rw [cutEq]
        exact append_runs blockRun incrementRun
      refine ⟨finalValues, .next (by omega) bodyRun remaining, ?_, ?_, ?_, finalFuel, ?_⟩
      · simpa only [scanTests, streamAppend, List.reverse_append, List.append_assoc] using finalWord
      · cases code <;> simpa only [List.tail_nil, List.tail_cons, List.drop_nil, List.drop_succ_cons] using finalCursor
      · omega
      · intro field kept
        have facts := headerFacts field kept
        have afterFrame : environment after field = environment cut field := by
          change after (roster field) = cut (roster field)
          simp only [after, write, facts.2.1, ↓reduceIte]
          exact middleFrame field facts.1
        have cutFrame : environment cut field = environment values field := by
          simp only [environment, cut, write, facts.2.2, ↓reduceIte]
        exact (finalFrame field kept).trans (afterFrame.trans cutFrame)

/-- A full scan's specification is exactly the finite-state portion of the
original constraint compiler, including its default instruction lookup. -/
theorem scanTests_exact (source : Program) :
    scanTests source.states 0 (by omega) source.code =
      (List.finRange source.states).flatMap (fun pc => partitionTests source.registers pc ++
        instructionTests pc (instructionAt source pc)) := by
  have interval (count start : Nat) (bound : start + count ≤ source.states)
      (code : List (Instruction source.registers source.states)) :
      scanTests count start bound code =
        (List.finRange count).flatMap (fun offset =>
          let pc : Fin source.states := ⟨start + offset.val, by omega⟩
          partitionTests source.registers pc ++ instructionTests pc (code[offset.val]?.getD .halt)) := by
    induction count generalizing start code with
    | zero => simp only [scanTests, List.finRange_zero, List.flatMap_nil]
    | succ count ih =>
      have headEq : code.head? = code[0]? := by cases code <;> rfl
      simp only [scanTests, List.finRange_succ, List.flatMap_cons, List.flatMap_map,
        Fin.val_zero, Nat.add_zero, headEq, Fin.val_succ]
      rw [ih]
      congr 1
      apply congrArg (fun mapping => (List.finRange count).flatMap mapping)
      funext offset
      have same : (⟨start + 1 + offset.val, by omega⟩ : Fin source.states) =
          ⟨start + (offset.val + 1), by omega⟩ := by
        apply Fin.ext
        change start + 1 + offset.val = start + (offset.val + 1)
        omega
      rw [same, List.getElem?_tail]
  rw [interval]
  simp only [Nat.zero_add, instructionAt]

def scanAll (mode : Mode) : Routine 16 :=
  append (clear 13) (append (copy 8 14 5) (scan mode))

theorem scanAll_runs (source : Program) (mode : Mode) (values : Values) (prior : Word)
    (cursor : values 0 = wordCode (list instruction source.code)) (encoded : values 1 = wordCode prior)
    (registersEq : environment values registersField = source.registers)
    (statesEq : environment values statesField = source.states) :
    ∃ finalValues, Runs (scanAll mode) values finalValues ∧
      finalValues 1 = wordCode ((stream mode ((List.finRange source.states).flatMap
        (fun pc => partitionTests source.registers pc ++ instructionTests pc (instructionAt source pc)))).reverse ++ prior) ∧
      ∀ field, HeaderField field → environment finalValues field = environment values field := by
  let cleared := write values 13 0
  let ready := write (write cleared 14 (values 8)) 5 0
  have clearing := clear_runs (13 : Register) values
  have copying := copy_runs (8 : Register) 14 5 (by decide) (by decide) (by decide) cleared
  have readyCursor : ready 0 = wordCode (list instruction source.code) := cursor
  have readyWord : ready 1 = wordCode prior := encoded
  have readyRegisters : environment ready registersField = source.registers := registersEq
  have readyStates : environment ready statesField = source.states := statesEq
  have readyPc : ready 13 = 0 := rfl
  have readyFuel : ready 14 = source.states := statesEq
  obtain ⟨finalValues, scanning, word, _, _, _, frame⟩ := scan_runs source.states 0 (by omega)
    source.code mode ready prior readyCursor readyWord readyRegisters readyStates readyPc readyFuel
  rw [scanTests_exact] at word
  refine ⟨finalValues, append_runs clearing (append_runs copying scanning), word, ?_⟩
  intro field kept
  have preserved : environment ready field = environment values field := by
    have alternatives : field = 1 ∨ field = 2 ∨ field = 3 ∨ field = 4 := by
      obtain ⟨positive, small⟩ := kept
      omega
    rcases alternatives with rfl | rfl | rfl | rfl <;> rfl
  exact (frame field kept).trans preserved

end Yulang.CommonCanonicalReductionMachine
