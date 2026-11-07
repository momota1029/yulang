import Yulang.CanonicalRegisterGuard
namespace Yulang.CanonicalRegisterRecognizer
open Yulang.CanonicalRegisterMachine
open Yulang.CanonicalRegisterMachine.Routine
open Yulang.CanonicalRegisterGuard

def invoke (source : Program)
    (registerMap : Fin (source.registers + 1) → Fin (registers + 1)) : Routine registers :=
  append (clearList (List.ofFn (fun index : Fin source.registers => registerMap index.succ)))
    (call source registerMap)

theorem invoke_runs (source : Program)
    (registerMap : Fin (source.registers + 1) → Fin (registers + 1))
    (injective : Function.Injective registerMap) (input output : Nat)
    (execution : Yulang.CanonicalRegisterMachine.Runs source input output)
    (values : Store registers) (inputValue : values (registerMap 0) = input) :
    ∃ finalValues, Routine.Runs (invoke source registerMap) values finalValues ∧
      finalValues (registerMap 0) = output ∧
      ∀ register, (∀ original, register ≠ registerMap original) →
        finalValues register = values register := by
  let targets := List.ofFn (fun index : Fin source.registers => registerMap index.succ)
  let cleared : Store registers := fun register => if register ∈ targets then 0 else values register
  have clearing : Routine.Runs (clearList targets) values cleared := clearList_runs targets values
  have succNonzero (index : Fin source.registers) : index.succ ≠ 0 := by
    intro same
    have impossible := congrArg Fin.val same
    change index.val + 1 = 0 at impossible
    omega
  have agrees : ∀ register, cleared (registerMap register) = (initial source input).values register := by
    intro register
    refine Fin.cases ?_ (fun index => ?_) register
    · simp [cleared, targets, List.mem_ofFn, injective.eq_iff, initial, inputValue, succNonzero]
    · simp [cleared, targets, List.mem_ofFn, injective.eq_iff, initial, succNonzero]
  obtain ⟨finalValues, run, result, frame⟩ := call_trace registerMap injective execution cleared agrees
  refine ⟨finalValues, append_runs clearing run, result, ?_⟩
  intro register outside
  rw [frame register outside]
  have absent : register ∉ targets := by
    intro member
    obtain ⟨index, equality⟩ := List.mem_ofFn.mp member
    exact outside index.succ equality.symm
  simp only [cleared, absent, ↓reduceIte]

def global (capacity : Nat) (index : Fin 5) : Fin (capacity + 5 + 1) :=
  ⟨index.val, by omega⟩

def work (capacity : Nat) : Fin (capacity + 5 + 1) := ⟨5, by omega⟩

def bank (capacity : Nat) (source : Program) (bound : source.registers ≤ capacity)
    (register : Fin (source.registers + 1)) : Fin (capacity + 5 + 1) :=
  ⟨register.val + 5, by omega⟩

theorem global_injective (capacity : Nat) : Function.Injective (global capacity) := by
  intro first last same
  apply Fin.ext
  have values := congrArg (fun index : Fin (capacity + 5 + 1) => index.val) same
  exact values

theorem bank_injective (capacity : Nat) (source : Program) (bound : source.registers ≤ capacity) :
    Function.Injective (bank capacity source bound) := by
  intro first last same
  apply Fin.ext
  have values := congrArg Fin.val same
  change first.val + 5 = last.val + 5 at values
  omega

theorem bank_zero (capacity : Nat) (source : Program) (bound : source.registers ≤ capacity) :
    bank capacity source bound 0 = work capacity := rfl

theorem global_outside (capacity : Nat) (source : Program) (bound : source.registers ≤ capacity)
    (index : Fin 5) (register : Fin (source.registers + 1)) :
    global capacity index ≠ bank capacity source bound register := by
  intro same
  have values := congrArg Fin.val same
  change index.val = register.val + 5 at values
  omega

theorem global_work_ne (capacity : Nat) (index : Fin 5) :
    global capacity index ≠ work capacity := by
  intro same
  have values := congrArg Fin.val same
  change index.val = 5 at values
  omega

def evaluate (capacity : Nat) (builder coder : Program)
    (builderBound : builder.registers ≤ capacity) (coderBound : coder.registers ≤ capacity)
    (destination : Fin 5) : Routine (capacity + 5) :=
  append (copy (global capacity 0) (work capacity) (global capacity 4))
    (append (invoke builder (bank capacity builder builderBound))
      (append (invoke coder (bank capacity coder coderBound))
        (copy (work capacity) (global capacity destination) (global capacity 4))))

theorem evaluate_runs (capacity : Nat) (builder coder : Program)
    (builderBound : builder.registers ≤ capacity) (coderBound : coder.registers ≤ capacity)
    (destination : Fin 5) (notTemporary : destination ≠ 4)
    (input intermediate output : Nat)
    (buildRun : Yulang.CanonicalRegisterMachine.Runs builder input intermediate)
    (codeRun : Yulang.CanonicalRegisterMachine.Runs coder intermediate output)
    (values : Store (capacity + 5)) (initialValue : values (global capacity 0) = input) :
    ∃ finalValues, Routine.Runs (evaluate capacity builder coder builderBound coderBound destination)
        values finalValues ∧
      finalValues (global capacity destination) = output ∧
      ∀ index : Fin 5, index ≠ destination → index ≠ 4 →
        finalValues (global capacity index) = values (global capacity index) := by
  have globalNe {first last : Fin 5} (different : first ≠ last) :
      global capacity first ≠ global capacity last := fun same => different (global_injective capacity same)
  let entered := write (write values (work capacity) (values (global capacity 0))) (global capacity 4) 0
  have enter := copy_runs (global capacity 0) (work capacity) (global capacity 4)
    (global_work_ne capacity 0) (globalNe (by decide)) (Ne.symm (global_work_ne capacity 4)) values
  have enteredInput : entered (bank capacity builder builderBound 0) = input := by
    simp only [bank_zero, entered, write, Ne.symm (global_work_ne capacity 4), ↓reduceIte, initialValue]
  obtain ⟨built, builtRun, builtOutput, builtFrame⟩ :=
    invoke_runs builder (bank capacity builder builderBound) (bank_injective capacity builder builderBound)
      input intermediate buildRun entered enteredInput
  have coderInput : built (bank capacity coder coderBound 0) = intermediate := by
    simpa only [bank_zero] using builtOutput
  obtain ⟨coded, codedRun, codedOutput, codedFrame⟩ :=
    invoke_runs coder (bank capacity coder coderBound) (bank_injective capacity coder coderBound)
      intermediate output codeRun built coderInput
  have outputValue : coded (work capacity) = output := by
    simpa only [bank_zero] using codedOutput
  let finalValues := write (write coded (global capacity destination) output) (global capacity 4) 0
  have leave := copy_runs (work capacity) (global capacity destination) (global capacity 4)
    (Ne.symm (global_work_ne capacity destination)) (Ne.symm (global_work_ne capacity 4))
    (globalNe notTemporary) coded
  rw [outputValue] at leave
  refine ⟨finalValues, append_runs enter (append_runs builtRun (append_runs codedRun leave)), ?_, ?_⟩
  · simp only [finalValues, write, globalNe notTemporary, ↓reduceIte]
  · intro index different temporary
    have fromCode := codedFrame (global capacity index) (global_outside capacity coder coderBound index)
    have fromBuild := builtFrame (global capacity index) (global_outside capacity builder builderBound index)
    simp only [finalValues, entered, write, globalNe different, globalNe temporary,
      global_work_ne capacity index, ↓reduceIte] at *
    exact fromCode.trans fromBuild

def capacity (first last coder : Program) : Nat :=
  max first.registers (max last.registers coder.registers)

theorem first_bound (first last coder : Program) : first.registers ≤ capacity first last coder :=
  Nat.le_max_left _ _

theorem last_bound (first last coder : Program) : last.registers ≤ capacity first last coder :=
  Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)

theorem coder_bound (first last coder : Program) : coder.registers ≤ capacity first last coder :=
  Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)

def preparation (first last coder : Program) : Routine (capacity first last coder + 5) :=
  append (evaluate (capacity first last coder) first coder (first_bound first last coder) (coder_bound first last coder) 1)
    (append (evaluate (capacity first last coder) last coder (last_bound first last coder) (coder_bound first last coder) 2)
      (compareCounters (global (capacity first last coder) 1)
        (global (capacity first last coder) 2) (global (capacity first last coder) 3)))

theorem preparation_runs (first last coder : Program) (input before after firstCode lastCode : Nat)
    (firstRun : Yulang.CanonicalRegisterMachine.Runs first input before)
    (lastRun : Yulang.CanonicalRegisterMachine.Runs last input after)
    (firstCodeRun : Yulang.CanonicalRegisterMachine.Runs coder before firstCode)
    (lastCodeRun : Yulang.CanonicalRegisterMachine.Runs coder after lastCode)
    (values : Store (capacity first last coder + 5))
    (inputValue : values (global (capacity first last coder) 0) = input) :
    ∃ finalValues, Routine.Runs (preparation first last coder) values finalValues ∧
      finalValues (global (capacity first last coder) 3) = if firstCode = lastCode then 0 else 1 := by
  let size := capacity first last coder
  obtain ⟨firstValues, runFirst, firstResult, firstFrame⟩ :=
    evaluate_runs size first coder (first_bound first last coder) (coder_bound first last coder) 1
      (by decide) input before firstCode firstRun firstCodeRun values inputValue
  have inputAgain : firstValues (global size 0) = input :=
    (firstFrame 0 (by decide) (by decide)).trans inputValue
  obtain ⟨lastValues, runLast, lastResult, lastFrame⟩ :=
    evaluate_runs size last coder (last_bound first last coder) (coder_bound first last coder) 2
      (by decide) input after lastCode lastRun lastCodeRun firstValues inputAgain
  have firstRetained : lastValues (global size 1) = firstCode :=
    (lastFrame 1 (by decide) (by decide)).trans firstResult
  have globalNe {a b : Fin 5} (different : a ≠ b) : global size a ≠ global size b :=
    fun same => different (global_injective size same)
  have compare := compareCounters_runs (global size 1) (global size 2) (global size 3)
    (globalNe (by decide)) (globalNe (by decide)) (globalNe (by decide)) lastValues
  rw [firstRetained, lastResult] at compare
  refine ⟨_, append_runs runFirst (append_runs runLast compare), ?_⟩
  simp only [size, write, ↓reduceIte]

def recognizer (first last coder : Program) : Program :=
  (append (preparation first last coder) (acceptZero (global (capacity first last coder) 3))).compile

theorem recognizer_exact {Index : Type} (first last coder : Program)
    (encoding before after firstCode lastCode : Index → Nat)
    (firstRun : ∀ index, Yulang.CanonicalRegisterMachine.Runs first (encoding index) (before index))
    (lastRun : ∀ index, Yulang.CanonicalRegisterMachine.Runs last (encoding index) (after index))
    (firstCodeRun : ∀ index, Yulang.CanonicalRegisterMachine.Runs coder (before index) (firstCode index))
    (lastCodeRun : ∀ index, Yulang.CanonicalRegisterMachine.Runs coder (after index) (lastCode index)) :
    ∃ machine : Program, ∀ index,
      Halts machine (encoding index) ↔ firstCode index = lastCode index := by
  refine ⟨recognizer first last coder, ?_⟩
  intro index
  let values := (initial (recognizer first last coder) (encoding index)).values
  have inputValue : values (global (capacity first last coder) 0) = encoding index := by
    rfl
  obtain ⟨finalValues, execution, flag⟩ :=
    preparation_runs first last coder (encoding index) (before index) (after index)
      (firstCode index) (lastCode index) (firstRun index) (lastRun index)
      (firstCodeRun index) (lastCodeRun index) values inputValue
  have guarded := guarded_prefix_halts_iff (global (capacity first last coder) 3) execution
  change Halts (recognizer first last coder) (encoding index) ↔ _ at guarded
  rw [flag] at guarded
  by_cases equal : firstCode index = lastCode index <;> simpa [equal] using guarded

end Yulang.CanonicalRegisterRecognizer
