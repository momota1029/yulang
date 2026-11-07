import Yulang.CanonicalRegisterRoutines

/-! Concrete finite counter routines used by the finite-word compiler. -/

namespace Yulang.CanonicalRegisterMachine.Routine

def skip {registers : Nat} : Routine registers := atomic (.jump ())

def increment {registers : Nat} (register : Fin (registers + 1)) : Routine registers :=
  atomic (.increment register ())

def clear {registers : Nat} (register : Fin (registers + 1)) : Routine registers :=
  loop register skip

theorem clear_runs {registers : Nat} (register : Fin (registers + 1))
    (values : Store registers) : Runs (clear register) values (write values register 0) := by
  apply loop_runs
  generalize valueEquation : values register = count
  induction count generalizing values with
  | zero =>
      have same : write values register 0 = values := by
        funext current
        by_cases equal : current = register
        · subst current
          simp only [write, ↓reduceIte, valueEquation]
        · simp only [write, equal, ↓reduceIte]
      rw [same]
      exact .done valueEquation
  | succ count ih =>
      let lower := write values register count
      have lowerValue : lower register = count := by simp only [lower, write, ↓reduceIte]
      have same : write lower register 0 = write values register 0 := by
        funext current
        by_cases equal : current = register <;> simp [lower, write, equal]
      rw [← same]
      apply LoopRuns.next (by omega) (middleValues := lower) ?_ (ih lower lowerValue)
      have lowerEquation : write values register (values register - 1) = lower := by
        simp only [valueEquation, Nat.add_sub_cancel, lower]
      rw [lowerEquation]
      exact atomic_runs (.jump ()) lower

def incrementList {registers : Nat} : List (Fin (registers + 1)) → Routine registers
  | [] => skip
  | register :: rest => append (increment register) (incrementList rest)

/-- A fixed finite sequence of increments adds the occurrence count of each
register, including repeated occurrences of the same register. -/
theorem incrementList_runs {registers : Nat} (targets : List (Fin (registers + 1)))
    (values : Store registers) :
    Runs (incrementList targets) values (fun register => values register + targets.count register) := by
  induction targets generalizing values with
  | nil =>
      simpa only [List.count_nil, Nat.add_zero, Op.eval, incrementList, skip] using atomic_runs (.jump ()) values
  | cons target rest ih =>
      have combined := append_runs (atomic_runs (.increment target ()) values)
        (ih (write values target (values target + 1)))
      have same : (fun register => write values target (values target + 1) register + rest.count register) =
          (fun register => values register + (target :: rest).count register) := by
        funext register
        by_cases equal : register = target
        · subst register
          simp only [write, ↓reduceIte, List.count_cons_self]
          omega
        · simp [write, equal, Ne.symm equal]
      exact same ▸ combined

def drain {registers : Nat} (source : Fin (registers + 1))
    (targets : List (Fin (registers + 1))) : Routine registers :=
  loop source (incrementList targets)

/-- Transfer all units out of one counter, adding one unit to every listed
target per iteration. Repeated targets implement multiplication by a fixed
constant; distinct targets implement copying through a temporary counter. -/
theorem drain_runs {registers : Nat} (source : Fin (registers + 1))
    (targets : List (Fin (registers + 1))) (sourceAbsent : source ∉ targets)
    (values : Store registers) :
    Runs (drain source targets) values
      (fun register => if register = source then 0
        else values register + targets.count register * values source) := by
  have sourceCount : targets.count source = 0 := List.count_eq_zero.mpr sourceAbsent
  apply loop_runs
  generalize countEquation : values source = count
  induction count generalizing values with
  | zero =>
      have same : (fun register => if register = source then 0
          else values register + targets.count register * 0) = values := by
        funext register
        by_cases equal : register = source
        · subst register
          simp only [↓reduceIte, countEquation]
        · simp only [equal, ↓reduceIte, Nat.mul_zero, Nat.add_zero]
      rw [same]
      exact .done countEquation
  | succ count ih =>
      let lower := write values source count
      let middle : Store registers := fun register => lower register + targets.count register
      have middleSource : middle source = count := by
        simp only [middle, lower, write, ↓reduceIte, sourceCount, Nat.add_zero]
      have bodyRun : Runs (incrementList targets)
          (write values source (values source - 1)) middle := by
        simpa only [countEquation, Nat.add_sub_cancel] using incrementList_runs targets lower
      have rest := ih middle middleSource
      have same : (fun register => if register = source then 0
            else middle register + targets.count register * count) =
          (fun register => if register = source then 0
            else values register + targets.count register * (count + 1)) := by
        funext register
        by_cases equal : register = source
        · simp only [equal, ↓reduceIte]
        · simp only [equal, ↓reduceIte, middle, lower, write, Nat.mul_add, Nat.mul_one]
          omega
      rw [same] at rest
      exact .next (by omega) bodyRun rest

def copy {registers : Nat} (source target temporary : Fin (registers + 1)) : Routine registers :=
  append (clear target) (append (clear temporary)
    (append (drain source [target, temporary]) (drain temporary [source])))

/-- Copy one counter without consuming it. The target is overwritten, the
temporary is cleared, and all other counters retain their original values. -/
theorem copy_runs {registers : Nat} (source target temporary : Fin (registers + 1))
    (sourceTarget : source ≠ target) (sourceTemporary : source ≠ temporary)
    (targetTemporary : target ≠ temporary) (values : Store registers) :
    Runs (copy source target temporary) values
      (write (write values target (values source)) temporary 0) := by
  let first := write values target 0
  let second := write first temporary 0
  let third : Store registers := fun register => if register = source then 0
    else second register + [target, temporary].count register * second source
  let fourth : Store registers := fun register => if register = temporary then 0
    else third register + [source].count register * third temporary
  have firstRun := clear_runs target values
  have secondRun := clear_runs temporary first
  have thirdRun := drain_runs source [target, temporary]
    (by simp [sourceTarget, sourceTemporary]) second
  have fourthRun := drain_runs temporary [source]
    (by simpa only [List.mem_singleton] using Ne.symm sourceTemporary) third
  have combined : Runs (copy source target temporary) values fourth :=
    append_runs firstRun (append_runs secondRun (append_runs thirdRun fourthRun))
  have same : fourth = write (write values target (values source)) temporary 0 := by
    funext register
    by_cases atSource : register = source
    · subst register
      simp [fourth, third, second, first, write, sourceTarget, sourceTemporary,
        Ne.symm sourceTemporary, targetTemporary]
    · by_cases atTarget : register = target
      · subst register
        simp [fourth, third, second, first, write, sourceTarget, sourceTemporary,
          Ne.symm sourceTarget, targetTemporary, Ne.symm targetTemporary]
      · by_cases atTemporary : register = temporary
        · subst register
          simp [fourth, write]
        · simp [fourth, third, second, first, write, atSource, atTarget, atTemporary,
            Ne.symm atSource, Ne.symm atTarget, Ne.symm atTemporary]
  exact same ▸ combined

def pushDigit {registers : Nat} (base digit : Nat)
    (word temporary : Fin (registers + 1)) : Routine registers :=
  append (clear temporary)
    (append (drain word (List.replicate base temporary))
      (append (drain temporary [word]) (incrementList (List.replicate digit word))))

/-- Multiplication by a fixed alphabet base and addition of a fixed token
digit are implemented by a concrete finite counter routine. -/
theorem pushDigit_runs {registers : Nat} (base digit : Nat)
    (word temporary : Fin (registers + 1)) (distinct : word ≠ temporary)
    (values : Store registers) :
    Runs (pushDigit base digit word temporary) values
      (write (write values word (base * values word + digit)) temporary 0) := by
  let first := write values temporary 0
  let second : Store registers := fun register => if register = word then 0
    else first register + (List.replicate base temporary).count register * first word
  let third : Store registers := fun register => if register = temporary then 0
    else second register + [word].count register * second temporary
  let fourth : Store registers := fun register => third register + (List.replicate digit word).count register
  have firstRun := clear_runs temporary values
  have secondRun := drain_runs word (List.replicate base temporary)
    (by simp [distinct]) first
  have thirdRun := drain_runs temporary [word]
    (by simpa only [List.mem_singleton] using Ne.symm distinct) second
  have fourthRun := incrementList_runs (List.replicate digit word) third
  have combined : Runs (pushDigit base digit word temporary) values fourth :=
    append_runs firstRun (append_runs secondRun (append_runs thirdRun fourthRun))
  have same : fourth = write (write values word (base * values word + digit)) temporary 0 := by
    funext register
    by_cases atWord : register = word
    · subst register
      simp [fourth, third, second, first, write, distinct, Ne.symm distinct]
    · by_cases atTemporary : register = temporary
      · subst register
        simp [fourth, third, write, List.count_replicate, distinct]
      · simp [fourth, third, second, first, write, List.count_replicate,
          atWord, atTemporary, Ne.symm atWord, Ne.symm atTemporary]
  exact same ▸ combined

def setConstant {registers : Nat} (register : Fin (registers + 1)) (value : Nat) : Routine registers :=
  append (clear register) (incrementList (List.replicate value register))

theorem setConstant_runs {registers : Nat} (register : Fin (registers + 1))
    (value : Nat) (values : Store registers) :
    Runs (setConstant register value) values (write values register value) := by
  have execution := append_runs (clear_runs register values)
    (incrementList_runs (List.replicate value register) (write values register 0))
  have same : (fun current => write values register 0 current +
        (List.replicate value register).count current) = write values register value := by
    funext current
    by_cases equal : current = register
    · subst current
      simp only [write, ↓reduceIte, List.count_replicate_self, Nat.zero_add]
    · simp [write, equal, Ne.symm equal, List.count_replicate]
  exact same ▸ execution

end Yulang.CanonicalRegisterMachine.Routine
