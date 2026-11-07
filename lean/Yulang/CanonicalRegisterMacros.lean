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

end Yulang.CanonicalRegisterMachine.Routine
