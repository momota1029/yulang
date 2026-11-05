import Yulang.CyclicRows
import Yulang.SegmentDecisions

/-!
# Inclusion and equality of computed guarded-cycle least rows

The comparison input is two actual `SeededCycle` problems. Their computed
solutions may be empty, finite prefixes, singleton constant rays, or infinite
rays. The decision theorems refer to the existing `RecursiveRows.Derives`
relations of those finite problems, not just to separately supplied segments.

The finite-prefix comparison inherits `SegmentDecisions`' enumeration through
the actual endpoint. No unfolding limit is added. Arbitrary branching or
mutually recursive graphs remain outside this decision procedure.
-/

namespace Yulang.CyclicRowDecisions

open Directed
open CyclicRows (SeededCycle)
open SymbolicRows (Segment)

variable {n : Nat} {Key : Type}

def solutionMeaning : Option (Segment n Key) → RecursiveRows.SetRow n Key
  | none => fun _ => False
  | some segment => segment.Holds

def SolutionSubset (source target : Option (Segment n Key)) : Prop :=
  ∀ occurrence, solutionMeaning source occurrence → solutionMeaning target occurrence

theorem segment_contains_base (segment : Segment n Key) : segment.Holds segment.ray.base := by
  refine ⟨0, ?_, segment.ray.point_zero⟩
  cases segment.upper <;> simp [SymbolicRows.Allows]

def checkSolutionSubset [DecidableEq Key] : Option (Segment n Key) → Option (Segment n Key) → Bool
  | none, _ => true
  | some _, none => false
  | some source, some target => SegmentDecisions.checkSubset source target

theorem checkSolutionSubset_exact [DecidableEq Key]
    (source target : Option (Segment n Key)) :
    checkSolutionSubset source target = true ↔ SolutionSubset source target := by
  cases source with
  | none => simp [checkSolutionSubset, SolutionSubset, solutionMeaning]
  | some source =>
      cases target with
      | none =>
          constructor
          · intro impossible
            cases impossible
          · intro included
            exact False.elim (included source.ray.base (segment_contains_base source))
      | some target => exact SegmentDecisions.checkSubset_exact source target

def Included [DecidableEq Key] (source target : SeededCycle n Key) : Prop :=
  ∀ occurrence, RecursiveRows.Derives source.problem () occurrence →
    RecursiveRows.Derives target.problem () occurrence

def checkSubset [DecidableEq Key] (source target : SeededCycle n Key) : Bool :=
  checkSolutionSubset source.solve target.solve

theorem solutionMeaning_exact [DecidableEq Key] (source : SeededCycle n Key)
    (occurrence : Occurrence n Key) :
    solutionMeaning source.solve occurrence ↔ RecursiveRows.Derives source.problem () occurrence := by
  have same : solutionMeaning source.solve occurrence ↔ source.Holds occurrence := by
    unfold SeededCycle.Holds
    cases source.solve <;> rfl
  exact same.trans (source.solve_exact occurrence)

theorem checkSubset_exact [DecidableEq Key] (source target : SeededCycle n Key) :
    checkSubset source target = true ↔ Included source target := by
  rw [checkSubset, checkSolutionSubset_exact]
  constructor
  · intro included occurrence member
    exact (solutionMeaning_exact target occurrence).mp
      (included occurrence ((solutionMeaning_exact source occurrence).mpr member))
  · intro included occurrence member
    exact (solutionMeaning_exact target occurrence).mpr
      (included occurrence ((solutionMeaning_exact source occurrence).mp member))

theorem checkSubset_rejects [DecidableEq Key] (source target : SeededCycle n Key) :
    checkSubset source target = false ↔ ¬ Included source target := by
  constructor
  · intro rejected included
    have accepted := (checkSubset_exact source target).mpr included
    rw [rejected] at accepted
    cases accepted
  · intro missing
    cases answer : checkSubset source target with
    | false => rfl
    | true => exact False.elim (missing ((checkSubset_exact source target).mp answer))

def checkEqual [DecidableEq Key] (left right : SeededCycle n Key) : Bool :=
  checkSubset left right && checkSubset right left

theorem checkEqual_exact [DecidableEq Key] (left right : SeededCycle n Key) :
    checkEqual left right = true ↔ ∀ occurrence,
      RecursiveRows.Derives left.problem () occurrence ↔
        RecursiveRows.Derives right.problem () occurrence := by
  simp only [checkEqual, Bool.and_eq_true, checkSubset_exact]
  exact ⟨fun ⟨lr, rl⟩ occurrence => ⟨lr occurrence, rl occurrence⟩,
    fun same => ⟨fun occurrence => (same occurrence).mp, fun occurrence => (same occurrence).mpr⟩⟩

theorem checkEqual_set_exact [DecidableEq Key] (left right : SeededCycle n Key) :
    checkEqual left right = true ↔
      RecursiveRows.Derives left.problem () = RecursiveRows.Derives right.problem () := by
  rw [checkEqual_exact]
  exact ⟨fun same => funext (fun occurrence => propext (same occurrence)),
    fun same occurrence => by rw [same]⟩

namespace Examples

open CyclicRows.Examples

def plainAscending : SeededCycle 1 Nat := ⟨0, [], [.protect 0 allowNone]⟩
def descendingPrefix : SeededCycle 1 Nat :=
  ⟨0, [.protect 0 allowNone], [.residual [0], .release 0 allowNone]⟩

theorem unused_guard_preserves_least_row : checkEqual ascending plainAscending = true := by decide
theorem stopped_cycle_below_infinite_cycle : checkSubset interrupted ascending = true := by decide
theorem infinite_cycle_not_below_stopped_cycle : checkSubset ascending interrupted = false := by decide
theorem different_cycles_same_prefix : checkEqual interrupted descendingPrefix = true := by decide
theorem empty_seed_below_every_row : checkSubset rejectedSeed ascending = true := by decide
theorem nonempty_cycle_not_below_empty : checkSubset constant rejectedSeed = false := by decide
theorem zero_displacement_and_blocked_cycle_equal : checkEqual constant initiallyBlocked = true := by decide
theorem opposite_infinite_directions_differ : checkEqual ascending descending = false := by decide

theorem stopped_problem_not_equal_infinite_problem :
    RecursiveRows.Derives interrupted.problem () ≠ RecursiveRows.Derives ascending.problem () := by
  intro equal
  have included : Included ascending interrupted := by
    intro occurrence member
    rw [equal]
    exact member
  exact (checkSubset_rejects ascending interrupted).mp infinite_cycle_not_below_stopped_cycle included

end Examples

end Yulang.CyclicRowDecisions
