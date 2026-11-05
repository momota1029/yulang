import Yulang.SymbolicRows
import Yulang.FinitePointGuards

/-!
# Exact least rows for one guarded transport cycle

A finite transport program preserves operation keys. For one seed, its repeated
successful executions therefore follow an integer affine ray. Intermediate
residuals can stop that ray: the first excluded input remains reachable, while
the next execution from it is blocked.

The solver computes that first obstruction from finitely many arithmetic
candidates. It handles arbitrary finite boundary dimension, signed periods,
and constant cycles. No unfolding bound or finite-support assumption is used.
The result concerns one repeated program; arbitrary branching recursive row
graphs are outside this module's decision theorem.
-/

namespace Yulang.CyclicRows

open Directed
open AffineRows (Ray)
open RecursiveRowGraph (Program)
open RowTransportNormalForm (NormalForm normalize translate)

variable {n : Nat} {Key : Type}

structure Cycle (n : Nat) (Key : Type) where
  seed : Occurrence n Key
  body : Program n Key

def Cycle.normal [DecidableEq Key] (cycle : Cycle n Key) : NormalForm n Key :=
  normalize cycle.seed.key cycle.body

def Cycle.ray [DecidableEq Key] (cycle : Cycle n Key) : Ray n Key :=
  ⟨cycle.seed, cycle.normal.displacement⟩

/-- A cycle's independent finite-execution semantics. -/
inductive Cycle.Reachable [DecidableEq Key] (cycle : Cycle n Key) : Occurrence n Key → Prop where
  | seed : cycle.Reachable cycle.seed
  | step : cycle.Reachable input → Program.run cycle.body input = some output →
      cycle.Reachable output

def Cycle.Safe [DecidableEq Key] (cycle : Cycle n Key) (count : Nat) : Prop :=
  ∀ earlier, earlier < count → cycle.ray.point earlier ∉ cycle.normal.excluded

theorem Cycle.point_succ [DecidableEq Key] (cycle : Cycle n Key) (count : Nat) :
    translate cycle.normal.displacement (cycle.ray.point count) = cycle.ray.point (count + 1) := by
  apply Occurrence.ext
  · rfl
  intro coordinate
  simp only [translate, Ray.point, Cycle.ray, Int.natCast_add, Int.ofNat_one,
    Int.add_mul, Int.one_mul]
  omega

theorem Cycle.run_point [DecidableEq Key] (cycle : Cycle n Key)
    (count : Nat) (output : Occurrence n Key) :
    Program.run cycle.body (cycle.ray.point count) = some output ↔
      cycle.ray.point count ∉ cycle.normal.excluded ∧ output = cycle.ray.point (count + 1) := by
  rw [RowTransportNormalForm.execution_normal_form cycle.seed.key cycle.body
    (cycle.ray.point count) output rfl]
  change (_ ∧ output = translate cycle.normal.displacement (cycle.ray.point count)) ↔
    _ ∧ output = _
  rw [cycle.point_succ]
  rfl

theorem Cycle.safe_zero [DecidableEq Key] (cycle : Cycle n Key) : cycle.Safe 0 := by
  intro earlier bound
  omega

theorem Cycle.safe_downward [DecidableEq Key] (cycle : Cycle n Key)
    {first last : Nat} (safe : cycle.Safe last) (bound : first ≤ last) : cycle.Safe first := by
  intro earlier before
  exact safe earlier (by omega)

theorem Cycle.safe_succ [DecidableEq Key] (cycle : Cycle n Key) (count : Nat) :
    cycle.Safe (count + 1) ↔
      cycle.Safe count ∧ cycle.ray.point count ∉ cycle.normal.excluded := by
  constructor
  · intro safe
    exact ⟨cycle.safe_downward safe (by omega), safe count (by omega)⟩
  · rintro ⟨safe, last⟩ earlier before
    by_cases same : earlier = count
    · exact same ▸ last
    · exact safe earlier (by omega)

theorem Cycle.reachable_iff_safe [DecidableEq Key] (cycle : Cycle n Key)
    (output : Occurrence n Key) :
    cycle.Reachable output ↔ ∃ count, cycle.Safe count ∧ cycle.ray.point count = output := by
  constructor
  · intro reached
    induction reached with
    | seed => exact ⟨0, cycle.safe_zero, cycle.ray.point_zero⟩
    | step _ execution ih =>
        obtain ⟨count, safe, rfl⟩ := ih
        obtain ⟨allowed, rfl⟩ := (cycle.run_point count _).mp execution
        exact ⟨count + 1, (cycle.safe_succ count).mpr ⟨safe, allowed⟩, rfl⟩
  · rintro ⟨count, safe, rfl⟩
    induction count with
    | zero => simpa only [Ray.point_zero, Cycle.ray] using Cycle.Reachable.seed (cycle := cycle)
    | succ count ih =>
        obtain ⟨earlier, allowed⟩ := (cycle.safe_succ count).mp safe
        exact .step (ih earlier) ((cycle.run_point count _).mpr ⟨allowed, rfl⟩)

/-- Candidate indices for all excluded input occurrences. The list is finite
even when the ray has infinite support. Equal candidates need not be removed. -/
def Cycle.hitCandidates [DecidableEq Key] (cycle : Cycle n Key) : List Nat :=
  cycle.normal.excluded.flatMap fun excluded =>
    (cycle.ray.candidates excluded).filter (fun count => decide (cycle.ray.point count = excluded))

theorem Cycle.hit_candidate_blocked [DecidableEq Key] (cycle : Cycle n Key)
    {count : Nat} (member : count ∈ cycle.hitCandidates) :
    cycle.ray.point count ∈ cycle.normal.excluded := by
  obtain ⟨excluded, declared, candidate⟩ := List.mem_flatMap.mp member
  have same : cycle.ray.point count = excluded := by
    simpa using (List.mem_filter.mp candidate).2
  exact same ▸ declared

/-- Every blocked point has a candidate no later than its given index. For a
constant ray this chooses zero, which is the only relevant first obstruction. -/
theorem Cycle.blocked_has_candidate [DecidableEq Key] (cycle : Cycle n Key)
    {count : Nat} (blocked : cycle.ray.point count ∈ cycle.normal.excluded) :
    ∃ candidate ∈ cycle.hitCandidates, candidate ≤ count := by
  obtain ⟨candidate, inCandidates, same, bound⟩ := cycle.ray.bounded_candidate count
  refine ⟨candidate, List.mem_flatMap.mpr ⟨cycle.ray.point count, blocked, ?_⟩, bound⟩
  exact List.mem_filter.mpr ⟨inCandidates, by simpa using same⟩

theorem Cycle.safe_iff_candidates [DecidableEq Key] (cycle : Cycle n Key) (count : Nat) :
    cycle.Safe count ↔ ∀ candidate ∈ cycle.hitCandidates, count ≤ candidate := by
  constructor
  · intro safe candidate member
    have blocked := cycle.hit_candidate_blocked member
    apply Classical.byContradiction
    intro before
    exact safe candidate (by omega) blocked
  · intro bounds earlier before blocked
    obtain ⟨candidate, member, bound⟩ := cycle.blocked_has_candidate blocked
    have lower := bounds candidate member
    omega

/-- `none` means that the whole ray is reachable; `some h` retains exactly
indices through `h`, including the input at which the next cycle would fail. -/
def Cycle.firstHit [DecidableEq Key] (cycle : Cycle n Key) : Option Nat :=
  cycle.hitCandidates.min?

theorem Cycle.allows_exact [DecidableEq Key] (cycle : Cycle n Key) (count : Nat) :
    SymbolicRows.Allows cycle.firstHit count ↔ cycle.Safe count := by
  rw [cycle.safe_iff_candidates]
  unfold Cycle.firstHit
  cases minimum : cycle.hitCandidates.min? with
  | none =>
      have empty := List.min?_eq_none_iff.mp minimum
      simp [SymbolicRows.Allows, empty]
  | some last =>
      obtain ⟨member, lower⟩ := List.min?_eq_some_iff.mp minimum
      change count ≤ last ↔ _
      exact ⟨fun bound candidate present => Nat.le_trans bound (lower candidate present),
        fun all => all last member⟩

theorem Cycle.firstHit_exact [DecidableEq Key] (cycle : Cycle n Key) (last : Nat) :
    cycle.firstHit = some last ↔
      cycle.ray.point last ∈ cycle.normal.excluded ∧ cycle.Safe last := by
  constructor
  · intro hit
    obtain ⟨member, lower⟩ := List.min?_eq_some_iff.mp hit
    exact ⟨cycle.hit_candidate_blocked member, (cycle.safe_iff_candidates last).mpr lower⟩
  · rintro ⟨blocked, safe⟩
    obtain ⟨candidate, member, bound⟩ := cycle.blocked_has_candidate blocked
    have lower := (cycle.safe_iff_candidates last).mp safe
    have same : candidate = last := by have := lower candidate member; omega
    apply List.min?_eq_some_iff.mpr
    exact ⟨same ▸ member, lower⟩

theorem Cycle.no_hit_exact [DecidableEq Key] (cycle : Cycle n Key) :
    cycle.firstHit = none ↔
      ∀ count, cycle.ray.point count ∉ cycle.normal.excluded := by
  constructor
  · intro unblocked count blocked
    have empty := List.min?_eq_none_iff.mp unblocked
    obtain ⟨candidate, member, _⟩ := cycle.blocked_has_candidate blocked
    simp [empty] at member
  · intro unblocked
    cases hit : cycle.firstHit with
    | none => rfl
    | some last => exact False.elim (unblocked last ((cycle.firstHit_exact last).mp hit).1)

def Cycle.solution [DecidableEq Key] (cycle : Cycle n Key) : SymbolicRows.Segment n Key :=
  ⟨cycle.ray, cycle.firstHit⟩

def Cycle.Holds [DecidableEq Key] (cycle : Cycle n Key) : RecursiveRows.SetRow n Key :=
  cycle.solution.Holds

theorem Cycle.holds_exact [DecidableEq Key] (cycle : Cycle n Key) (output : Occurrence n Key) :
    cycle.Holds output ↔ cycle.Reachable output := by
  rw [cycle.reachable_iff_safe]
  exact exists_congr (fun count => and_congr (cycle.allows_exact count) Iff.rfl)

theorem Cycle.full_ray [DecidableEq Key] (cycle : Cycle n Key) (unblocked : cycle.firstHit = none)
    (output : Occurrence n Key) : cycle.Holds output ↔ cycle.ray.Holds output := by
  simp [Cycle.Holds, Cycle.solution, SymbolicRows.Segment.Holds, SymbolicRows.Allows,
    unblocked, Ray.Holds]

theorem Cycle.inclusive_prefix [DecidableEq Key] (cycle : Cycle n Key) (last : Nat)
    (blocked : cycle.firstHit = some last) (output : Occurrence n Key) :
    cycle.Holds output ↔ ∃ count, count ≤ last ∧ cycle.ray.point count = output := by
  simp [Cycle.Holds, Cycle.solution, SymbolicRows.Segment.Holds, SymbolicRows.Allows, blocked]

/-- Once the segment is computed, membership uses at most one candidate per
boundary coordinate and zero. Segment construction separately checks the finite
candidate list for every excluded input. Neither phase unfolds the cycle up to
the obstruction or the queried weight. -/
def Cycle.check [DecidableEq Key] (cycle : Cycle n Key) (output : Occurrence n Key) : Bool :=
  cycle.solution.check output

theorem Cycle.check_holds [DecidableEq Key] (cycle : Cycle n Key) (output : Occurrence n Key) :
    cycle.check output = true ↔ cycle.Holds output :=
  cycle.solution.check_exact output

theorem Cycle.check_exact [DecidableEq Key] (cycle : Cycle n Key) (output : Occurrence n Key) :
    cycle.check output = true ↔ cycle.Reachable output :=
  (cycle.check_holds output).trans (cycle.holds_exact output)

/-- A finite seed program followed by one repeated program. A rejected seed
program gives the empty least row, rather than an invented initial occurrence. -/
structure SeededCycle (n : Nat) (Key : Type) where
  key : Key
  initial : Program n Key
  body : Program n Key

def SeededCycle.seedRule (source : SeededCycle n Key) : RecursiveRows.Rule n Key Unit :=
  ⟨(), FinitePointGuards.wrap source.initial (.head source.key)⟩

def SeededCycle.cycleRule (source : SeededCycle n Key) : RecursiveRows.Rule n Key Unit :=
  ⟨(), FinitePointGuards.wrap source.body (.var ())⟩

/-- The original positive lower-rule syntax, with no new row constructor. -/
def SeededCycle.problem (source : SeededCycle n Key) : RecursiveRows.Problem n Key Unit :=
  [source.seedRule, source.cycleRule]

def SeededCycle.Reachable [DecidableEq Key] (source : SeededCycle n Key) :
    RecursiveRows.SetRow n Key :=
  fun output => ∃ seed, Program.run source.initial (raw source.key) = some seed ∧
    (Cycle.mk seed source.body).Reachable output

theorem SeededCycle.reachable_models [DecidableEq Key] (source : SeededCycle n Key) :
    RecursiveRows.Models source.problem (fun _ => source.Reachable) := by
  intro rule declared output member
  simp only [SeededCycle.problem, List.mem_cons, List.not_mem_nil, or_false] at declared
  rcases declared with rfl | rfl
  · obtain ⟨input, isHead, execution⟩ :=
      (FinitePointGuards.eval_wrap source.initial (.head source.key) _ output).mp member
    change input = raw source.key at isHead
    cases isHead
    exact ⟨output, execution, .seed⟩
  · obtain ⟨input, reached, execution⟩ :=
      (FinitePointGuards.eval_wrap source.body (.var ()) _ output).mp member
    obtain ⟨seed, initial, reached⟩ := reached
    exact ⟨seed, initial, .step reached execution⟩

theorem SeededCycle.derives_seed [DecidableEq Key] (source : SeededCycle n Key)
    (seed : Occurrence n Key) (execution : Program.run source.initial (raw source.key) = some seed) :
    RecursiveRows.Derives source.problem () seed := by
  apply RecursiveRows.least_models source.problem source.seedRule (by simp [SeededCycle.problem]) seed
  exact (FinitePointGuards.eval_wrap source.initial (.head source.key) _ seed).mpr
    ⟨raw source.key, rfl, execution⟩

theorem SeededCycle.derives_step [DecidableEq Key] (source : SeededCycle n Key)
    (input output : Occurrence n Key) (reached : RecursiveRows.Derives source.problem () input)
    (execution : Program.run source.body input = some output) :
    RecursiveRows.Derives source.problem () output := by
  apply RecursiveRows.least_models source.problem source.cycleRule (by simp [SeededCycle.problem]) output
  exact (FinitePointGuards.eval_wrap source.body (.var ()) _ output).mpr ⟨input, reached, execution⟩

/-- The independent iteration semantics is the actual least set solution of
the finite lower-rule problem. The theorem quantifies over every occurrence. -/
theorem SeededCycle.reachable_iff_derives [DecidableEq Key] (source : SeededCycle n Key)
    (output : Occurrence n Key) :
    source.Reachable output ↔ RecursiveRows.Derives source.problem () output := by
  constructor
  · rintro ⟨seed, initial, reached⟩
    induction reached with
    | seed => exact source.derives_seed seed initial
    | step _ execution ih => exact source.derives_step _ _ ih execution
  · exact RecursiveRows.least_below source.problem (fun _ => source.Reachable)
      source.reachable_models () output

def SeededCycle.solve [DecidableEq Key] (source : SeededCycle n Key) :
    Option (SymbolicRows.Segment n Key) :=
  match Program.run source.initial (raw source.key) with
  | none => none
  | some seed => some (Cycle.mk seed source.body).solution

def SeededCycle.Holds [DecidableEq Key] (source : SeededCycle n Key) : RecursiveRows.SetRow n Key :=
  fun output => match source.solve with
  | none => False
  | some segment => segment.Holds output

theorem SeededCycle.solve_exact [DecidableEq Key] (source : SeededCycle n Key)
    (output : Occurrence n Key) :
    source.Holds output ↔ RecursiveRows.Derives source.problem () output := by
  rw [← source.reachable_iff_derives]
  unfold SeededCycle.Holds SeededCycle.solve SeededCycle.Reachable
  cases initial : Program.run source.initial (raw source.key) with
  | none => simp
  | some seed =>
      simp only [Option.some.injEq]
      constructor
      · intro member
        exact ⟨seed, rfl, ((Cycle.mk seed source.body).holds_exact output).mp member⟩
      · rintro ⟨other, same, reached⟩
        cases same
        exact ((Cycle.mk seed source.body).holds_exact output).mpr reached

def SeededCycle.check [DecidableEq Key] (source : SeededCycle n Key)
    (output : Occurrence n Key) : Bool :=
  match source.solve with
  | none => false
  | some segment => segment.check output

theorem SeededCycle.check_exact [DecidableEq Key] (source : SeededCycle n Key)
    (output : Occurrence n Key) :
    source.check output = true ↔ RecursiveRows.Derives source.problem () output := by
  rw [← source.solve_exact]
  unfold SeededCycle.check SeededCycle.Holds
  cases source.solve with
  | none => simp
  | some segment => exact segment.check_exact output

theorem SeededCycle.check_rejects [DecidableEq Key] (source : SeededCycle n Key)
    (output : Occurrence n Key) :
    source.check output = false ↔ ¬ RecursiveRows.Derives source.problem () output := by
  constructor
  · intro rejected reached
    have accepted := (source.check_exact output).mpr reached
    rw [rejected] at accepted
    cases accepted
  · intro missing
    cases answer : source.check output with
    | false => rfl
    | true => exact False.elim (missing ((source.check_exact output).mp answer))

theorem SeededCycle.compiled_check_exact [DecidableEq Key] (source : SeededCycle n Key)
    (output : Occurrence n Key) :
    source.check output = true ↔
      RecursiveRowGraph.Reachable (RecursiveRowGraph.compile source.problem) () output :=
  (source.check_exact output).trans
    (RecursiveRowGraph.reachable_iff_derives source.problem () output).symm

/-- The computed finite description is itself a least model of the existing
rule problem, not only a sound approximation of its reachable occurrences. -/
theorem SeededCycle.solution_least [DecidableEq Key] (source : SeededCycle n Key) :
    RecursiveRows.IsLeastModel source.problem (fun _ => source.Holds) := by
  have same : (fun _ : Unit => source.Holds) = RecursiveRows.Derives source.problem := by
    funext slot output
    cases slot
    exact propext (source.solve_exact output)
  rw [same]
  exact RecursiveRows.least_principal source.problem

/-- Every signed seed occurrence can be introduced from its raw key using a
finite sequence of the existing protection and release constructors. -/
def Cycle.asSeeded (cycle : Cycle n Key) : SeededCycle n Key :=
  ⟨cycle.seed.key, FinitePointGuards.translation cycle.seed.weights, cycle.body⟩

theorem Cycle.asSeeded_initial [DecidableEq Key] (cycle : Cycle n Key) :
    Program.run cycle.asSeeded.initial (raw cycle.asSeeded.key) = some cycle.seed := by
  rw [show cycle.asSeeded.initial = FinitePointGuards.translation cycle.seed.weights from rfl,
    FinitePointGuards.translation_run]
  congr 1
  apply Occurrence.ext
  · rfl
  intro coordinate
  simp [translate, raw]

theorem Cycle.asSeeded_solve [DecidableEq Key] (cycle : Cycle n Key) :
    cycle.asSeeded.solve = some cycle.solution := by
  unfold SeededCycle.solve
  rw [cycle.asSeeded_initial]
  rfl

/-- The exact membership decision also applies directly to the existing finite
rule problem for an arbitrary signed seed, not just a zero-weight head. -/
theorem Cycle.check_derives [DecidableEq Key] (cycle : Cycle n Key)
    (output : Occurrence n Key) :
    cycle.check output = true ↔ RecursiveRows.Derives cycle.asSeeded.problem () output := by
  have same : cycle.asSeeded.check output = cycle.check output := by
    simp only [SeededCycle.check, cycle.asSeeded_solve, Cycle.check]
  rw [← same]
  exact cycle.asSeeded.check_exact output

theorem Cycle.solution_least [DecidableEq Key] (cycle : Cycle n Key) :
    RecursiveRows.IsLeastModel cycle.asSeeded.problem (fun _ => cycle.Holds) := by
  have same : cycle.asSeeded.Holds = cycle.Holds := by
    funext output
    unfold SeededCycle.Holds
    rw [cycle.asSeeded_solve]
    rfl
  simpa only [same] using cycle.asSeeded.solution_least

namespace Examples

def scope : Fin 1 := 0

def scalar (weight : Int) : Occurrence 1 Nat := ⟨0, fun _ => weight⟩

def ascending : SeededCycle 1 Nat :=
  ⟨0, [], [.protect scope allowNone, .residual [0]]⟩

theorem ascending_unbounded : (Cycle.mk (raw 0) ascending.body).firstHit = none := by decide

theorem ascending_accepts_large : ascending.check (scalar 1000000) = true := by decide

theorem ascending_rejects_negative : ascending.check (scalar (-1)) = false := by decide

def descending : SeededCycle 1 Nat := ⟨0, [], [.release scope allowNone]⟩

theorem negative_period_accepted : descending.check (scalar (-1000000)) = true := by decide

theorem negative_period_wrong_direction : descending.check (scalar 1) = false := by decide

/-- The release reaches zero inside the second iteration. Its residual blocks
that iteration even though the complete program has net displacement +1. -/
def interrupted : SeededCycle 1 Nat :=
  ⟨0, [], [.release scope allowNone, .residual [0],
    .protect scope allowNone, .protect scope allowNone]⟩

theorem intermediate_guard_first_hit :
    (Cycle.mk (raw 0) interrupted.body).firstHit = some 1 := by decide

theorem first_blocked_input_is_retained : interrupted.check (scalar 1) = true := by decide

theorem point_after_obstruction_is_rejected : interrupted.check (scalar 2) = false := by decide

theorem interrupted_exact_model :
    RecursiveRows.IsLeastModel interrupted.problem (fun _ => interrupted.Holds) :=
  interrupted.solution_least

theorem obstruction_blocks_actual_derivation :
    ¬ RecursiveRows.Derives interrupted.problem () (scalar 2) :=
  (interrupted.check_rejects _).mp point_after_obstruction_is_rejected

def constant : SeededCycle 1 Nat :=
  ⟨0, [], [.protect scope allowNone, .residual [0], .release scope allowNone]⟩

theorem zero_period_is_singleton :
    constant.check (scalar 0) = true ∧ constant.check (scalar 1) = false := by decide

def initiallyBlocked : SeededCycle 1 Nat :=
  ⟨0, [], [.residual [0], .protect scope allowNone]⟩

theorem blocked_at_seed_keeps_seed :
    (Cycle.mk (raw 0) initiallyBlocked.body).firstHit = some 0 ∧
      initiallyBlocked.check (scalar 0) = true ∧
      initiallyBlocked.check (scalar 1) = false := by decide

def rejectedSeed : SeededCycle 1 Nat :=
  ⟨0, [.residual [0]], [.protect scope allowNone]⟩

theorem rejected_seed_is_empty :
    rejectedSeed.solve = none ∧ rejectedSeed.check (scalar 0) = false := by decide

def offAxis : SeededCycle 2 Nat :=
  ⟨0, [.protect 0 allowNone, .protect 1 allowNone], [.release 0 allowNone, .residual [0]]⟩

def offAxisPoint (first second : Int) : Occurrence 2 Nat :=
  ⟨0, fun coordinate => if coordinate.val = 0 then first else second⟩

/-- Residual checks the entire vector; a nonzero other boundary keeps the
occurrence protected when the first boundary passes through zero. -/
theorem other_boundary_prevents_capture :
    offAxis.check (offAxisPoint 0 1) = true ∧
      offAxis.check (offAxisPoint (-1000000) 1) = true ∧
      offAxis.check (offAxisPoint (-1000000) 0) = false := by decide

theorem operation_keys_remain_distinct :
    ascending.check ⟨1, fun _ => 1000000⟩ = false := by decide

end Examples

end Yulang.CyclicRows
