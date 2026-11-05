import Yulang.RecursiveRows

/-!
# Finite guarded graphs for recursive signed rows

The existing row expressions compile to a finite list of edges. Each edge has
one head or slot as its source, a target slot, and a finite transport program.
The program retains the order of protection, release, and residual tests.
In particular, a residual tests the occurrence at its own intermediate point;
it is not moved to the end of a recursive path.

Compilation preserves every model, and the independent finite-path reachability
judgement agrees with `RecursiveRows.Derives`, hence with the least set solution.
The control graph is finite, but its integer-weight configurations need not be.
This is an exact finite presentation, not a claim that arbitrary reachability,
row inclusion, or row equality has already been decided.
-/

namespace Yulang.RecursiveRowGraph

open Directed
open RowInference (RowExpr)
open RecursiveRows (SetRow Environment Problem)

variable {n : Nat} {Key Slot : Type}

inductive Action (n : Nat) (Key : Type) where
  | protect : Fin n → Permission Key → Action n Key
  | release : Fin n → Permission Key → Action n Key
  | residual : List Key → Action n Key

def Action.run [DecidableEq Key] : Action n Key → Occurrence n Key → Option (Occurrence n Key)
  | .protect scope permission, occurrence => some (Directed.protect scope permission occurrence)
  | .release scope permission, occurrence => some (Directed.release scope permission occurrence)
  | .residual handled, occurrence =>
      if Capturable handled occurrence then none else some occurrence

def Action.image [DecidableEq Key] (action : Action n Key) (row : SetRow n Key) : SetRow n Key :=
  fun output => ∃ input, row input ∧ action.run input = some output

theorem Action.residual_image [DecidableEq Key] (handled : List Key) (row : SetRow n Key)
    (output : Occurrence n Key) :
    (Action.residual handled).image row output ↔ row output ∧ ¬ Capturable handled output := by
  constructor
  · rintro ⟨input, member, execution⟩
    by_cases capture : Capturable handled input
    · simp [Action.run, capture] at execution
    · have equal : input = output := by simpa [Action.run, capture] using execution
      cases equal
      exact ⟨member, capture⟩
  · rintro ⟨member, blocked⟩
    exact ⟨output, member, by simp [Action.run, blocked]⟩

theorem Action.run_key [DecidableEq Key] (action : Action n Key)
    (input output : Occurrence n Key) (execution : action.run input = some output) :
    output.key = input.key := by
  cases action with
  | protect scope permission =>
      have equal : Directed.protect scope permission input = output := Option.some.inj execution
      exact equal ▸ rfl
  | release scope permission =>
      have equal : Directed.release scope permission input = output := Option.some.inj execution
      exact equal ▸ rfl
  | residual handled =>
      by_cases capture : Capturable handled input
      · simp [Action.run, capture] at execution
      · have equal : input = output := by simpa [Action.run, capture] using execution
        exact equal ▸ rfl

abbrev Program (n : Nat) (Key : Type) := List (Action n Key)

def Program.run [DecidableEq Key] : Program n Key → Occurrence n Key → Option (Occurrence n Key)
  | [], occurrence => some occurrence
  | action :: rest, occurrence => (action.run occurrence).bind (Program.run rest)

theorem Program.run_append [DecidableEq Key] (first second : Program n Key)
    (input : Occurrence n Key) :
    Program.run (first ++ second) input = (Program.run first input).bind (Program.run second) := by
  induction first generalizing input with
  | nil => rfl
  | cons action rest ih =>
      simp only [List.cons_append, Program.run]
      cases action.run input <;> simp [ih]

theorem Program.run_snoc [DecidableEq Key] (program : Program n Key) (action : Action n Key)
    (input output : Occurrence n Key) :
    Program.run (program ++ [action]) input = some output ↔
      ∃ middle, Program.run program input = some middle ∧ action.run middle = some output := by
  rw [run_append]
  cases execution : Program.run program input <;> simp [Program.run]

theorem Program.run_key [DecidableEq Key] (program : Program n Key)
    (input output : Occurrence n Key) (execution : Program.run program input = some output) :
    output.key = input.key := by
  induction program generalizing input with
  | nil => exact (Option.some.inj execution) ▸ rfl
  | cons action rest ih =>
      simp only [Program.run] at execution
      cases first : action.run input with
      | none => simp [first] at execution
      | some middle =>
          have remainder : Program.run rest middle = some output := by simpa [first] using execution
          exact (ih middle remainder).trans (action.run_key input middle first)

inductive Source (Key Slot : Type) where
  | head : Key → Source Key Slot
  | slot : Slot → Source Key Slot

def Source.Holds (source : Source Key Slot) (rows : Environment n Key Slot)
    (occurrence : Occurrence n Key) : Prop :=
  match source with
  | .head key => occurrence = raw key
  | .slot name => rows name occurrence

structure Route (n : Nat) (Key Slot : Type) where
  source : Source Key Slot
  program : Program n Key

def Route.push (action : Action n Key) (route : Route n Key Slot) : Route n Key Slot :=
  ⟨route.source, route.program ++ [action]⟩

def Route.Accepts [DecidableEq Key] (route : Route n Key Slot) (rows : Environment n Key Slot)
    (output : Occurrence n Key) : Prop :=
  ∃ input, route.source.Holds rows input ∧ Program.run route.program input = some output

theorem Route.accepts_push [DecidableEq Key] (action : Action n Key) (route : Route n Key Slot)
    (rows : Environment n Key Slot) (output : Occurrence n Key) :
    (route.push action).Accepts rows output ↔ action.image (route.Accepts rows) output := by
  constructor
  · rintro ⟨input, source, execution⟩
    obtain ⟨middle, earlier, last⟩ := (Program.run_snoc route.program action input output).mp execution
    exact ⟨middle, ⟨input, source, earlier⟩, last⟩
  · rintro ⟨middle, ⟨input, source, earlier⟩, last⟩
    exact ⟨input, source, (Program.run_snoc route.program action input output).mpr
      ⟨middle, earlier, last⟩⟩

def routesMean [DecidableEq Key] (routes : List (Route n Key Slot))
    (rows : Environment n Key Slot) : SetRow n Key :=
  fun output => ∃ route ∈ routes, route.Accepts rows output

theorem routesMean_append [DecidableEq Key] (first second : List (Route n Key Slot))
    (rows : Environment n Key Slot) (output : Occurrence n Key) :
    routesMean (first ++ second) rows output ↔
      routesMean first rows output ∨ routesMean second rows output := by
  constructor
  · rintro ⟨route, member, accepted⟩
    exact (List.mem_append.mp member).elim
      (fun h => Or.inl ⟨route, h, accepted⟩) (fun h => Or.inr ⟨route, h, accepted⟩)
  · rintro (⟨route, member, accepted⟩ | ⟨route, member, accepted⟩)
    · exact ⟨route, List.mem_append.mpr (Or.inl member), accepted⟩
    · exact ⟨route, List.mem_append.mpr (Or.inr member), accepted⟩

theorem routesMean_push [DecidableEq Key] (action : Action n Key) (routes : List (Route n Key Slot))
    (rows : Environment n Key Slot) (output : Occurrence n Key) :
    routesMean (routes.map (Route.push action)) rows output ↔
      action.image (routesMean routes rows) output := by
  constructor
  · rintro ⟨pushed, pushedMember, accepted⟩
    obtain ⟨route, routeMember, rfl⟩ := List.mem_map.mp pushedMember
    obtain ⟨middle, earlier, last⟩ := (route.accepts_push action rows output).mp accepted
    exact ⟨middle, ⟨route, routeMember, earlier⟩, last⟩
  · rintro ⟨middle, ⟨route, member, earlier⟩, last⟩
    exact ⟨route.push action, List.mem_map.mpr ⟨route, member, rfl⟩,
      (route.accepts_push action rows output).mpr ⟨middle, earlier, last⟩⟩

/-- Every branch ends in a single source; its outer operations are appended in
evaluation order. No distributivity or guard commutation is assumed. -/
def compileExpr : RowExpr Key (Fin n) Slot → List (Route n Key Slot)
  | .empty => []
  | .head key => [⟨.head key, []⟩]
  | .var slot => [⟨.slot slot, []⟩]
  | .union left right => compileExpr left ++ compileExpr right
  | .protect scope permission row => (compileExpr row).map (Route.push (.protect scope permission))
  | .release scope permission row => (compileExpr row).map (Route.push (.release scope permission))
  | .residual handled row => (compileExpr row).map (Route.push (.residual handled))

/-- The finite compilation preserves a row expression for every supplied row
assignment, including assignments with infinite support. -/
theorem compileExpr_exact [DecidableEq Key] (row : RowExpr Key (Fin n) Slot)
    (rows : Environment n Key Slot) (output : Occurrence n Key) :
    routesMean (compileExpr row) rows output ↔ row.eval (RecursiveRows.algebra n Key) rows output := by
  induction row generalizing output with
  | empty => simp [compileExpr, routesMean, RowExpr.eval, RecursiveRows.algebra]
  | head key =>
      simp [compileExpr, routesMean, Route.Accepts, Source.Holds, Program.run,
        RowExpr.eval, RecursiveRows.algebra, eq_comm]
  | var slot =>
      simp [compileExpr, routesMean, Route.Accepts, Source.Holds, Program.run,
        RowExpr.eval]
  | union left right ihLeft ihRight =>
      exact (routesMean_append _ _ rows output).trans (or_congr (ihLeft output) (ihRight output))
  | protect scope permission row ih =>
      rw [compileExpr, routesMean_push]
      simp only [Action.image, Action.run, Option.some.injEq, RowExpr.eval, RecursiveRows.algebra]
      exact exists_congr (fun input => and_congr (ih input) Iff.rfl)
  | release scope permission row ih =>
      rw [compileExpr, routesMean_push]
      simp only [Action.image, Action.run, Option.some.injEq, RowExpr.eval, RecursiveRows.algebra]
      exact exists_congr (fun input => and_congr (ih input) Iff.rfl)
  | residual handled row ih =>
      rw [compileExpr, routesMean_push, Action.residual_image]
      exact and_congr (ih output) Iff.rfl

structure Edge (n : Nat) (Key Slot : Type) where
  source : Source Key Slot
  program : Program n Key
  target : Slot

def Route.edge (target : Slot) (route : Route n Key Slot) : Edge n Key Slot :=
  ⟨route.source, route.program, target⟩

abbrev Graph (n : Nat) (Key Slot : Type) := List (Edge n Key Slot)

def compile (problem : Problem n Key Slot) : Graph n Key Slot :=
  problem.flatMap (fun rule => (compileExpr rule.lower).map (Route.edge rule.target))

def Models [DecidableEq Key] (graph : Graph n Key Slot) (rows : Environment n Key Slot) : Prop :=
  ∀ edge ∈ graph, ∀ input output, edge.source.Holds rows input →
    Program.run edge.program input = some output → rows edge.target output

theorem compile_models_exact [DecidableEq Key] (problem : Problem n Key Slot)
    (rows : Environment n Key Slot) :
    Models (compile problem) rows ↔ RecursiveRows.Models problem rows := by
  constructor
  · intro model rule declared output member
    obtain ⟨route, routeMember, input, source, execution⟩ :=
      (compileExpr_exact rule.lower rows output).mpr member
    exact model (route.edge rule.target)
      (List.mem_flatMap.mpr ⟨rule, declared, List.mem_map.mpr ⟨route, routeMember, rfl⟩⟩)
      input output source execution
  · intro model edge declared input output source execution
    obtain ⟨rule, ruleMember, edgeMember⟩ := List.mem_flatMap.mp declared
    obtain ⟨route, routeMember, rfl⟩ := List.mem_map.mp edgeMember
    exact model rule ruleMember output ((compileExpr_exact rule.lower rows output).mp
      ⟨route, routeMember, input, source, execution⟩)

/-- Independent reachability in the compiled graph: start at a declared head,
then follow a finite path of slot edges whose guarded programs succeed. -/
inductive Reachable [DecidableEq Key] (graph : Graph n Key Slot) : Slot → Occurrence n Key → Prop where
  | head {key : Key} {program : Program n Key} {target : Slot} :
      ⟨.head key, program, target⟩ ∈ graph →
      Program.run program (raw key) = some output → Reachable graph target output
  | step {source target : Slot} {program : Program n Key} :
      ⟨.slot source, program, target⟩ ∈ graph → Reachable graph source input →
      Program.run program input = some output → Reachable graph target output

theorem reachable_models [DecidableEq Key] (graph : Graph n Key Slot) :
    Models graph (Reachable graph) := by
  intro edge declared input output sourceFact execution
  rcases edge with ⟨origin, program, target⟩
  cases origin with
  | head key =>
      change input = raw key at sourceFact
      cases sourceFact
      exact .head declared execution
  | slot slot => exact .step declared sourceFact execution

theorem reachable_below [DecidableEq Key] (graph : Graph n Key Slot)
    (rows : Environment n Key Slot) (model : Models graph rows) :
    RecursiveRows.Below (Reachable graph) rows := by
  intro slot output reached
  induction reached with
  | head declared execution => exact model _ declared _ _ rfl execution
  | step declared reached execution ih => exact model _ declared _ _ ih execution

/-- Graph paths characterize the actual least set solution, with neither a
weight bound nor a finite-support premise. -/
theorem reachable_iff_derives [DecidableEq Key] (problem : Problem n Key Slot)
    (slot : Slot) (occurrence : Occurrence n Key) :
    Reachable (compile problem) slot occurrence ↔ RecursiveRows.Derives problem slot occurrence :=
  ⟨reachable_below (compile problem) (RecursiveRows.Derives problem)
      ((compile_models_exact problem _).mpr (RecursiveRows.least_models problem)) slot occurrence,
    RecursiveRows.least_below problem (Reachable (compile problem))
      ((compile_models_exact problem _).mp (reachable_models (compile problem))) slot occurrence⟩

theorem compiled_least [DecidableEq Key] (problem : Problem n Key Slot) :
    RecursiveRows.IsLeastModel problem (Reachable (compile problem)) :=
  ⟨(compile_models_exact problem _).mp (reachable_models (compile problem)),
    fun rows model => reachable_below (compile problem) rows ((compile_models_exact problem rows).mpr model)⟩

/-- Even if the supplied slot type is infinite, every reachable control is
one of the finitely many targets actually present in the compiled graph. -/
theorem reachable_target [DecidableEq Key] (graph : Graph n Key Slot)
    (reached : Reachable graph slot occurrence) : slot ∈ graph.map Edge.target := by
  cases reached with
  | head declared _ => exact List.mem_map.mpr ⟨_, declared, rfl⟩
  | step declared _ _ => exact List.mem_map.mpr ⟨_, declared, rfl⟩

def headKeys (graph : Graph n Key Slot) : List Key :=
  graph.filterMap (fun edge => match edge.source with
    | .head key => some key
    | .slot _ => none)

theorem reachable_key [DecidableEq Key] (graph : Graph n Key Slot)
    (reached : Reachable graph slot occurrence) : occurrence.key ∈ headKeys graph := by
  induction reached with
  | head declared execution =>
      rw [Program.run_key _ _ _ execution]
      exact List.mem_filterMap.mpr ⟨_, declared, rfl⟩
  | step declared reached execution ih =>
      rw [Program.run_key _ _ _ execution]
      exact ih

namespace Examples

def scope : Fin 1 := 0

/-- The two syntactic placements of the guard differ at a fresh head. -/
def guardBefore : Program 1 Nat := [.residual [0], .protect scope allowNone]
def guardAfter : Program 1 Nat := [.protect scope allowNone, .residual [0]]

theorem guard_before_rejects : Program.run guardBefore (raw 0) = none := by decide
theorem guard_after_keeps :
    Program.run guardAfter (raw 0) = some (protect scope allowNone (raw 0)) := by decide

theorem growing_paths (count : Nat) :
    Reachable (compile RecursiveRows.Examples.growing) () (RecursiveRows.Examples.raised count) :=
  (reachable_iff_derives _ _ _).mpr (RecursiveRows.Examples.every_weight_derived count)

end Examples

end Yulang.RecursiveRowGraph
