import Yulang.RowTransportNormalForm

/-!
# Finite point guards in the existing row syntax

The wrapper below expresses a guarded transport program using only the existing
`RowExpr` protection, release and residual constructors. Its evaluation theorem
uses the established possibly infinite set-row algebra and keeps every guard
at its original point in the program.

Conversely, every integer translation with finitely many forbidden input points
has such a program. A point is tested by translating its weight vector to zero,
applying the ordinary residual for its key, then translating back. The test
uses the full occurrence: another key with the same weights remains permitted.
Finite graphs of these transports embed into finite row problems, with exact
preservation of reachability and the least set solution. This is an
expressibility theorem, with no general reachability decision claim.
-/

namespace Yulang.FinitePointGuards

open Directed
open RowInference (RowExpr)
open RecursiveRowGraph (Action Program)
open RecursiveRows (Environment)
open RowTransportNormalForm (Weights NormalForm translate)

variable {n : Nat} {Key Slot : Type}

def applyAction : Action n Key → RowExpr Key (Fin n) Slot → RowExpr Key (Fin n) Slot
  | .protect scope permission, row => .protect scope permission row
  | .release scope permission, row => .release scope permission row
  | .residual handled, row => .residual handled row

theorem eval_applyAction [DecidableEq Key] (action : Action n Key)
    (row : RowExpr Key (Fin n) Slot) (rows : Environment n Key Slot) (output : Occurrence n Key) :
    (applyAction action row).eval (RecursiveRows.algebra n Key) rows output ↔
      action.image (row.eval (RecursiveRows.algebra n Key) rows) output := by
  cases action with
  | protect scope permission =>
      simp [applyAction, RowExpr.eval, RecursiveRows.algebra, Action.image, Action.run]
  | release scope permission =>
      simp [applyAction, RowExpr.eval, RecursiveRows.algebra, Action.image, Action.run]
  | residual handled => exact (Action.residual_image handled _ output).symm

/-- The first program action is the innermost row operation. -/
def wrap : Program n Key → RowExpr Key (Fin n) Slot → RowExpr Key (Fin n) Slot
  | [], row => row
  | action :: rest, row => wrap rest (applyAction action row)

theorem eval_wrap [DecidableEq Key] (program : Program n Key)
    (row : RowExpr Key (Fin n) Slot) (rows : Environment n Key Slot) (output : Occurrence n Key) :
    (wrap program row).eval (RecursiveRows.algebra n Key) rows output ↔
      ∃ input, row.eval (RecursiveRows.algebra n Key) rows input ∧
        Program.run program input = some output := by
  induction program generalizing row output with
  | nil =>
      constructor
      · intro member; exact ⟨output, member, rfl⟩
      · rintro ⟨input, member, execution⟩
        cases Option.some.inj execution
        exact member
  | cons action rest ih =>
      rw [wrap, ih]
      constructor
      · rintro ⟨middle, middleMember, remainder⟩
        obtain ⟨input, inputMember, first⟩ := (eval_applyAction action row rows middle).mp middleMember
        exact ⟨input, inputMember, by simpa [Program.run, first] using remainder⟩
      · rintro ⟨input, member, execution⟩
        cases first : action.run input with
        | none => simp [Program.run, first] at execution
        | some middle =>
            exact ⟨middle, (eval_applyAction action row rows middle).mpr ⟨input, member, first⟩,
              by simpa [Program.run, first] using execution⟩

/-! ## Every integer translation uses finitely many signed unit steps -/

def coordinate (scope : Fin n) : Int → Program n Key
  | .ofNat count => List.replicate count (.protect scope allowNone)
  | .negSucc count => List.replicate (count + 1) (.release scope allowNone)

theorem repeated_protect_run [DecidableEq Key] (scope : Fin n) (count : Nat)
    (input : Occurrence n Key) :
    Program.run (List.replicate count (.protect scope allowNone)) input =
      some (shift scope allowNone (count : Int) input) := by
  induction count generalizing input with
  | zero => simp [List.replicate, Program.run]
  | succ count ih =>
      simp only [List.replicate_succ, Program.run, Action.run, Option.bind_some, ih]
      congr 1
      unfold protect
      rw [shift_add]
      have amounts : 1 + (count : Int) = ((count + 1 : Nat) : Int) := by omega
      rw [amounts]

theorem repeated_release_run [DecidableEq Key] (scope : Fin n) (count : Nat)
    (input : Occurrence n Key) :
    Program.run (List.replicate count (.release scope allowNone)) input =
      some (shift scope allowNone (-(count : Int)) input) := by
  induction count generalizing input with
  | zero => simp [List.replicate, Program.run]
  | succ count ih =>
      simp only [List.replicate_succ, Program.run, Action.run, Option.bind_some, ih]
      congr 1
      unfold release
      rw [shift_add]
      have amounts : -1 + -(count : Int) = -((count + 1 : Nat) : Int) := by omega
      rw [amounts]

theorem coordinate_run [DecidableEq Key] (scope : Fin n) (amount : Int)
    (input : Occurrence n Key) :
    Program.run (coordinate scope amount) input = some (shift scope allowNone amount input) := by
  cases amount with
  | ofNat count => exact repeated_protect_run scope count input
  | negSucc count =>
      simpa only [coordinate, Int.negSucc_eq, Int.natCast_succ] using
        repeated_release_run scope (count + 1) input

def coordinates (displacement : Weights n) : List (Fin n) → Program n Key
  | [] => []
  | scope :: rest => coordinate scope (displacement scope) ++ coordinates displacement rest

def moveCoordinates (displacement : Weights n) : List (Fin n) → Occurrence n Key → Occurrence n Key
  | [], input => input
  | scope :: rest, input =>
      moveCoordinates displacement rest (shift scope allowNone (displacement scope) input)

theorem coordinates_run [DecidableEq Key] (displacement : Weights n) (scopes : List (Fin n))
    (input : Occurrence n Key) :
    Program.run (coordinates displacement scopes) input = some (moveCoordinates displacement scopes input) := by
  induction scopes generalizing input with
  | nil => rfl
  | cons scope rest ih =>
      simp only [coordinates, Program.run_append, coordinate_run, Option.bind_some,
        moveCoordinates, ih]

theorem moveCoordinates_key (displacement : Weights n) (scopes : List (Fin n))
    (input : Occurrence n Key) : (moveCoordinates displacement scopes input).key = input.key := by
  induction scopes generalizing input with
  | nil => rfl
  | cons scope rest ih => exact ih _

theorem moveCoordinates_weights (displacement : Weights n) (scopes : List (Fin n))
    (distinct : scopes.Nodup) (input : Occurrence n Key) (index : Fin n) :
    (moveCoordinates displacement scopes input).weights index =
      input.weights index + if index ∈ scopes then displacement index else 0 := by
  induction scopes generalizing input with
  | nil => simp [moveCoordinates]
  | cons scope rest ih =>
      obtain ⟨absent, tailDistinct⟩ := List.nodup_cons.mp distinct
      rw [moveCoordinates, ih tailDistinct]
      by_cases same : index = scope
      · subst index
        simp [shift, allowNone, absent]
      · simp [shift, allowNone, same]

def translation (displacement : Weights n) : Program n Key :=
  coordinates displacement (List.finRange n)

theorem translation_run [DecidableEq Key] (displacement : Weights n) (input : Occurrence n Key) :
    Program.run (translation displacement) input = some (translate displacement input) := by
  rw [translation, coordinates_run]
  congr 1
  apply Occurrence.ext
  · exact moveCoordinates_key _ _ _
  intro index
  rw [moveCoordinates_weights displacement _ (List.nodup_finRange n)]
  simp [translate]

/-! ## A shifted residual excludes exactly one prescribed point -/

def exclude (point : Occurrence n Key) : Program n Key :=
  translation (fun index => -point.weights index) ++
    .residual [point.key] :: translation point.weights

theorem translated_capture_iff (point input : Occurrence n Key) :
    Capturable [point.key] (translate (fun index => -point.weights index) input) ↔ input = point := by
  constructor
  · rintro ⟨key, weights⟩
    apply Occurrence.ext
    · exact List.mem_singleton.mp key
    intro index
    have zero := weights index
    change input.weights index + -point.weights index = 0 at zero
    omega
  · intro equal
    subst input
    refine ⟨by simp [translate], ?_⟩
    intro index
    change point.weights index + -point.weights index = 0
    omega

theorem translation_restores (point input : Occurrence n Key) :
    translate point.weights (translate (fun index => -point.weights index) input) = input := by
  apply Occurrence.ext
  · rfl
  intro index
  change input.weights index + -point.weights index + point.weights index = input.weights index
  omega

theorem exclude_run [DecidableEq Key] (point input : Occurrence n Key) :
    Program.run (exclude point) input = if input = point then none else some input := by
  rw [exclude, Program.run_append, translation_run]
  simp only [Option.bind_some, Program.run, Action.run]
  simp only [translated_capture_iff]
  by_cases equal : input = point
  · simp [equal]
  · simp [equal, translation_run, translation_restores]

def excludeAll : List (Occurrence n Key) → Program n Key
  | [] => []
  | point :: rest => exclude point ++ excludeAll rest

theorem excludeAll_run [DecidableEq Key] (excluded : List (Occurrence n Key))
    (input : Occurrence n Key) :
    Program.run (excludeAll excluded) input = if input ∈ excluded then none else some input := by
  induction excluded with
  | nil => simp [excludeAll, Program.run]
  | cons point rest ih =>
      rw [excludeAll, Program.run_append, exclude_run]
      by_cases equal : input = point <;> simp [equal, ih]

/-- Every finite-point-guarded translation can be expressed using ordinary
protect/release unit steps and residuals. No new row constructor is needed. -/
def encode (normal : NormalForm n Key) : Program n Key :=
  excludeAll normal.excluded ++ translation normal.displacement

theorem encode_run [DecidableEq Key] (normal : NormalForm n Key) (input : Occurrence n Key) :
    Program.run (encode normal) input = normal.run input := by
  rw [encode, Program.run_append, excludeAll_run]
  by_cases excluded : input ∈ normal.excluded <;>
    simp [excluded, NormalForm.run, translation_run]

theorem eval_encode [DecidableEq Key] (normal : NormalForm n Key)
    (row : RowExpr Key (Fin n) Slot) (rows : Environment n Key Slot) (output : Occurrence n Key) :
    (wrap (encode normal) row).eval (RecursiveRows.algebra n Key) rows output ↔
      ∃ input, row.eval (RecursiveRows.algebra n Key) rows input ∧ normal.run input = some output := by
  rw [eval_wrap]
  simp only [encode_run]

/-! ## Finite guarded translation graphs embed into finite row problems -/

open RecursiveRowGraph (Source Route compileExpr)

theorem compile_applyAction (action : Action n Key) (row : RowExpr Key (Fin n) Slot) :
    compileExpr (applyAction action row) = (compileExpr row).map (Route.push action) := by
  cases action <;> rfl

theorem compile_wrap (program : Program n Key) (row : RowExpr Key (Fin n) Slot) :
    compileExpr (wrap program row) =
      (compileExpr row).map (fun route => ⟨route.source, route.program ++ program⟩) := by
  induction program generalizing row with
  | nil => simp [wrap]
  | cons action rest ih =>
      rw [wrap, ih, compile_applyAction]
      simp only [List.map_map]
      congr 1
      funext route
      cases route
      simp [Route.push, List.append_assoc]

def sourceRow : Source Key Slot → RowExpr Key (Fin n) Slot
  | .head key => .head key
  | .slot name => .var name

theorem compile_source (source : Source Key Slot) :
    compileExpr (sourceRow (n := n) source) = [⟨source, []⟩] := by
  cases source <;> rfl

structure GuardedEdge (n : Nat) (Key Slot : Type) where
  source : Source Key Slot
  transport : NormalForm n Key
  target : Slot

def GuardedEdge.toEdge (edge : GuardedEdge n Key Slot) : RecursiveRowGraph.Edge n Key Slot :=
  ⟨edge.source, encode edge.transport, edge.target⟩

def GuardedEdge.toRule (edge : GuardedEdge n Key Slot) : RecursiveRows.Rule n Key Slot :=
  ⟨edge.target, wrap (encode edge.transport) (sourceRow edge.source)⟩

/-- An arbitrary initial integer point is expressible from its ordinary raw
head; initialization does not restrict the starting weights to zero. -/
def GuardedEdge.seed (target : Slot) (point : Occurrence n Key) : GuardedEdge n Key Slot :=
  ⟨.head point.key, ⟨point.weights, []⟩, target⟩

theorem GuardedEdge.seed_run [DecidableEq Key] (target : Slot) (point : Occurrence n Key) :
    (GuardedEdge.seed target point).transport.run (raw point.key) = some point := by
  simp only [GuardedEdge.seed, NormalForm.run, List.not_mem_nil, ↓reduceIte]
  congr 1
  apply Occurrence.ext
  · rfl
  intro index
  simp [translate, raw]

abbrev GuardedGraph (n : Nat) (Key Slot : Type) := List (GuardedEdge n Key Slot)

def programGraph (graph : GuardedGraph n Key Slot) : RecursiveRowGraph.Graph n Key Slot :=
  graph.map GuardedEdge.toEdge

def rowProblem (graph : GuardedGraph n Key Slot) : RecursiveRows.Problem n Key Slot :=
  graph.map GuardedEdge.toRule

/-- Compiling the embedded row problem returns precisely its encoded edge
programs. There are no extra control slots, branches, or assumptions. -/
theorem compile_rowProblem (graph : GuardedGraph n Key Slot) :
    RecursiveRowGraph.compile (rowProblem graph) = programGraph graph := by
  induction graph with
  | nil => rfl
  | cons edge rest ih =>
      change (compileExpr edge.toRule.lower).map (Route.edge edge.toRule.target) ++
        RecursiveRowGraph.compile (rowProblem rest) = edge.toEdge :: programGraph rest
      rw [ih]
      simp [GuardedEdge.toRule, compile_wrap, compile_source, Route.edge, GuardedEdge.toEdge]

/-- Reachability stated directly with finite forbidden points and integer
translations, independently of row expressions and transport programs. -/
inductive GuardedReachable [DecidableEq Key] (graph : GuardedGraph n Key Slot) :
    Slot → Occurrence n Key → Prop where
  | head {key : Key} {transport : NormalForm n Key} {target : Slot} :
      ⟨.head key, transport, target⟩ ∈ graph →
      transport.run (raw key) = some output → GuardedReachable graph target output
  | step {source target : Slot} {transport : NormalForm n Key} :
      ⟨.slot source, transport, target⟩ ∈ graph → GuardedReachable graph source input →
      transport.run input = some output → GuardedReachable graph target output

theorem seed_reachable [DecidableEq Key] (graph : GuardedGraph n Key Slot)
    (target : Slot) (point : Occurrence n Key) (declared : GuardedEdge.seed target point ∈ graph) :
    GuardedReachable graph target point :=
  .head declared (GuardedEdge.seed_run target point)

theorem guarded_reachable_program [DecidableEq Key] (graph : GuardedGraph n Key Slot)
    (slot : Slot) (occurrence : Occurrence n Key) :
    GuardedReachable graph slot occurrence ↔
      RecursiveRowGraph.Reachable (programGraph graph) slot occurrence := by
  constructor
  · intro reached
    induction reached with
    | head declared execution =>
        exact .head (List.mem_map.mpr ⟨_, declared, rfl⟩) (by simpa only [encode_run] using execution)
    | step declared reached execution ih =>
        exact .step (List.mem_map.mpr ⟨_, declared, rfl⟩) ih (by simpa only [encode_run] using execution)
  · intro reached
    induction reached with
    | head declared execution =>
        obtain ⟨edge, member, equality⟩ := List.mem_map.mp declared
        cases edge with
        | mk source transport target =>
            cases equality
            exact .head member (by simpa only [encode_run] using execution)
    | step declared reached execution ih =>
        obtain ⟨edge, member, equality⟩ := List.mem_map.mp declared
        cases edge with
        | mk source transport target =>
            cases equality
            exact .step member ih (by simpa only [encode_run] using execution)

/-- Arbitrary finite-point-guarded integer translation graphs occur inside the
existing row language. Their reachability is exactly the least row solution. -/
theorem guarded_graph_exact [DecidableEq Key] (graph : GuardedGraph n Key Slot)
    (slot : Slot) (occurrence : Occurrence n Key) :
    GuardedReachable graph slot occurrence ↔
      RecursiveRows.Derives (rowProblem graph) slot occurrence := by
  rw [guarded_reachable_program, ← compile_rowProblem]
  exact RecursiveRowGraph.reachable_iff_derives _ _ _

end Yulang.FinitePointGuards
