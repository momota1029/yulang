import Yulang.FreshBoundaries
import Yulang.AnnotationSnapshots

/-!
# Fresh boundaries in inferred row expressions and annotation snapshots

`eval_mapScopes` proves that renaming every boundary in the existing `RowExpr`
syntax commutes with signed-row evaluation. The environment is arbitrary:
unknown row slots can contain positive or negative weights, repeated keys, and
the same key as an explicit head. `fresh_eval_zero` then constructs zero origin
at the newly allocated coordinate for every occurrence of the evaluated row.

`observe_mapScopes` and `checkHistory_reindex` connect the same embedding to
frozen T3 observations. Scope names do not change their checks or discard any
history. This is independent of later substitution; it does not reobserve an
unknown slot when that slot becomes concrete.

These theorems concern finite row expressions over arbitrary finite signed-row
environments. They do not discover source scopes, rename type-variable slots,
traverse latent values, or prove whole-language elaboration.
-/

namespace Yulang.FreshRowInference

open Directed
open RowInference (RowExpr signedAlgebra)
open FreshBoundaries (reindex liftOccurrence)
open AnnotationSnapshots (Observation TrackedRow)

/-- Structural renaming of boundary names, preserving keys, masks, and slots. -/
def mapScopes (embedding : Scope → OtherScope) : RowExpr Key Scope α → RowExpr Key OtherScope α
  | .empty => .empty
  | .head key => .head key
  | .var slot => .var slot
  | .union left right => .union (mapScopes embedding left) (mapScopes embedding right)
  | .protect scope permission row => .protect (embedding scope) permission (mapScopes embedding row)
  | .release scope permission row => .release (embedding scope) permission (mapScopes embedding row)
  | .residual handled row => .residual handled (mapScopes embedding row)

theorem mapScopes_identity (row : RowExpr Key Scope α) : mapScopes id row = row := by
  induction row <;> simp_all [mapScopes]

theorem mapScopes_comp (first : Scope → Middle) (second : Middle → OtherScope)
    (row : RowExpr Key Scope α) :
    mapScopes second (mapScopes first row) = mapScopes (second ∘ first) row := by
  induction row <;> simp_all [mapScopes, Function.comp_def]

/-- Scope renaming does not allocate or identify any row-variable slot. -/
theorem mapScopes_subst (embedding : Scope → OtherScope) (row : RowExpr Key Scope α)
    (substitution : α → RowExpr Key Scope β) :
    mapScopes embedding (row.subst substitution) =
      (mapScopes embedding row).subst (fun slot => mapScopes embedding (substitution slot)) := by
  induction row <;> simp_all [mapScopes, RowExpr.subst]

theorem reindex_raw (embedding : Fin n → Fin m) (key : Key) :
    reindex embedding (raw key) = (raw key : Occurrence m Key) := by
  apply Occurrence.ext
  · rfl
  intro coordinate
  cases found : FreshBoundaries.locate embedding coordinate <;>
    simp [reindex, found, raw]

/-- Exact evaluation for every existing row constructor, including both signed
transport directions and handler subtraction. -/
theorem eval_mapScopes [DecidableEq Key] (embedding : Fin n → Fin m)
    (injective : Function.Injective embedding) (row : RowExpr Key (Fin n) α)
    (rows : α → Row n Key) :
    ((mapScopes embedding row).eval (signedAlgebra m Key)
      (fun slot => (rows slot).map (reindex embedding)) : Row m Key) =
        (row.eval (signedAlgebra n Key) rows).map (reindex embedding) := by
  dsimp only [signedAlgebra] at *
  induction row with
  | empty => rfl
  | head key => simp [mapScopes, RowExpr.eval, reindex_raw]
  | var slot => rfl
  | union left right ihLeft ihRight =>
      change List.append _ _ = List.map _ (List.append _ _)
      rw [ihLeft, ihRight]
      exact (List.map_append ..).symm
  | protect scope permission row ih =>
      change List.map (protect (embedding scope) permission) _ =
        List.map (reindex embedding) (List.map (protect scope permission) _)
      rw [ih]
      simp only [List.map_map, Function.comp_def,
        FreshBoundaries.reindex_protect embedding injective]
  | release scope permission row ih =>
      change List.map (release (embedding scope) permission) _ =
        List.map (reindex embedding) (List.map (release scope permission) _)
      rw [ih]
      simp only [List.map_map, Function.comp_def,
        FreshBoundaries.reindex_release embedding injective]
  | residual handled row ih =>
      change Directed.residual handled _ = List.map (reindex embedding) (Directed.residual handled _)
      rw [ih, FreshBoundaries.residual_reindex embedding injective]

/-- Allocate a fresh coordinate in a complete inferred row expression. -/
def liftRow (row : RowExpr Key (Fin n) α) : RowExpr Key (Fin (n + 1)) α :=
  mapScopes Fin.succ row

def liftEnvironment (rows : α → Row n Key) : α → Row (n + 1) Key :=
  fun slot => (rows slot).map liftOccurrence

theorem eval_liftRow [DecidableEq Key] (row : RowExpr Key (Fin n) α) (rows : α → Row n Key) :
    ((liftRow row).eval (signedAlgebra (n + 1) Key) (liftEnvironment rows) : Row (n + 1) Key) =
      (row.eval (signedAlgebra n Key) rows).map liftOccurrence :=
  eval_mapScopes Fin.succ FreshBoundaries.succ_injective row rows

/-- The fresh origin premise is derived from all of the row syntax, including
arbitrary substituted unknown tails. No old-coordinate zero premise is needed. -/
theorem fresh_eval_zero [DecidableEq Key] (row : RowExpr Key (Fin n) α) (rows : α → Row n Key)
    (occurrence : Occurrence (n + 1) Key)
    (member : List.Mem occurrence ((liftRow row).eval (signedAlgebra (n + 1) Key)
      (liftEnvironment rows))) :
    occurrence.weights FreshBoundaries.fresh = 0 := by
  have lifted := eval_liftRow row rows
  dsimp only [signedAlgebra] at lifted member
  rw [lifted] at member
  obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
  exact FreshBoundaries.liftOccurrence_fresh original

/-- The exact residual after a fresh selective boundary, expressed in the old
inference row. Permission is a filter on handled keys, not an injected effect. -/
theorem fresh_protect_residual_eval [DecidableEq Key] (handled : List Key)
    (permission : Permission Key) (row : RowExpr Key (Fin n) α) (rows : α → Row n Key) :
    (RowExpr.residual handled (.protect FreshBoundaries.fresh permission (liftRow row))).eval
      (signedAlgebra (n + 1) Key) (liftEnvironment rows) =
        (Directed.residual (handled.filter permission) (row.eval (signedAlgebra n Key) rows)).map
          (fun occurrence => protect FreshBoundaries.fresh permission (liftOccurrence occurrence)) := by
  have lifted := eval_liftRow row rows
  dsimp only [signedAlgebra] at lifted ⊢
  change Directed.residual handled
    (List.map (protect FreshBoundaries.fresh permission)
      ((liftRow row).eval (signedAlgebra (n + 1) Key) (liftEnvironment rows))) = _
  dsimp only [signedAlgebra]
  rw [lifted]
  simp only [List.map_map, Function.comp_def]
  exact FreshBoundaries.fresh_protect_residual handled permission _

/-- A runtime row bound inferred from the lifted expression supplies origin.
Deriving this bound from source typing is a separate obligation. -/
theorem bounded_fresh_origin [DecidableEq Key] (row : RowExpr Key (Fin n) α)
    (rows : α → Row n Key) (computation : Computation (n + 1) Key Payload Response Value)
    (bound : Computation.BoundedBy
      ((liftRow row).eval (signedAlgebra (n + 1) Key) (liftEnvironment rows)) computation) :
    Computation.ZeroAt FreshBoundaries.fresh computation :=
  Computation.allRequests_mono _ _ (fun occurrence member => fresh_eval_zero row rows occurrence member)
    computation bound

/-! ## Existing frozen observations are invariant under scope embeddings -/

def reindexObservation (embedding : Fin n → Fin m) (observation : Observation n Key) :
    Observation m Key :=
  ⟨observation.permission, observation.concrete.map (reindex embedding)⟩

theorem visible_reindex_iff (embedding : Fin n → Fin m) (injective : Function.Injective embedding)
    (occurrence : Occurrence n Key) :
    AnnotationSnapshots.Visible (reindex embedding occurrence) ↔ AnnotationSnapshots.Visible occurrence :=
  FreshBoundaries.reindex_zero_iff embedding injective occurrence

theorem observation_check_reindex (embedding : Fin n → Fin m) (injective : Function.Injective embedding)
    (observation : Observation n Key) :
    (reindexObservation embedding observation).check = observation.check := by
  simp only [reindexObservation, Observation.check, List.all_map, Function.comp_def,
    visible_reindex_iff embedding injective, FreshBoundaries.reindex_key]

theorem observation_admissible_reindex (embedding : Fin n → Fin m)
    (injective : Function.Injective embedding) (observation : Observation n Key) :
    (reindexObservation embedding observation).Admissible ↔ observation.Admissible := by
  rw [← Observation.check_exact, ← Observation.check_exact, observation_check_reindex embedding injective]

theorem known_mapScopes [DecidableEq Key] (embedding : Fin n → Fin m)
    (injective : Function.Injective embedding) (row : RowExpr Key (Fin n) α) :
    AnnotationSnapshots.known (mapScopes embedding row) =
      (AnnotationSnapshots.known row).map (reindex embedding) := by
  simpa only [AnnotationSnapshots.known, signedAlgebra, List.map_nil] using
    eval_mapScopes embedding injective row (fun _ => [])

/-- This compares the same finalization snapshot under a coordinate embedding,
not a new observation after a row-variable substitution. -/
theorem observe_mapScopes [DecidableEq Key] (embedding : Fin n → Fin m)
    (injective : Function.Injective embedding) (permission : Key → Bool)
    (row : RowExpr Key (Fin n) α) :
    AnnotationSnapshots.observe permission (mapScopes embedding row) =
      reindexObservation embedding (AnnotationSnapshots.observe permission row) := by
  simp only [AnnotationSnapshots.observe, reindexObservation, known_mapScopes embedding injective]

theorem observe_check_mapScopes [DecidableEq Key] (embedding : Fin n → Fin m)
    (injective : Function.Injective embedding) (permission : Key → Bool)
    (row : RowExpr Key (Fin n) α) :
    (AnnotationSnapshots.observe permission (mapScopes embedding row)).check =
      (AnnotationSnapshots.observe permission row).check := by
  rw [observe_mapScopes embedding injective, observation_check_reindex embedding injective]

theorem checkHistory_reindex (embedding : Fin n → Fin m) (injective : Function.Injective embedding)
    (history : List (Observation n Key)) :
    AnnotationSnapshots.checkHistory (history.map (reindexObservation embedding)) =
      AnnotationSnapshots.checkHistory history := by
  simp only [AnnotationSnapshots.checkHistory, List.all_map, Function.comp_def,
    observation_check_reindex embedding injective]

def reindexTracked (embedding : Fin n → Fin m) (tracked : TrackedRow n Key α) : TrackedRow m Key α :=
  ⟨mapScopes embedding tracked.row, tracked.history.map (reindexObservation embedding)⟩

theorem reindexTracked_annotate [DecidableEq Key] (embedding : Fin n → Fin m)
    (injective : Function.Injective embedding) (tracked : TrackedRow n Key α)
    (permission : Key → Bool) :
    reindexTracked embedding (tracked.annotate permission) =
      (reindexTracked embedding tracked).annotate permission := by
  simp only [reindexTracked, TrackedRow.annotate, List.map_cons, observe_mapScopes embedding injective]

theorem reindexTracked_subst (embedding : Fin n → Fin m) (tracked : TrackedRow n Key α)
    (substitution : α → RowExpr Key (Fin n) β) :
    reindexTracked embedding (tracked.subst substitution) =
      (reindexTracked embedding tracked).subst (fun slot => mapScopes embedding (substitution slot)) := by
  simp only [reindexTracked, TrackedRow.subst, mapScopes_subst]

/-- The actual gate attached to an inference formula is unchanged, regardless
of what the formula or its later type/row instantiations say. -/
theorem emit_reindex (embedding : Fin n → Fin m) (injective : Function.Injective embedding)
    (history : List (Observation n Key)) (formula : Inference.Formula α) :
    AnnotationSnapshots.emit (history.map (reindexObservation embedding)) formula =
      AnnotationSnapshots.emit history formula := by
  simp only [AnnotationSnapshots.emit, checkHistory_reindex embedding injective]

namespace Examples

def oldScope : Fin 1 := 0
def onlyIO : Nat → Bool := fun key => key == 0

/-- An explicit visible key and a protected tail can share key 0. The supplied
tail below also contains a negative weight for another key. -/
def row : RowExpr Nat (Fin 1) Nat :=
  .residual [0] (.union (.head 0) (.protect oldScope allowNone (.var 0)))

def rows : Nat → Row 1 Nat := fun _ => [raw 0, release oldScope allowNone (raw 1)]

theorem fresh_origin_for_mixed_tail (occurrence : Occurrence 2 Nat)
    (member : List.Mem occurrence ((liftRow row).eval (signedAlgebra 2 Nat)
      (liftEnvironment rows))) :
    occurrence.weights FreshBoundaries.fresh = 0 := fresh_eval_zero row rows occurrence member

def rejected : TrackedRow 1 Nat Nat :=
  (⟨.head 1, []⟩ : TrackedRow 1 Nat Nat).annotate onlyIO

theorem prior_rejection_survives_fresh_allocation :
    AnnotationSnapshots.checkHistory (reindexTracked Fin.succ rejected).history = false := by
  rw [reindexTracked, checkHistory_reindex Fin.succ FreshBoundaries.succ_injective]
  decide

def acceptedUnknown : TrackedRow 1 Nat Nat :=
  (⟨.var 0, []⟩ : TrackedRow 1 Nat Nat).annotate onlyIO

def laterConcrete : TrackedRow 1 Nat Nat := acceptedUnknown.subst (fun _ => .head 1)

theorem later_substitution_does_not_recheck :
    AnnotationSnapshots.checkHistory
      (reindexTracked Fin.succ laterConcrete).history = true := by
  rw [reindexTracked, checkHistory_reindex Fin.succ FreshBoundaries.succ_injective]
  decide

theorem reobserving_the_later_row_would_reject :
    (AnnotationSnapshots.observe onlyIO
      (reindexTracked Fin.succ laterConcrete).row).check = false := by
  change (AnnotationSnapshots.observe onlyIO (mapScopes Fin.succ laterConcrete.row)).check = false
  rw [observe_check_mapScopes Fin.succ FreshBoundaries.succ_injective]
  decide

end Examples

end Yulang.FreshRowInference
