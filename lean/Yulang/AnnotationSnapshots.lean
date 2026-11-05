import Yulang.Annotations
import Yulang.RowInference

/-!
# Frozen positive-annotation observations, including signed rows

T3 (2026-11-05) checks concrete effects visible at the observation site. An
unknown row later instantiated through a generalized scheme is not rechecked.
This module makes that temporal distinction explicit: a row expression can be
substituted, while the finite history of observations retains its original
signed concrete rows. A failed earlier observation also cannot be repaired by
a later substitution or by adding protection afterwards.

`observe` expects the row expression at the current inference stage: any
already-known substitutions must have been applied before taking the snapshot.
Its unresolved variables are opaque. The theorem does not claim a solver that
decides when a variable becomes known, or source annotation elaboration.

`principal_observed_exact` connects this check to the existing principal
constraint generator. Valid snapshots add no row equation or permission bound
to the later instantiation; invalid snapshots reject every instantiation.
-/

namespace Yulang.AnnotationSnapshots

open Inference
open RowInference (RowExpr signedAlgebra)

def Visible (occurrence : Directed.Occurrence n Key) : Prop :=
  ∀ scope, occurrence.weights scope = 0

instance (occurrence : Directed.Occurrence n Key) : Decidable (Visible occurrence) :=
  inferInstanceAs (Decidable (∀ scope, occurrence.weights scope = 0))

structure Observation (n : Nat) (Key : Type) where
  permission : Key → Bool
  concrete : Directed.Row n Key

def Observation.Admissible (observation : Observation n Key) : Prop :=
  ∀ occurrence ∈ observation.concrete,
    Visible occurrence → observation.permission occurrence.key = true

def Observation.check (observation : Observation n Key) : Bool :=
  observation.concrete.all fun occurrence =>
    decide (Visible occurrence → observation.permission occurrence.key = true)

theorem Observation.check_exact (observation : Observation n Key) :
    observation.check = true ↔ observation.Admissible := by
  simp only [check, List.all_eq_true, decide_eq_true_eq, Admissible]

/-- Unknown slots contribute no concrete occurrence to this observation only. -/
def known [DecidableEq Key] (row : RowExpr Key (Fin n) α) : Directed.Row n Key :=
  row.eval (signedAlgebra n Key) (fun _ => [])

def observe [DecidableEq Key] (permission : Key → Bool) (row : RowExpr Key (Fin n) α) :
    Observation n Key := ⟨permission, known row⟩

structure TrackedRow (n : Nat) (Key α : Type) where
  row : RowExpr Key (Fin n) α
  history : List (Observation n Key)

/-- Taking a snapshot is distinct from substituting the row. -/
def TrackedRow.annotate [DecidableEq Key] (tracked : TrackedRow n Key α)
    (permission : Key → Bool) : TrackedRow n Key α :=
  ⟨tracked.row, observe permission tracked.row :: tracked.history⟩

def TrackedRow.subst (tracked : TrackedRow n Key α) (σ : α → RowExpr Key (Fin n) β) :
    TrackedRow n Key β := ⟨tracked.row.subst σ, tracked.history⟩

def HistoryAdmissible (history : List (Observation n Key)) : Prop :=
  ∀ observation ∈ history, observation.Admissible

def checkHistory (history : List (Observation n Key)) : Bool :=
  history.all Observation.check

theorem checkHistory_exact (history : List (Observation n Key)) :
    checkHistory history = true ↔ HistoryAdmissible history := by
  simp only [checkHistory, HistoryAdmissible, List.all_eq_true, Observation.check_exact]

theorem annotation_exact [DecidableEq Key] (tracked : TrackedRow n Key α)
    (permission : Key → Bool) :
    checkHistory (tracked.annotate permission).history = true ↔
      (observe permission tracked.row).Admissible ∧ HistoryAdmissible tracked.history := by
  simp [TrackedRow.annotate, checkHistory_exact, HistoryAdmissible]

/-- This is a property of retained observation history, not an extensional
substitution-invariance assertion about newly observed row expressions. -/
theorem instantiation_keeps_observation (tracked : TrackedRow n Key α)
    (σ : α → RowExpr Key (Fin n) β) :
    checkHistory (tracked.subst σ).history = checkHistory tracked.history := rfl

theorem instantiated_row_meaning [DecidableEq Key] (tracked : TrackedRow n Key α)
    (σ : α → RowExpr Key (Fin n) β) (ρ : β → Directed.Row n Key) :
    (tracked.subst σ).row.eval (signedAlgebra n Key) ρ =
      tracked.row.eval (signedAlgebra n Key)
        (fun name => (σ name).eval (signedAlgebra n Key) ρ) :=
  RowExpr.eval_subst _ _ _ _

/-- Positive observations are closed checks, not constraints on future rows. -/
def emit (history : List (Observation n Key)) (formula : Formula α) : Formula α :=
  if checkHistory history then formula else .bot

theorem emit_exact (history : List (Observation n Key)) (formula : Formula α)
    (m : Model) (ρ : α → Comp m) :
    (emit history formula).Holds m ρ ↔ HistoryAdmissible history ∧ formula.Holds m ρ := by
  cases checked : checkHistory history with
  | false =>
    have invalid : ¬ HistoryAdmissible history := by
      intro valid
      rw [(checkHistory_exact history).mpr valid] at checked
      cases checked
    simp [emit, checked, invalid, Formula.Holds]
  | true =>
    have valid := (checkHistory_exact history).mp checked
    simp [emit, checked, valid]

theorem emit_subst (history : List (Observation n Key)) (formula : Formula α)
    (σ : α → CompTerm β) :
    (emit history formula).subst σ = emit history (formula.subst σ) := by
  cases checked : checkHistory history <;> simp [emit, checked, Formula.subst]

/-- Exactness of the observed principal scheme for every result type and row.
Its environment condition is the same one as the existing principal theorem. -/
theorem principal_observed_exact (history : List (Observation n Key))
    (m : Model) (ρ : α → Comp m) (sΓ : SchemeEnv α) (Γ : List (Binding m))
    (environment : EnvRel m ρ sΓ Γ) (expression : Expr) (result : Comp m) :
    (emit history (principal sΓ expression)).Holds m (extend ρ result) ↔
      HistoryAdmissible history ∧ Typing m Γ expression result := by
  rw [emit_exact, principal_exact m expression sΓ Γ ρ environment result]

theorem valid_observation_adds_no_instantiation_bound (history : List (Observation n Key))
    (valid : HistoryAdmissible history) (formula : Formula α)
    (σ : α → CompTerm β) (m : Model) (ρ : β → Comp m) :
    ((emit history formula).subst σ).Holds m ρ ↔
      formula.Holds m (fun name => (σ name).eval m ρ) := by
  rw [emit_subst, emit_exact, Formula.holds_subst]
  exact and_iff_right valid

theorem invalid_observation_rejects_all_instantiations (history : List (Observation n Key))
    (invalid : ¬ HistoryAdmissible history) (formula : Formula α)
    (σ : α → CompTerm β) (m : Model) (ρ : β → Comp m) :
    ¬ ((emit history formula).subst σ).Holds m ρ := by
  rw [emit_subst, emit_exact]
  exact fun held => invalid held.1

theorem opaque_allowed [DecidableEq Key] (permission : Key → Bool) (name : α) :
    (observe permission (RowExpr.var name : RowExpr Key (Fin n) α)).check = true := rfl

theorem known_forbidden_rejected [DecidableEq Key] (permission : Key → Bool) (key : Key)
    (denied : permission key = false) :
    (observe permission (RowExpr.head key : RowExpr Key (Fin n) α)).check = false := by
  simp [observe, known, Observation.check, RowExpr.eval, signedAlgebra, Visible,
    Directed.raw, denied]

theorem release_protect_observation [DecidableEq Key] (scope : Fin n) (mask permission : Key → Bool)
    (row : RowExpr Key (Fin n) α) :
    observe permission (.release scope mask (.protect scope mask row)) =
      observe permission row := by
  unfold observe known
  rw [RowInference.signed_eval_release_protect]

namespace Examples

def onlyIO : Nat → Bool := fun key => key == 0

def initiallyUnknown : TrackedRow 1 Nat Nat := ⟨.var 0, []⟩

def recorded : TrackedRow 1 Nat Nat := initiallyUnknown.annotate onlyIO

def laterConcrete : TrackedRow 1 Nat Nat := recorded.subst (fun _ => .head 1)

theorem t3_initial_observation_accepts : checkHistory recorded.history = true := by decide

theorem t3_later_instantiation_accepts : checkHistory laterConcrete.history = true := by decide

theorem t3_new_observation_would_reject : (observe onlyIO laterConcrete.row).check = false := by
  decide

theorem t3_known_head_cannot_hide_behind_unknown_tail :
    (observe onlyIO (.union (.head 1) (.var 0) : RowExpr Nat (Fin 1) Nat)).check = false := by
  decide

theorem protected_known_head_is_not_visible :
    (observe onlyIO (.protect 0 Directed.allowNone (.head 1) : RowExpr Nat (Fin 1) Nat)).check =
      true := by decide

theorem released_known_head_becomes_visible :
    (observe onlyIO (.release 0 Directed.allowNone (.protect 0 Directed.allowNone (.head 1)) :
      RowExpr Nat (Fin 1) Nat)).check = false := by decide

end Examples
end Yulang.AnnotationSnapshots
