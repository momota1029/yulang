import Yulang.CommonRoleCanonicalRows
import Yulang.CommonRoleIntervalGeneration

/-!
# Canonical record subtraction preserves both interval endpoints

This component starts from a determined finite record spine whose visible
payloads carry lower/upper terms. It computes the actual first-field-wins
residual, rather than solving a masked equation by an arbitrary substitution.
Unknown spines do not enter this operation. No actual argument or centre is
stored, and no declaration-variance decision is made here.
-/

namespace Yulang.CommonRoleIntervalRecordResidual

open Core.PresenceGeneration (TyTerm Comp)
open CommonRoleCanonicalRows (Row normalize residual capture)
open CommonRoleIntervals (Interval Fits Valid evaluate)
open CommonRoleIntervalGeneration (Argument)
open PresenceNormalForm (Atom All)

def mapPayload (f : Payload → Other) (row : Row Payload) : Row Other :=
  row.map (fun entry => (entry.1, f entry.2))

theorem normalize_map (f : Payload → Other) (row : Row Payload) :
    normalize (mapPayload f row) = mapPayload f (normalize row) := by
  induction row with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨label, payload⟩
      simp only [mapPayload, List.map_cons, normalize] at *
      rw [ih, CommonRoleCanonicalRows.residual_map]

/-- Subtraction acts on labels only; it neither fixes an argument point nor
replaces one endpoint with the other. This includes hidden duplicate fields. -/
theorem capture_map (labels : List Nat) (f : Payload → Other) (row : Row Payload) :
    capture labels (mapPayload f row) = mapPayload f (capture labels row) := by
  unfold capture
  rw [normalize_map]
  exact CommonRoleCanonicalRows.residual_map labels f (normalize row)

abbrev Fields (α : Type) := Row (Argument α)

def lowerFields (fields : Fields α) : Row (TyTerm α) := mapPayload Prod.fst fields
def upperFields (fields : Fields α) : Row (TyTerm α) := mapPayload Prod.snd fields

/-- Both endpoints are computed from the SAME canonical source residual. -/
theorem residual_endpoints (labels : List Nat) (fields : Fields α) :
    lowerFields (capture labels fields) = capture labels (lowerFields fields) ∧
      upperFields (capture labels fields) = capture labels (upperFields fields) :=
  ⟨(capture_map labels Prod.fst fields).symm,
    (capture_map labels Prod.snd fields).symm⟩

end Yulang.CommonRoleIntervalRecordResidual
