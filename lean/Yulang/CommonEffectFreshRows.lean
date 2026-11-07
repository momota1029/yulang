import Yulang.CommonEffectRequestGeneration

/-! A fresh boundary coordinate for arbitrary Common rows. Inserting an
explicit leading coordinate retains every old signed weight, including
negative debt and heterogeneous/empty coordinate lists. This is a proved
embedding with a retraction, not an identification with padded original rows.
Source/type-boundary elaboration and solver support for this insertion remain
separate from these row laws. -/
namespace Yulang.CommonEffectFreshRows
open Common (Occurrence Row)
open CommonEffectRequestGeneration (Permission)
open CommonSignedRows (Capturable commonResidual shiftOccurrence)

def liftOccurrence (occurrence : Occurrence) : Occurrence := (occurrence.1, 0 :: occurrence.2)

def enterOccurrence (permission : Permission) (occurrence : Occurrence) : Occurrence :=
  (occurrence.1, (if permission.allows occurrence.1 then 0 else 1) :: occurrence.2)

theorem lift_injective : Function.Injective liftOccurrence := by
  intro first last same
  have key := congrArg (fun occurrence : Occurrence => occurrence.1) same
  have weights := congrArg (fun occurrence : Occurrence => occurrence.2) same
  exact Prod.ext key (List.cons.inj weights).2

theorem enter_injective (permission : Permission) : Function.Injective (enterOccurrence permission) := by
  intro first last same
  have key := congrArg (fun occurrence : Occurrence => occurrence.1) same
  have weights := congrArg (fun occurrence : Occurrence => occurrence.2) same
  exact Prod.ext key (List.cons.inj weights).2

@[simp] theorem enter_key (permission : Permission) (occurrence : Occurrence) :
    (enterOccurrence permission occurrence).1 = occurrence.1 := rfl

@[simp] theorem enter_old_weights (permission : Permission) (occurrence : Occurrence) :
    (enterOccurrence permission occurrence).2.tail = occurrence.2 := rfl

theorem enter_capture_iff (permission : Permission) (handled : List Nat) (occurrence : Occurrence) :
    Capturable handled (enterOccurrence permission occurrence) ↔
      Capturable handled occurrence ∧ permission.allows occurrence.1 = true := by
  cases allowed : permission.allows occurrence.1 <;>
    simp [Capturable, enterOccurrence, allowed]

theorem lift_shift (scope : Nat) (permission : Permission) (delta : Int) (occurrence : Occurrence) :
    liftOccurrence (shiftOccurrence scope permission.allows delta occurrence) =
      shiftOccurrence (scope + 1) permission.allows delta (liftOccurrence occurrence) := by
  apply Prod.ext
  · rfl
  apply List.ext_getElem
  · simp [liftOccurrence, shiftOccurrence]
  · intro index hi hj
    cases index with
    | zero => simp [liftOccurrence, shiftOccurrence]
    | succ index => simp [liftOccurrence, shiftOccurrence]

theorem enter_shift (permission : Permission) (occurrence : Occurrence) :
    enterOccurrence permission occurrence = shiftOccurrence 0 permission.allows 1 (liftOccurrence occurrence) := by
  apply Prod.ext
  · rfl
  apply List.ext_getElem
  · simp [enterOccurrence, liftOccurrence, shiftOccurrence]
  · intro index hi hj
    cases index with
    | zero => cases allowed : permission.allows occurrence.1 <;> simp [enterOccurrence, liftOccurrence, shiftOccurrence, allowed]
    | succ index => simp [enterOccurrence, liftOccurrence, shiftOccurrence]

def liftRow (row : Row) : Row := fun occurrence => ∃ original, row original ∧ liftOccurrence original = occurrence
def enterRow (permission : Permission) (row : Row) : Row :=
  fun occurrence => ∃ original, row original ∧ enterOccurrence permission original = occurrence

def exitRow (permission : Permission) (row : Row) : Row := fun original => row (enterOccurrence permission original)

theorem exit_enter (permission : Permission) (row : Row) : exitRow permission (enterRow permission row) = row := by
  funext occurrence
  apply propext
  constructor
  · rintro ⟨original, member, same⟩
    exact enter_injective permission same ▸ member
  · intro member
    exact ⟨occurrence, member, rfl⟩

theorem enter_protect (permission : Permission) (row : Row) :
    enterRow permission row = CommonSignedRows.commonProtect 0 permission.allows (liftRow row) := by
  funext occurrence
  apply propext
  change enterRow permission row occurrence ↔ CommonSignedRows.transport 0 permission.allows 1 (liftRow row) occurrence
  rw [CommonSignedRows.transport_member_iff]
  constructor
  · rintro ⟨original, member, same⟩
    exact ⟨liftOccurrence original, ⟨original, member, rfl⟩, (enter_shift permission original).symm.trans same⟩
  · rintro ⟨_, ⟨original, member, rfl⟩, same⟩
    exact ⟨original, member, (enter_shift permission original).trans same⟩

theorem residual_incoming (permission : Permission) (handled : List Nat) (row : Row) :
    commonResidual handled (enterRow permission row) =
      enterRow permission (commonResidual (handled.filter permission.allows) row) := by
  funext occurrence
  apply propext
  constructor
  · rintro ⟨⟨original, member, same⟩, uncaptured⟩
    refine ⟨original, ⟨member, ?_⟩, same⟩
    intro captured
    apply uncaptured
    rw [← same, enter_capture_iff]
    have key := List.mem_filter.mp captured.1
    exact ⟨⟨key.1, captured.2⟩, key.2⟩
  · rintro ⟨original, ⟨member, uncaptured⟩, same⟩
    refine ⟨⟨original, member, same⟩, ?_⟩
    intro captured
    apply uncaptured
    rw [← same, enter_capture_iff] at captured
    exact ⟨List.mem_filter.mpr ⟨captured.1.1, captured.2⟩, captured.1.2⟩

/-- Default callback hygiene, for every arbitrary incoming row and old debt. -/
theorem unannotated_never_subtracted (handled : List Nat) (row : Row) :
    commonResidual handled (enterRow (.only []) row) = enterRow (.only []) row := by
  rw [residual_incoming]
  congr 1
  funext occurrence
  apply propext
  simp [commonResidual, Capturable, Permission.allows]
end Yulang.CommonEffectFreshRows
