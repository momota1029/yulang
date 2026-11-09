import Yulang.CommonRoleDirectedBounds

/-! Executable certificates for contradictory directed scalar bounds.
Absence of this certificate does not establish satisfiability. -/
namespace Yulang.CommonRoleDirectedConflicts
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All)
open CommonRoleSettledConstraints (State)
open CommonRoleDirectedBounds

/-- Independent scalar conflict, not a general inconsistency judgment. -/
def Conflict (s : State n) : Prop :=
  ∃ i : Fin n, ∃ lo hi : Inference.Base,
    Derived s (false,i,lo) ∧ Derived s (true,i,hi) ∧ lo ≠ hi

/-- Finite search over lower facts, then upper facts at the same slot. -/
def check (s : State n) : Bool :=
  (saturate s).any fun l => (saturate s).any fun u =>
    !l.1 && u.1 && (l.2.1 == u.2.1) && !(l.2.2 == u.2.2)

theorem check_exact (s : State n) : check s = true ↔ Conflict s := by
  simp only [check, List.any_eq_true, Bool.and_eq_true,
    beq_iff_eq]
  constructor
  · rintro ⟨⟨ls,i,lo⟩,hl,⟨us,j,hi⟩,hu,⟨⟨⟨hls,hus⟩,hij⟩,hne⟩⟩
    cases ls <;> cases us <;> simp_all
    subst j
    exact ⟨i,lo,hi,(saturate_exact ..).mp hl,(saturate_exact ..).mp hu,hne⟩
  · rintro ⟨i,lo,hi,hl,hu,hne⟩
    exact ⟨(false,i,lo),(saturate_exact ..).mpr hl,
      (true,i,hi),(saturate_exact ..).mpr hu,by simp [hne]⟩

theorem conflict_no_model (s : State n) (conflict : Conflict s)
    (a : Fin n → Comp Common.model) : ¬ All Common.model a s.atoms := by
  rintro models
  obtain ⟨i,lo,hi,hl,hu,hne⟩ := conflict
  have lower := derived_models s _ hl a models
  have upper := derived_models s _ hu a models
  exact hne ((CommonRigidHeadInspection.base_iff lo hi).mp
    (Common.subtype_trans lower upper))

theorem checked_no_model (s : State n) (found : check s = true)
    (a : Fin n → Comp Common.model) : ¬ All Common.model a s.atoms :=
  conflict_no_model s ((check_exact s).mp found) a

theorem model_check_false (s : State n) (a : Fin n → Comp Common.model)
    (models : All Common.model a s.atoms) : check s = false := by
  cases h : check s
  · rfl
  · exact False.elim (checked_no_model s h a models)

theorem normalize_conflict (s : State n) : Conflict (normalize s) ↔ Conflict s := by
  simp only [Conflict, normalize_derived]

theorem normalize_check (s : State n) : check (normalize s) = check s := by
  apply Bool.eq_iff_iff.mpr
  rw [check_exact, check_exact, normalize_conflict]

end Yulang.CommonRoleDirectedConflicts
