import Yulang.SemanticRecordVarianceBoundary

/-!
# The former local variance example satisfies rigid-demand covariance

Decision 39 only requires covariance toward a rigid demanded tail. In the
finite field-presence algebra from `SemanticRecordVarianceBoundary`, proper
record tails are the principal upper sets of required fields. Every operation
satisfying the stated local laws is covariant toward these tails: the existing
head and known-field guarantees already imply this restricted comparison.

The old failed comparison has a nonprincipal demanded union, so it does not
contradict the newly selected restricted law. This remains a statement about
the explicitly defined local field-presence algebra, not a model of all
Yulang payload types, values or source programs.
-/

namespace Yulang.RigidRecordVarianceBoundary

open SemanticRecordVarianceBoundary

/-- The local counterpart of decision 39. Principal tails are the semantic
proper-record types in this three-field observation algebra. -/
def RigidTailCovariant (operation : Field → Ty → Ty) : Prop :=
  ∀ field left right, IsPrincipal right → Le left right →
    Le (operation field left) (operation field right)

/-- For every operation satisfying all the listed local laws, covariance
toward every principal demanded tail follows from head and field presence. -/
theorem local_laws_rigid_covariant (operation : Field → Ty → Ty)
    (laws : LocalRecordLaws operation) : RigidTailCovariant operation := by
  intro field left right shape below
  obtain ⟨required, rfl⟩ := shape
  rw [laws.proper]
  intro actual present name demanded
  by_cases same : name = field
  · subst name
    exact (principal_singleton field actual).mp (laws.head field left actual present)
  · have requiredField : required name = true := by
      simpa [SemanticRecordVarianceBoundary.insert, same] using demanded
    exact laws.knownFields field left required below actual present name requiredField

theorem extend_rigid_covariant : RigidTailCovariant extend :=
  local_laws_rigid_covariant extend local_record_laws

/-- The demanded union in the old counterexample is not a rigid tail. -/
theorem counterexample_target_not_rigid : ¬ IsPrincipal rightTail :=
  rightTail_not_principal

/-- The same local algebra satisfies the selected restricted law while
still refuting unrestricted tail covariance. No language-wide independence
claim is made by this existential statement. -/
theorem local_laws_with_rigid_without_general_covariance :
    ∃ operation : Field → Ty → Ty,
      LocalRecordLaws operation ∧ RigidTailCovariant operation ∧ ¬ TailCovariant operation :=
  ⟨extend, local_record_laws, extend_rigid_covariant, not_tail_covariant⟩

end Yulang.RigidRecordVarianceBoundary
