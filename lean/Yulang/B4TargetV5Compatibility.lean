import Yulang.B4TargetV5

/-! Fidelity checks for I-25: only Initial restricts the public input domain.
These implications do not prove either target for the concrete source boundary. -/
namespace Yulang.B4TargetV5Compatibility
open B4Target (Vocabulary)
open B4TargetV3 (Executor)
open B4TargetV5 (SourceBoundary)
universe u
variable {v : Vocabulary.{u}}

/-- Any old all-state solution restricts to the chosen initial states, without
adding a model, success or second-registry Initial premise. -/
theorem restrict_statement (b : SourceBoundary v) (e : Executor v)
    (old : B4TargetV3.Statement b.toSourceBoundary e) : B4TargetV5.Statement b e := by
  obtain ⟨total,exact,order,sound,reject⟩ := old
  exact ⟨fun r checked s d _ => total r checked s d,
    fun r checked s d tree _ => exact r checked s d tree,
    fun r r' checked checked' reorder s d _ => order r r' checked checked' reorder s d,
    fun r checked s d dictionary _ => sound r checked s d dictionary,
    fun r checked s d _ => reject r checked s d⟩

/-- If every input is initial, V5 recovers every V3 conclusion. This is a
comparison theorem, not an assumption supplied to the concrete V5 proof. -/
theorem unrestrict_statement (b : SourceBoundary v) (e : Executor v)
    (allInitial : ∀ r d s, b.Initial r d s)
    (current : B4TargetV5.Statement b e) : B4TargetV3.Statement b.toSourceBoundary e := by
  obtain ⟨total,exact,order,sound,reject⟩ := current
  exact ⟨fun r checked s d => total r checked s d (allInitial r d s),
    fun r checked s d tree => exact r checked s d tree (allInitial r d s),
    fun r r' checked checked' reorder s d => order r r' checked checked' reorder s d (allInitial r d s),
    fun r checked s d dictionary => sound r checked s d dictionary (allInitial r d s),
    fun r checked s d => reject r checked s d (allInitial r d s)⟩

/-- Exact compatibility when the restriction is universal. -/
theorem universal_initial_iff (b : SourceBoundary v) (e : Executor v)
    (allInitial : ∀ r d s, b.Initial r d s) :
    B4TargetV5.Statement b e ↔ B4TargetV3.Statement b.toSourceBoundary e :=
  ⟨unrestrict_statement b e allInitial,restrict_statement b e⟩

end Yulang.B4TargetV5Compatibility
