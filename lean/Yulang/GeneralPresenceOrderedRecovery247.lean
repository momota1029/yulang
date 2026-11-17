import Yulang.GeneralPresenceOrderedBlock247
import Yulang.GeneralPresenceModelCongruence245

/-! Re-evaluating an already satisfied actual definition block preserves its
model up to mutual subtyping, even without SafeOrder. This does not construct
an initial model for a cyclic block or produce an actual source ordering. -/
namespace Yulang.GeneralPresenceOrderedRecovery247
open Core.PresenceGeneration PresenceNormalForm
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOrderedBlock247
open GeneralPresenceModelCongruence245
variable {Name : Type} [DecidableEq Name]

theorem put_compatible (model : Model) (laws : Laws model)
    (assignment : Name → Comp model) (target : Name) (value : model.Ty)
    (same : Equiv model value (assignment target).1) :
    Compatible model (put model assignment target value) assignment := by
  intro name
  refine ⟨?_,put_rows model assignment target value name⟩
  by_cases hit : name = target
  · subst name
    simpa [put] using same
  · simp only [put,hit,ite_false]
    exact tyEq_refl laws _

omit [DecidableEq Name] in
theorem compatible_trans (model : Model) (laws : Laws model)
    (first middle last : Name → Comp model)
    (before : Compatible model first middle) (after : Compatible model middle last) :
    Compatible model first last := fun name =>
  ⟨tyEq_trans laws (before name).1 (after name).1, (before name).2.trans (after name).2⟩

theorem solve_compatible (model : Model) (laws : Laws model)
    (entries : List (Entry Name)) (assignment : Name → Comp model)
    (valid : All model assignment (block entries)) :
    Compatible model (solve model entries assignment) assignment := by
  induction entries generalizing assignment with
  | nil => exact fun name => ⟨tyEq_refl laws _,rfl⟩
  | cons entry rest ih =>
    have split : All model assignment (equations entry.1 entry.2) ∧
        All model assignment (block rest) := (all_append model assignment _ _).mp valid
    have forward : model.subTy (assignment entry.1).1 (entry.2.eval model assignment) :=
      split.1 (.tyLe (.var entry.1) entry.2) (by simp [equations])
    have backward : model.subTy (entry.2.eval model assignment) (assignment entry.1).1 :=
      split.1 (.tyLe entry.2 (.var entry.1)) (by simp [equations])
    have step := put_compatible model laws assignment entry.1 (entry.2.eval model assignment)
      ⟨backward,forward⟩
    have tailValid : All model (put model assignment entry.1 (entry.2.eval model assignment))
        (block rest) := (all_iff laws step (block rest)).mpr split.2
    exact compatible_trans model laws _ _ _ (ih _ tailValid) step

theorem all_recovered (model : Model) (laws : Laws model)
    (entries : List (Entry Name)) (assignment : Name → Comp model)
    (valid : All model assignment (block entries)) (atoms : List (Atom Name)) :
    All model (solve model entries assignment) atoms ↔ All model assignment atoms :=
  all_iff laws (solve_compatible model laws entries assignment valid) atoms

theorem block_recovered (model : Model) (laws : Laws model)
    (entries : List (Entry Name)) (assignment : Name → Comp model)
    (valid : All model assignment (block entries)) :
    All model (solve model entries assignment) (block entries) :=
  (all_recovered model laws entries assignment valid (block entries)).mpr valid

end Yulang.GeneralPresenceOrderedRecovery247
