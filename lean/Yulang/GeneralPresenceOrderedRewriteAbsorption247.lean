import Yulang.GeneralPresenceOrderedSubstitution247
import Yulang.GeneralPresenceOrderedDependence247
/-! Semantic compression for successive finite textual substitutions. The result
is exact in every model, without subtype laws, but is not literal syntax equality
or a size bound on the rewritten terms. It does not supply a source ordering. -/
namespace Yulang.GeneralPresenceOrderedRewriteAbsorption247
open Core.PresenceGeneration PresenceNormalForm
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOrderedBlock247
open GeneralPresenceOrderedSubstitution247 GeneralPresenceOrderedDependence247
variable {Name : Type} [DecidableEq Name]

theorem rewrite_append (entries : List (Entry Name)) (first last : List (Atom Name)) :
 rewrite entries (first ++ last) = rewrite entries first ++ rewrite entries last := by
 simp only [rewrite,List.map_append]

theorem nested_absorbs (model : Model) (old fresh : List (Entry Name))
 (safe : SafeOrder old) (within : TargetsWithin fresh old)
 (atoms : List (Atom Name)) (assignment : Name → Comp model) :
 All model assignment (rewrite fresh (rewrite old atoms)) ↔
 All model assignment (rewrite old atoms) := by
 rw [rewrite_exact,rewrite_exact,solve_absorbs model old fresh safe within,rewrite_exact]

theorem nested_idempotent (model : Model) (entries : List (Entry Name))
 (safe : SafeOrder entries) (atoms : List (Atom Name)) (assignment : Name → Comp model) :
 All model assignment (rewrite entries (rewrite entries atoms)) ↔
 All model assignment (rewrite entries atoms) :=
 nested_absorbs model entries entries safe (fun entry member => ⟨entry,member,rfl⟩) atoms assignment

theorem assignment_independent (model : Model) (entries : List (Entry Name))
 (safe : SafeOrder entries) (atoms : List (Atom Name)) (first last : Name → Comp model)
 (rows : ∀ name, (first name).2 = (last name).2)
 (outside : ∀ name, (∀ entry ∈ entries, entry.1 ≠ name) → (first name).1 = (last name).1) :
 All model first (rewrite entries atoms) ↔ All model last (rewrite entries atoms) := by
 rw [rewrite_exact,rewrite_exact,solve_equal model entries safe first last rows outside]
end Yulang.GeneralPresenceOrderedRewriteAbsorption247
