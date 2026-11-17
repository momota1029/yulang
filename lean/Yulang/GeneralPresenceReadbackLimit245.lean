import Yulang.GeneralPresenceReadback245

/-! The bare Model signature does not impose reflexive subtyping. This closed
example explains the explicit reflexivity premise in the readback block law.
It is a limitation of that abstract lemma, not a source-language counterexample
or a claim about the intended semantic models. -/
namespace Yulang.GeneralPresenceReadbackLimit245
open Core.PresenceGeneration
open PresenceNormalForm
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOwnerRewrite244
open GeneralPresenceCrossRead244 GeneralPresenceOwnerTable244
open GeneralPresenceReadback245

def falseModel : Model where
  Ty := Unit
  Row := Unit
  base := fun _ => ()
  bottom := ()
  top := ()
  union := fun _ _ => ()
  inter := fun _ _ => ()
  pair := fun _ _ => ()
  emptyRecord := ()
  record := fun _ _ _ => ()
  variant := fun _ _ => ()
  arrow := fun _ _ _ _ => ()
  empty := ()
  join := fun _ _ => ()
  subTy := fun _ _ => False
  subRow := fun _ _ => True
  exactEmpty := ()
  required := fun _ _ => ()
  recordDefault := fun _ _ _ => ()

def old : State Nat Nat where
  base := []
  owners := [0]
  entries := fun _ => [(2,.bottom)]

def assignment : Nat → Comp falseModel := fun _ => ((),())

theorem old_external : External (old.entries 0) := by
  simp [old, External, CrossRead, Avoid, GeneralPresenceSubstitutionSupport244.typeSources]

theorem old_coherent : Coherent (old.entries 0) := by
  simp [old, Coherent]

theorem selected_present : 0 ∈ old.owners := by decide

theorem disjoint_other : ∀ other ∈ old.owners, other ≠ 0 →
    DisjointTargets (old.entries 0) (old.entries other) := by
  intro other member different
  have same : other = 0 := by simpa [old] using member
  exact False.elim (different same)

theorem new_models : Models (rebase old 0 []) falseModel assignment := by
  constructor
  · simp [rebase, old, All]
  · intro owner member
    have same : owner = 0 := by simpa [rebase, old] using member
    subst owner
    simp [rebase_at, block, All]

theorem old_has_no_models (values : Nat → Comp falseModel) :
    ¬ Models old falseModel values := by
  intro valid
  have held := valid.2 0 selected_present
  have impossible := held (.tyLe (.var 2) .bottom) (by simp [old, block, equations])
  exact impossible

theorem readback_not_old_models :
    ¬ Models old falseModel (readback (old.entries 0) falseModel assignment) :=
  old_has_no_models _

theorem not_reflexive : ¬ (∀ value, falseModel.subTy value value) := by
  intro assumed
  exact assumed ()

end Yulang.GeneralPresenceReadbackLimit245
