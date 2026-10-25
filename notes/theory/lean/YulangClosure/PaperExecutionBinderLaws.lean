import YulangClosure.PaperExecutionSyntax

/-!
Scope-extension laws for universal introduction in the partial paper judgments.
The shift extends the ambient type-variable context by one fresh binder.
-/
namespace YulangClosure.PaperTypes

def shiftTypeSubstitution (index : Nat) : Ty := .var (index + 1)

theorem subst_shiftTypeSubstitution (ty : Ty) :
    subst shiftTypeSubstitution ty = mapVars Nat.succ ty := by
  have h := subst_mapVars idSub Nat.succ ty
  calc
    subst shiftTypeSubstitution ty =
        subst (fun index => Ty.var (index + 1)) ty := rfl
    _ = subst idSub (mapVars Nat.succ ty) := by
      simpa [idSub] using h.symm
    _ = mapVars Nat.succ ty := subst_id _

theorem liftSub_shiftTypeSubstitution_commutes (σ : Nat → Ty) :
    (fun index => liftSub σ (index + 1)) =
      (fun index => subst shiftTypeSubstitution (σ index)) := by
  funext index
  simp [liftSub, subst_shiftTypeSubstitution]

def composeTypeSubstitution (outer inner : Nat → Ty) : Nat → Ty :=
  fun index => subst outer (inner index)

theorem compose_liftSub (outer inner : Nat → Ty) :
    composeTypeSubstitution (liftSub outer) (liftSub inner) =
      liftSub (composeTypeSubstitution outer inner) := by
  funext index
  exact congrFun (liftSub_comp inner outer) index

theorem liftSubN_shift_compose (depth : Nat) (σ : Nat → Ty) :
    composeTypeSubstitution (liftSubN depth (liftSub σ))
        (liftSubN depth shiftTypeSubstitution) =
      composeTypeSubstitution (liftSubN depth shiftTypeSubstitution)
        (liftSubN depth σ) := by
  induction depth with
  | zero =>
      funext index
      exact congrFun (liftSub_shiftTypeSubstitution_commutes σ) index
  | succ depth ih =>
      simp only [liftSubN]
      rw [compose_liftSub, compose_liftSub, ih]

@[simp] theorem subst_liftSubN_shift_commutes
    (depth : Nat) (σ : Nat → Ty) (ty : Ty) :
    subst (liftSubN depth (liftSub σ))
        (subst (liftSubN depth shiftTypeSubstitution) ty) =
      subst (liftSubN depth shiftTypeSubstitution)
        (subst (liftSubN depth σ) ty) := by
  rw [subst_comp, subst_comp]
  exact congrArg (fun substitution => subst substitution ty)
    (liftSubN_shift_compose depth σ)

theorem liftSubN_add (outerDepth innerDepth : Nat) (σ : Nat → Ty) :
    liftSubN outerDepth (liftSubN innerDepth σ) =
      liftSubN (innerDepth + outerDepth) σ := by
  induction outerDepth with
  | zero => simp [liftSubN]
  | succ outerDepth ih =>
      simp only [liftSubN]
      rw [ih]
      simp [liftSubN, Nat.add_assoc]

theorem mapTypeEnvironment_shift_substitution_commutes
    (σ : Nat → Ty) (environment : TypeEnvironment) :
    mapTypeEnvironment (liftSub σ)
        (mapTypeEnvironment shiftTypeSubstitution environment) =
      mapTypeEnvironment shiftTypeSubstitution
        (mapTypeEnvironment σ environment) := by
  simp only [mapTypeEnvironment, List.map_map]
  apply List.map_congr_left
  intro ty _
  change subst (liftSub σ) (subst shiftTypeSubstitution ty) =
    subst shiftTypeSubstitution (subst σ ty)
  rw [subst_comp, subst_comp]
  congr 1
  funext index
  exact congrFun (liftSub_shiftTypeSubstitution_commutes σ) index

theorem mapGraphEnvironment_shift_substitution_commutes
    (σ : Nat → Ty) (environment : GraphEnvironment) :
    mapGraphEnvironment (liftSub σ)
        (mapGraphEnvironment shiftTypeSubstitution environment) =
      mapGraphEnvironment shiftTypeSubstitution
        (mapGraphEnvironment σ environment) := by
  simp only [mapGraphEnvironment, List.map_map]
  apply List.map_congr_left
  intro entry _
  rcases entry with ⟨identity, ty⟩
  change (identity, subst (liftSub σ) (subst shiftTypeSubstitution ty)) =
    (identity, subst shiftTypeSubstitution (subst σ ty))
  congr 1
  change subst (liftSub σ) (subst shiftTypeSubstitution ty) =
    subst shiftTypeSubstitution (subst σ ty)
  rw [subst_comp, subst_comp]
  congr 1
  funext index
  exact congrFun (liftSub_shiftTypeSubstitution_commutes σ) index


end YulangClosure.PaperTypes
