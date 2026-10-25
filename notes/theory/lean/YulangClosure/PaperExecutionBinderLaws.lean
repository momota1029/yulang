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



private theorem mapAdapterMetadata_shift (depth : Nat) (σ : Nat → Ty) (x : AdapterMetadata) :
    mapAdapterMetadata (liftSubN depth (liftSub σ)) (mapAdapterMetadata (liftSubN depth shiftTypeSubstitution) x) =
      mapAdapterMetadata (liftSubN depth shiftTypeSubstitution) (mapAdapterMetadata (liftSubN depth σ) x) := by
  cases x
  simp [mapAdapterMetadata]

private theorem mapViewMetadata_shift (depth : Nat) (σ : Nat → Ty) (x : ViewMetadata) :
    mapViewMetadata (liftSubN depth (liftSub σ)) (mapViewMetadata (liftSubN depth shiftTypeSubstitution) x) =
      mapViewMetadata (liftSubN depth shiftTypeSubstitution) (mapViewMetadata (liftSubN depth σ) x) := by
  cases x
  simp [mapViewMetadata, mapTypeArguments, List.map_map]

private theorem mapOperationInstance_shift (depth : Nat) (σ : Nat → Ty) (x : OperationInstance) :
    (x.subst (liftSubN depth shiftTypeSubstitution)).subst (liftSubN depth (liftSub σ)) =
      (x.subst (liftSubN depth σ)).subst (liftSubN depth shiftTypeSubstitution) := by
  cases x
  simp [OperationInstance.subst]

private theorem mapPaperValue_record_eq (τ : Nat → Ty) (fields : List (Label × Presence × Value)) :
    mapPaperValue τ (.record fields) =
      .record (fields.map fun field => (field.1, field.2.1, mapPaperValue τ field.2.2)) := by
  rw [mapPaperValue]
  congr 1
  exact List.attach_map_val (f := fun (field : Label × Presence × Value) => (field.1, field.2.1, mapPaperValue τ field.2.2))

private theorem mapPaperComputation_recursive_eq (τ : Nat → Ty) (bindings : List (TermName × Value)) (body : Computation) :
    mapPaperComputation τ (.recursive bindings body) =
      .recursive (bindings.map fun binding => (binding.1, mapPaperValue τ binding.2)) (mapPaperComputation τ body) := by
  rw [mapPaperComputation]
  congr 1
  exact List.attach_map_val (f := fun (binding : TermName × Value) => (binding.1, mapPaperValue τ binding.2))

/-- Common size bound for all mutually recursive raw syntax families. -/
private structure ShiftAt (n : Nat) : Prop where
  value : ∀ (x : Value), sizeOf x = n → ∀ (depth : Nat) (σ : Nat → Ty),
    mapPaperValue (liftSubN depth (liftSub σ)) (mapPaperValue (liftSubN depth shiftTypeSubstitution) x) =
      mapPaperValue (liftSubN depth shiftTypeSubstitution) (mapPaperValue (liftSubN depth σ) x)
  computation : ∀ (x : Computation), sizeOf x = n → ∀ (depth : Nat) (σ : Nat → Ty),
    mapPaperComputation (liftSubN depth (liftSub σ)) (mapPaperComputation (liftSubN depth shiftTypeSubstitution) x) =
      mapPaperComputation (liftSubN depth shiftTypeSubstitution) (mapPaperComputation (liftSubN depth σ) x)
  pattern : ∀ (x : PatternPlan), sizeOf x = n → ∀ (depth : Nat) (σ : Nat → Ty),
    mapPaperPattern (liftSubN depth (liftSub σ)) (mapPaperPattern (liftSubN depth shiftTypeSubstitution) x) =
      mapPaperPattern (liftSubN depth shiftTypeSubstitution) (mapPaperPattern (liftSubN depth σ) x)
  constructorBranch : ∀ (x : ConstructorBranch), sizeOf x = n → ∀ (depth : Nat) (σ : Nat → Ty),
    mapConstructorBranch (liftSubN depth (liftSub σ)) (mapConstructorBranch (liftSubN depth shiftTypeSubstitution) x) =
      mapConstructorBranch (liftSubN depth shiftTypeSubstitution) (mapConstructorBranch (liftSubN depth σ) x)
  guardedBranch : ∀ (x : GuardedBranch), sizeOf x = n → ∀ (depth : Nat) (σ : Nat → Ty),
    mapGuardedBranch (liftSubN depth (liftSub σ)) (mapGuardedBranch (liftSubN depth shiftTypeSubstitution) x) =
      mapGuardedBranch (liftSubN depth shiftTypeSubstitution) (mapGuardedBranch (liftSubN depth σ) x)
  valueArm : ∀ (x : ValueArm), sizeOf x = n → ∀ (depth : Nat) (σ : Nat → Ty),
    mapValueArm (liftSubN depth (liftSub σ)) (mapValueArm (liftSubN depth shiftTypeSubstitution) x) =
      mapValueArm (liftSubN depth shiftTypeSubstitution) (mapValueArm (liftSubN depth σ) x)
  operationArm : ∀ (x : OperationArm), sizeOf x = n → ∀ (depth : Nat) (σ : Nat → Ty),
    mapOperationArm (liftSubN depth (liftSub σ)) (mapOperationArm (liftSubN depth shiftTypeSubstitution) x) =
      mapOperationArm (liftSubN depth shiftTypeSubstitution) (mapOperationArm (liftSubN depth σ) x)
  handler : ∀ (x : HandlerPlan), sizeOf x = n → ∀ (depth : Nat) (σ : Nat → Ty),
    mapHandlerPlan (liftSubN depth (liftSub σ)) (mapHandlerPlan (liftSubN depth shiftTypeSubstitution) x) =
      mapHandlerPlan (liftSubN depth shiftTypeSubstitution) (mapHandlerPlan (liftSubN depth σ) x)
  mapper : ∀ (x : MapperPlan), sizeOf x = n → ∀ (depth : Nat) (σ : Nat → Ty),
    mapMapperPlan (liftSubN depth (liftSub σ)) (mapMapperPlan (liftSubN depth shiftTypeSubstitution) x) =
      mapMapperPlan (liftSubN depth shiftTypeSubstitution) (mapMapperPlan (liftSubN depth σ) x)

private theorem shiftAt_all (n : Nat) : ShiftAt n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    have h_value (x : Value) (h : sizeOf x < n) (depth : Nat) (σ : Nat → Ty) :=
      (ih (sizeOf x) h).value x rfl depth σ
    have h_computation (x : Computation) (h : sizeOf x < n) (depth : Nat) (σ : Nat → Ty) :=
      (ih (sizeOf x) h).computation x rfl depth σ
    have h_pattern (x : PatternPlan) (h : sizeOf x < n) (depth : Nat) (σ : Nat → Ty) :=
      (ih (sizeOf x) h).pattern x rfl depth σ
    have h_constructorBranch (x : ConstructorBranch) (h : sizeOf x < n) (depth : Nat) (σ : Nat → Ty) :=
      (ih (sizeOf x) h).constructorBranch x rfl depth σ
    have h_guardedBranch (x : GuardedBranch) (h : sizeOf x < n) (depth : Nat) (σ : Nat → Ty) :=
      (ih (sizeOf x) h).guardedBranch x rfl depth σ
    have h_valueArm (x : ValueArm) (h : sizeOf x < n) (depth : Nat) (σ : Nat → Ty) :=
      (ih (sizeOf x) h).valueArm x rfl depth σ
    have h_operationArm (x : OperationArm) (h : sizeOf x < n) (depth : Nat) (σ : Nat → Ty) :=
      (ih (sizeOf x) h).operationArm x rfl depth σ
    have h_handler (x : HandlerPlan) (h : sizeOf x < n) (depth : Nat) (σ : Nat → Ty) :=
      (ih (sizeOf x) h).handler x rfl depth σ
    have h_mapper (x : MapperPlan) (h : sizeOf x < n) (depth : Nat) (σ : Nat → Ty) :=
      (ih (sizeOf x) h).mapper x rfl depth σ
    constructor
    · intro x hn depth σ
      cases x with
      | typeAbstraction body =>
        have hs : sizeOf body < n := by simp +arith at hn; omega
        simpa only [mapPaperValue, liftSubN] using
          congrArg Value.typeAbstraction (h_value body hs (depth + 1) σ)
      | _ =>
        all_goals
          simp +arith at hn
          simp (config := { contextual := true }) (disch := omega)
            [mapPaperValue, mapPaperComputation, mapPaperPattern, mapConstructorBranch,
              mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
              mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift,
              mapOperationInstance_shift, List.attach_map_val, List.attach_map,
              List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation,
              h_pattern, h_constructorBranch, h_guardedBranch, h_valueArm,
              h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
              mapPaperComputation_recursive_eq]
        all_goals
          repeat' apply And.intro
        all_goals
          first
          | (intro label presence value hmem
             have hsmall := List.sizeOf_lt_of_mem hmem
             simp +arith at hsmall
             exact h_value value (by omega) depth σ)
          | (intro name value hmem
             have hsmall := List.sizeOf_lt_of_mem hmem
             simp +arith at hsmall
             exact h_value value (by omega) depth σ)
          | (intro child hmem
             have hsmall := List.sizeOf_lt_of_mem hmem
             simp (disch := omega) [h_value, h_computation, h_pattern, h_constructorBranch,
               h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper])
    · intro x hn depth σ
      cases x
      all_goals
        simp +arith at hn
        simp (config := { contextual := true }) (disch := omega)
          [mapPaperValue, mapPaperComputation, mapPaperPattern, mapConstructorBranch,
            mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
            mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift,
            mapOperationInstance_shift, List.attach_map_val, List.attach_map,
            List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation,
            h_pattern, h_constructorBranch, h_guardedBranch, h_valueArm,
            h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
            mapPaperComputation_recursive_eq]
      all_goals
        repeat' apply And.intro
      all_goals
        first
        | (intro label presence value hmem
           have hsmall := List.sizeOf_lt_of_mem hmem
           simp +arith at hsmall
           exact h_value value (by omega) depth σ)
        | (intro name value hmem
           have hsmall := List.sizeOf_lt_of_mem hmem
           simp +arith at hsmall
           exact h_value value (by omega) depth σ)
        | (intro child hmem
           have hsmall := List.sizeOf_lt_of_mem hmem
           simp (disch := omega) [h_value, h_computation, h_pattern, h_constructorBranch,
             h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper])
    · intro x hn depth σ
      cases x
      all_goals
        simp +arith at hn
        simp (config := { contextual := true }) (disch := omega)
          [mapPaperValue, mapPaperComputation, mapPaperPattern, mapConstructorBranch,
            mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
            mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift,
            mapOperationInstance_shift, List.attach_map_val, List.attach_map,
            List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation,
            h_pattern, h_constructorBranch, h_guardedBranch, h_valueArm,
            h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
            mapPaperComputation_recursive_eq]
      all_goals
        repeat' apply And.intro
      all_goals
        first
        | (intro label pattern default hmem
           have hsmall := List.sizeOf_lt_of_mem hmem
           cases default <;> simp +arith at hsmall <;>
             simp (disch := omega) [h_pattern, h_computation])
        | (intro child hmem
           have hsmall := List.sizeOf_lt_of_mem hmem
           simp (disch := omega) [h_pattern])
    · intro x hn depth σ
      cases x
      all_goals
        simp +arith at hn
        simp (config := { contextual := true }) (disch := omega)
          [mapPaperValue, mapPaperComputation, mapPaperPattern, mapConstructorBranch,
            mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
            mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift,
            mapOperationInstance_shift, List.attach_map_val, List.attach_map,
            List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation,
            h_pattern, h_constructorBranch, h_guardedBranch, h_valueArm,
            h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
            mapPaperComputation_recursive_eq]
      all_goals
        repeat' apply And.intro
      all_goals
        first
        | (intro label presence value hmem
           have hsmall := List.sizeOf_lt_of_mem hmem
           simp +arith at hsmall
           exact h_value value (by omega) depth σ)
        | (intro name value hmem
           have hsmall := List.sizeOf_lt_of_mem hmem
           simp +arith at hsmall
           exact h_value value (by omega) depth σ)
        | (intro child hmem
           have hsmall := List.sizeOf_lt_of_mem hmem
           simp (disch := omega) [h_value, h_computation, h_pattern, h_constructorBranch,
             h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper])
    · intro x hn depth σ
      cases x with
      | mk pattern guard body =>
        cases guard
        all_goals
          simp +arith at hn
          simp (config := { contextual := true }) (disch := omega)
            [mapPaperValue, mapPaperComputation, mapPaperPattern, mapConstructorBranch,
              mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
              mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift,
              mapOperationInstance_shift, List.attach_map_val, List.attach_map,
              List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation,
              h_pattern, h_constructorBranch, h_guardedBranch, h_valueArm,
              h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
              mapPaperComputation_recursive_eq]
    · intro x hn depth σ
      cases x
      all_goals
        simp +arith at hn
        simp (config := { contextual := true }) (disch := omega)
          [mapPaperValue, mapPaperComputation, mapPaperPattern, mapConstructorBranch,
            mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
            mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift,
            mapOperationInstance_shift, List.attach_map_val, List.attach_map,
            List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation,
            h_pattern, h_constructorBranch, h_guardedBranch, h_valueArm,
            h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
            mapPaperComputation_recursive_eq]
      all_goals
        repeat' apply And.intro
      all_goals
        first
        | (intro label presence value hmem
           have hsmall := List.sizeOf_lt_of_mem hmem
           simp +arith at hsmall
           exact h_value value (by omega) depth σ)
        | (intro name value hmem
           have hsmall := List.sizeOf_lt_of_mem hmem
           simp +arith at hsmall
           exact h_value value (by omega) depth σ)
        | (intro child hmem
           have hsmall := List.sizeOf_lt_of_mem hmem
           simp (disch := omega) [h_value, h_computation, h_pattern, h_constructorBranch,
             h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper])
    · intro x hn depth σ
      cases x with
      | mk operation rigidBinders pattern continuationBinder guard body =>
        cases guard
        all_goals
          simp +arith at hn
          simp (config := { contextual := true }) (disch := omega)
            [mapPaperValue, mapPaperComputation, mapPaperPattern, mapConstructorBranch,
              mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
              mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift,
              mapOperationInstance_shift, List.attach_map_val, List.attach_map,
              List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation,
              h_pattern, h_constructorBranch, h_guardedBranch, h_valueArm,
              h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
              mapPaperComputation_recursive_eq]
    · intro x hn depth σ
      cases x
      all_goals
        simp +arith at hn
        simp (config := { contextual := true }) (disch := omega)
          [mapPaperValue, mapPaperComputation, mapPaperPattern, mapConstructorBranch,
            mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
            mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift,
            mapOperationInstance_shift, List.attach_map_val, List.attach_map,
            List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation,
            h_pattern, h_constructorBranch, h_guardedBranch, h_valueArm,
            h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
            mapPaperComputation_recursive_eq]
      all_goals
        repeat' apply And.intro
      all_goals
        first
        | (intro label presence value hmem
           have hsmall := List.sizeOf_lt_of_mem hmem
           simp +arith at hsmall
           exact h_value value (by omega) depth σ)
        | (intro name value hmem
           have hsmall := List.sizeOf_lt_of_mem hmem
           simp +arith at hsmall
           exact h_value value (by omega) depth σ)
        | (intro child hmem
           have hsmall := List.sizeOf_lt_of_mem hmem
           simp (disch := omega) [h_value, h_computation, h_pattern, h_constructorBranch,
             h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper])
    · intro x hn depth σ
      cases x
      all_goals
        simp +arith at hn
        simp (config := { contextual := true }) (disch := omega)
          [mapPaperValue, mapPaperComputation, mapPaperPattern, mapConstructorBranch,
            mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
            mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift,
            mapOperationInstance_shift, List.attach_map_val, List.attach_map,
            List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation,
            h_pattern, h_constructorBranch, h_guardedBranch, h_valueArm,
            h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
            mapPaperComputation_recursive_eq]
      all_goals
        repeat' apply And.intro
      all_goals
        first
        | (intro label presence value hmem
           have hsmall := List.sizeOf_lt_of_mem hmem
           simp +arith at hsmall
           exact h_value value (by omega) depth σ)
        | (intro name value hmem
           have hsmall := List.sizeOf_lt_of_mem hmem
           simp +arith at hsmall
           exact h_value value (by omega) depth σ)
        | (intro child hmem
           have hsmall := List.sizeOf_lt_of_mem hmem
           simp (disch := omega) [h_value, h_computation, h_pattern, h_constructorBranch,
             h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper])


theorem mapPaperValue_shift_substitution_commutes (depth : Nat) (σ : Nat → Ty) (x : Value) :
    mapPaperValue (liftSubN depth (liftSub σ)) (mapPaperValue (liftSubN depth shiftTypeSubstitution) x) =
      mapPaperValue (liftSubN depth shiftTypeSubstitution) (mapPaperValue (liftSubN depth σ) x) :=
  (shiftAt_all (sizeOf x)).value x rfl depth σ

theorem mapPaperComputation_shift_substitution_commutes (depth : Nat) (σ : Nat → Ty) (x : Computation) :
    mapPaperComputation (liftSubN depth (liftSub σ)) (mapPaperComputation (liftSubN depth shiftTypeSubstitution) x) =
      mapPaperComputation (liftSubN depth shiftTypeSubstitution) (mapPaperComputation (liftSubN depth σ) x) :=
  (shiftAt_all (sizeOf x)).computation x rfl depth σ

theorem mapPaperPattern_shift_substitution_commutes (depth : Nat) (σ : Nat → Ty) (x : PatternPlan) :
    mapPaperPattern (liftSubN depth (liftSub σ)) (mapPaperPattern (liftSubN depth shiftTypeSubstitution) x) =
      mapPaperPattern (liftSubN depth shiftTypeSubstitution) (mapPaperPattern (liftSubN depth σ) x) :=
  (shiftAt_all (sizeOf x)).pattern x rfl depth σ

theorem mapConstructorBranch_shift_substitution_commutes (depth : Nat) (σ : Nat → Ty) (x : ConstructorBranch) :
    mapConstructorBranch (liftSubN depth (liftSub σ)) (mapConstructorBranch (liftSubN depth shiftTypeSubstitution) x) =
      mapConstructorBranch (liftSubN depth shiftTypeSubstitution) (mapConstructorBranch (liftSubN depth σ) x) :=
  (shiftAt_all (sizeOf x)).constructorBranch x rfl depth σ

theorem mapGuardedBranch_shift_substitution_commutes (depth : Nat) (σ : Nat → Ty) (x : GuardedBranch) :
    mapGuardedBranch (liftSubN depth (liftSub σ)) (mapGuardedBranch (liftSubN depth shiftTypeSubstitution) x) =
      mapGuardedBranch (liftSubN depth shiftTypeSubstitution) (mapGuardedBranch (liftSubN depth σ) x) :=
  (shiftAt_all (sizeOf x)).guardedBranch x rfl depth σ

theorem mapValueArm_shift_substitution_commutes (depth : Nat) (σ : Nat → Ty) (x : ValueArm) :
    mapValueArm (liftSubN depth (liftSub σ)) (mapValueArm (liftSubN depth shiftTypeSubstitution) x) =
      mapValueArm (liftSubN depth shiftTypeSubstitution) (mapValueArm (liftSubN depth σ) x) :=
  (shiftAt_all (sizeOf x)).valueArm x rfl depth σ

theorem mapOperationArm_shift_substitution_commutes (depth : Nat) (σ : Nat → Ty) (x : OperationArm) :
    mapOperationArm (liftSubN depth (liftSub σ)) (mapOperationArm (liftSubN depth shiftTypeSubstitution) x) =
      mapOperationArm (liftSubN depth shiftTypeSubstitution) (mapOperationArm (liftSubN depth σ) x) :=
  (shiftAt_all (sizeOf x)).operationArm x rfl depth σ

theorem mapHandlerPlan_shift_substitution_commutes (depth : Nat) (σ : Nat → Ty) (x : HandlerPlan) :
    mapHandlerPlan (liftSubN depth (liftSub σ)) (mapHandlerPlan (liftSubN depth shiftTypeSubstitution) x) =
      mapHandlerPlan (liftSubN depth shiftTypeSubstitution) (mapHandlerPlan (liftSubN depth σ) x) :=
  (shiftAt_all (sizeOf x)).handler x rfl depth σ

theorem mapMapperPlan_shift_substitution_commutes (depth : Nat) (σ : Nat → Ty) (x : MapperPlan) :
    mapMapperPlan (liftSubN depth (liftSub σ)) (mapMapperPlan (liftSubN depth shiftTypeSubstitution) x) =
      mapMapperPlan (liftSubN depth shiftTypeSubstitution) (mapMapperPlan (liftSubN depth σ) x) :=
  (shiftAt_all (sizeOf x)).mapper x rfl depth σ

theorem mapTemplateBody_shift_substitution_commutes (depth : Nat) (σ : Nat → Ty) (x : TemplateBody) :
    mapTemplateBody (liftSubN depth (liftSub σ)) (mapTemplateBody (liftSubN depth shiftTypeSubstitution) (x)) =
      mapTemplateBody (liftSubN depth shiftTypeSubstitution) (mapTemplateBody (liftSubN depth σ) (x)) := by
  cases x
  simp [mapTemplateBody, liftSubN_add, List.map_map, mapPaperComputation_shift_substitution_commutes]

theorem mapOperationDeclaration_shift_substitution_commutes (depth : Nat) (σ : Nat → Ty) (x : OperationDeclaration) :
    OperationDeclaration.substAmbient (liftSubN depth (liftSub σ)) (OperationDeclaration.substAmbient (liftSubN depth shiftTypeSubstitution) (x)) =
      OperationDeclaration.substAmbient (liftSubN depth shiftTypeSubstitution) (OperationDeclaration.substAmbient (liftSubN depth σ) (x)) := by
  cases x
  simp [OperationDeclaration.substAmbient, liftSubN_add, List.map_map, mapPaperComputation_shift_substitution_commutes]

theorem mapNominalConstructor_shift_substitution_commutes (depth : Nat) (σ : Nat → Ty) (x : NominalConstructor) :
    mapNominalConstructor (liftSubN depth (liftSub σ)) (mapNominalConstructor (liftSubN depth shiftTypeSubstitution) (x)) =
      mapNominalConstructor (liftSubN depth shiftTypeSubstitution) (mapNominalConstructor (liftSubN depth σ) (x)) := by
  cases x
  simp [mapNominalConstructor, liftSubN_add, List.map_map, mapPaperComputation_shift_substitution_commutes]

theorem mapPrimitiveSignature_shift_substitution_commutes (depth : Nat) (σ : Nat → Ty) (x : PrimitiveSignature) :
    mapPrimitiveSignature (liftSubN depth (liftSub σ)) (mapPrimitiveSignature (liftSubN depth shiftTypeSubstitution) (x)) =
      mapPrimitiveSignature (liftSubN depth shiftTypeSubstitution) (mapPrimitiveSignature (liftSubN depth σ) (x)) := by
  cases x
  simp [mapPrimitiveSignature, liftSubN_add, List.map_map, mapPaperComputation_shift_substitution_commutes]

theorem mapDeclarationTable_shift_substitution_commutes
    (depth : Nat) (σ : Nat → Ty) (declarations : DeclarationTable) :
    mapDeclarationTable (liftSubN depth (liftSub σ))
        (mapDeclarationTable (liftSubN depth shiftTypeSubstitution) declarations) =
      mapDeclarationTable (liftSubN depth shiftTypeSubstitution)
        (mapDeclarationTable (liftSubN depth σ) declarations) := by
  cases declarations
  simp [mapDeclarationTable, List.map_map, mapOperationDeclaration_shift_substitution_commutes,
    mapNominalConstructor_shift_substitution_commutes,
    mapPrimitiveSignature_shift_substitution_commutes, mapTemplateBody_shift_substitution_commutes]

end YulangClosure.PaperTypes
