import YulangClosure.PaperExecutionTypingSubstitution
import YulangClosure.PaperCoreStep

/-!
R54: the represented administrative type beta step, with arbitrary shared
contexts. Source: operational manuscript 2063–2065, preservation proof 1101;
corrected value/continuation account V1(b). Full source/native correspondence,
full executor preservation, metadata, inference A/B and production remain open.
-/
namespace YulangClosure.PaperTypes.PaperTypeBetaExecution

/-- Cancellation is generalized under every intervening type binder. -/
theorem liftSubN_cancel (depth : Nat) (argument : Ty) :
    composeTypeSubstitution (liftSubN depth (instantiateSubstitution [argument]))
      (liftSubN depth shiftTypeSubstitution) = idSub := by
  induction depth with
  | zero =>
      funext i
      simp [composeTypeSubstitution, liftSubN, shiftTypeSubstitution, subst,
        instantiateSubstitution, lookupTypeArgument, idSub]
  | succ depth ih =>
      simp only [liftSubN]
      rw [compose_liftSub, ih, liftSub_id]

@[simp] theorem subst_liftSubN_cancel (depth : Nat) (argument : Ty) (ty : Ty) :
    subst (liftSubN depth (instantiateSubstitution [argument]))
      (subst (liftSubN depth shiftTypeSubstitution) ty) = ty := by
  rw [subst_comp]
  change subst (composeTypeSubstitution _ _) ty = ty
  rw [liftSubN_cancel, subst_id]

private theorem map_eq_self_iff {α : Type} (xs : List α) (f : α → α) :
    xs.map f = xs ↔ ∀ x ∈ xs, f x = x := by
  simpa only [List.map_id, id_eq] using (List.map_inj_left (l := xs) (f := f) (g := id))

private theorem map_attach_eq_iff {α : Type} (xs : List α)
    (f : {x // x ∈ xs} → α) :
    xs.attach.map f = xs ↔ ∀ x h, f ⟨x, h⟩ = x := by
  have hm : xs.attach.map f = xs ↔ ∀ x h, True → f ⟨x, h⟩ = x := by
    simpa only [List.attach_map_subtype_val, List.mem_attach, Subtype.forall] using
      (List.map_inj_left (l := xs.attach) (f := f) (g := Subtype.val))
  constructor
  · intro h x hx
    exact hm.mp h x hx True.intro
  · intro h
    exact hm.mpr (fun x hx _ => h x hx)

private theorem mapAdapterMetadata_cancel (depth : Nat) (argument : Ty) (x : AdapterMetadata) :
    mapAdapterMetadata (liftSubN depth (instantiateSubstitution [argument]))
      (mapAdapterMetadata (liftSubN depth shiftTypeSubstitution) x) = x := by
  cases x
  simp [mapAdapterMetadata]

private theorem mapViewMetadata_cancel (depth : Nat) (argument : Ty) (x : ViewMetadata) :
    mapViewMetadata (liftSubN depth (instantiateSubstitution [argument]))
      (mapViewMetadata (liftSubN depth shiftTypeSubstitution) x) = x := by
  cases x
  simp [mapViewMetadata, mapTypeArguments, List.map_map, Function.comp_def, map_eq_self_iff, map_attach_eq_iff]

private theorem mapOperationInstance_cancel (depth : Nat) (argument : Ty) (x : OperationInstance) :
    (x.subst (liftSubN depth shiftTypeSubstitution)).subst
      (liftSubN depth (instantiateSubstitution [argument])) = x := by
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
private structure CancelAt (n : Nat) : Prop where
  value : ∀ (x : Value), sizeOf x = n → ∀ (depth : Nat) (argument : Ty),
    mapPaperValue (liftSubN depth (instantiateSubstitution [argument])) (mapPaperValue (liftSubN depth shiftTypeSubstitution) x) =
      x
  computation : ∀ (x : Computation), sizeOf x = n → ∀ (depth : Nat) (argument : Ty),
    mapPaperComputation (liftSubN depth (instantiateSubstitution [argument])) (mapPaperComputation (liftSubN depth shiftTypeSubstitution) x) =
      x
  pattern : ∀ (x : PatternPlan), sizeOf x = n → ∀ (depth : Nat) (argument : Ty),
    mapPaperPattern (liftSubN depth (instantiateSubstitution [argument])) (mapPaperPattern (liftSubN depth shiftTypeSubstitution) x) =
      x
  constructorBranch : ∀ (x : ConstructorBranch), sizeOf x = n → ∀ (depth : Nat) (argument : Ty),
    mapConstructorBranch (liftSubN depth (instantiateSubstitution [argument])) (mapConstructorBranch (liftSubN depth shiftTypeSubstitution) x) =
      x
  guardedBranch : ∀ (x : GuardedBranch), sizeOf x = n → ∀ (depth : Nat) (argument : Ty),
    mapGuardedBranch (liftSubN depth (instantiateSubstitution [argument])) (mapGuardedBranch (liftSubN depth shiftTypeSubstitution) x) =
      x
  valueArm : ∀ (x : ValueArm), sizeOf x = n → ∀ (depth : Nat) (argument : Ty),
    mapValueArm (liftSubN depth (instantiateSubstitution [argument])) (mapValueArm (liftSubN depth shiftTypeSubstitution) x) =
      x
  operationArm : ∀ (x : OperationArm), sizeOf x = n → ∀ (depth : Nat) (argument : Ty),
    mapOperationArm (liftSubN depth (instantiateSubstitution [argument])) (mapOperationArm (liftSubN depth shiftTypeSubstitution) x) =
      x
  handler : ∀ (x : HandlerPlan), sizeOf x = n → ∀ (depth : Nat) (argument : Ty),
    mapHandlerPlan (liftSubN depth (instantiateSubstitution [argument])) (mapHandlerPlan (liftSubN depth shiftTypeSubstitution) x) =
      x
  mapper : ∀ (x : MapperPlan), sizeOf x = n → ∀ (depth : Nat) (argument : Ty),
    mapMapperPlan (liftSubN depth (instantiateSubstitution [argument])) (mapMapperPlan (liftSubN depth shiftTypeSubstitution) x) =
      x

private theorem cancelAt_all (n : Nat) : CancelAt n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    have h_value (x : Value) (h : sizeOf x < n) (depth : Nat) (argument : Ty) :=
      (ih (sizeOf x) h).value x rfl depth argument
    have h_computation (x : Computation) (h : sizeOf x < n) (depth : Nat) (argument : Ty) :=
      (ih (sizeOf x) h).computation x rfl depth argument
    have h_pattern (x : PatternPlan) (h : sizeOf x < n) (depth : Nat) (argument : Ty) :=
      (ih (sizeOf x) h).pattern x rfl depth argument
    have h_constructorBranch (x : ConstructorBranch) (h : sizeOf x < n) (depth : Nat) (argument : Ty) :=
      (ih (sizeOf x) h).constructorBranch x rfl depth argument
    have h_guardedBranch (x : GuardedBranch) (h : sizeOf x < n) (depth : Nat) (argument : Ty) :=
      (ih (sizeOf x) h).guardedBranch x rfl depth argument
    have h_valueArm (x : ValueArm) (h : sizeOf x < n) (depth : Nat) (argument : Ty) :=
      (ih (sizeOf x) h).valueArm x rfl depth argument
    have h_operationArm (x : OperationArm) (h : sizeOf x < n) (depth : Nat) (argument : Ty) :=
      (ih (sizeOf x) h).operationArm x rfl depth argument
    have h_handler (x : HandlerPlan) (h : sizeOf x < n) (depth : Nat) (argument : Ty) :=
      (ih (sizeOf x) h).handler x rfl depth argument
    have h_mapper (x : MapperPlan) (h : sizeOf x < n) (depth : Nat) (argument : Ty) :=
      (ih (sizeOf x) h).mapper x rfl depth argument
    constructor
    · intro x hn depth argument
      cases x with
      | typeAbstraction body =>
        have hs : sizeOf body < n := by simp +arith at hn; omega
        simpa only [mapPaperValue, liftSubN] using
          congrArg Value.typeAbstraction (h_value body hs (depth + 1) argument)
      | _ =>
        all_goals
          simp +arith at hn
          simp (config := { contextual := true }) (disch := omega)
            [mapPaperValue, mapPaperComputation, mapPaperPattern, mapConstructorBranch,
              mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
              mapTypeArguments, subst_liftSubN_cancel, mapAdapterMetadata_cancel, mapViewMetadata_cancel,
              mapOperationInstance_cancel, List.attach_map_val, List.attach_map,
              List.map_map, Function.comp_def, map_eq_self_iff, map_attach_eq_iff, List.map_inj_left, liftSubN_add, h_value, h_computation,
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
             exact h_value value (by omega) depth argument)
          | (intro name value hmem
             have hsmall := List.sizeOf_lt_of_mem hmem
             simp +arith at hsmall
             exact h_value value (by omega) depth argument)
          | (intro child hmem
             have hsmall := List.sizeOf_lt_of_mem hmem
             simp (disch := omega) [h_value, h_computation, h_pattern, h_constructorBranch,
               h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper])
    · intro x hn depth argument
      cases x
      all_goals
        simp +arith at hn
        simp (config := { contextual := true }) (disch := omega)
          [mapPaperValue, mapPaperComputation, mapPaperPattern, mapConstructorBranch,
            mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
            mapTypeArguments, subst_liftSubN_cancel, mapAdapterMetadata_cancel, mapViewMetadata_cancel,
            mapOperationInstance_cancel, List.attach_map_val, List.attach_map,
            List.map_map, Function.comp_def, map_eq_self_iff, map_attach_eq_iff, List.map_inj_left, liftSubN_add, h_value, h_computation,
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
           exact h_value value (by omega) depth argument)
        | (intro name value hmem
           have hsmall := List.sizeOf_lt_of_mem hmem
           simp +arith at hsmall
           exact h_value value (by omega) depth argument)
        | (intro child hmem
           have hsmall := List.sizeOf_lt_of_mem hmem
           simp (disch := omega) [h_value, h_computation, h_pattern, h_constructorBranch,
             h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper])
    · intro x hn depth argument
      cases x with
      | record fields spread =>
        simp +arith at hn
        simp only [mapPaperPattern, List.attach_map, List.map_map, Function.comp_def]
        apply congrArg (fun fs => PatternPlan.record fs spread)
        apply Eq.trans (b := fields.attach.attach.map (fun x => x.val.val))
        · apply List.map_congr_left
          intro wrapped _
          rcases wrapped with ⟨⟨⟨label, pattern, default⟩, hmem⟩, hmemAttached⟩
          have hsmall := List.sizeOf_lt_of_mem hmem
          cases default with
          | none =>
            simp +arith at hsmall
            simp (disch := omega) [h_pattern]
          | some computation =>
            simp +arith at hsmall
            simp (disch := omega) [h_pattern, h_computation]
        · simp only [List.attach_map_val, List.map_id]
          exact List.attach_map_subtype_val fields
      | _ =>
        all_goals
          simp +arith at hn
          simp (config := { contextual := true }) (disch := omega)
            [mapPaperValue, mapPaperComputation, mapPaperPattern, mapConstructorBranch,
              mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
              mapTypeArguments, subst_liftSubN_cancel, mapAdapterMetadata_cancel, mapViewMetadata_cancel,
              mapOperationInstance_cancel, List.attach_map_val, List.attach_map,
              List.map_map, Function.comp_def, map_eq_self_iff, map_attach_eq_iff, List.map_inj_left, liftSubN_add, h_value, h_computation,
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
    · intro x hn depth argument
      cases x
      all_goals
        simp +arith at hn
        simp (config := { contextual := true }) (disch := omega)
          [mapPaperValue, mapPaperComputation, mapPaperPattern, mapConstructorBranch,
            mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
            mapTypeArguments, subst_liftSubN_cancel, mapAdapterMetadata_cancel, mapViewMetadata_cancel,
            mapOperationInstance_cancel, List.attach_map_val, List.attach_map,
            List.map_map, Function.comp_def, map_eq_self_iff, map_attach_eq_iff, List.map_inj_left, liftSubN_add, h_value, h_computation,
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
           exact h_value value (by omega) depth argument)
        | (intro name value hmem
           have hsmall := List.sizeOf_lt_of_mem hmem
           simp +arith at hsmall
           exact h_value value (by omega) depth argument)
        | (intro child hmem
           have hsmall := List.sizeOf_lt_of_mem hmem
           simp (disch := omega) [h_value, h_computation, h_pattern, h_constructorBranch,
             h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper])
    · intro x hn depth argument
      cases x with
      | mk pattern guard body =>
        cases guard
        all_goals
          simp +arith at hn
          simp (config := { contextual := true }) (disch := omega)
            [mapPaperValue, mapPaperComputation, mapPaperPattern, mapConstructorBranch,
              mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
              mapTypeArguments, subst_liftSubN_cancel, mapAdapterMetadata_cancel, mapViewMetadata_cancel,
              mapOperationInstance_cancel, List.attach_map_val, List.attach_map,
              List.map_map, Function.comp_def, map_eq_self_iff, map_attach_eq_iff, List.map_inj_left, liftSubN_add, h_value, h_computation,
              h_pattern, h_constructorBranch, h_guardedBranch, h_valueArm,
              h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
              mapPaperComputation_recursive_eq]
    · intro x hn depth argument
      cases x
      all_goals
        simp +arith at hn
        simp (config := { contextual := true }) (disch := omega)
          [mapPaperValue, mapPaperComputation, mapPaperPattern, mapConstructorBranch,
            mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
            mapTypeArguments, subst_liftSubN_cancel, mapAdapterMetadata_cancel, mapViewMetadata_cancel,
            mapOperationInstance_cancel, List.attach_map_val, List.attach_map,
            List.map_map, Function.comp_def, map_eq_self_iff, map_attach_eq_iff, List.map_inj_left, liftSubN_add, h_value, h_computation,
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
           exact h_value value (by omega) depth argument)
        | (intro name value hmem
           have hsmall := List.sizeOf_lt_of_mem hmem
           simp +arith at hsmall
           exact h_value value (by omega) depth argument)
        | (intro child hmem
           have hsmall := List.sizeOf_lt_of_mem hmem
           simp (disch := omega) [h_value, h_computation, h_pattern, h_constructorBranch,
             h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper])
    · intro x hn depth argument
      cases x with
      | mk operation rigidBinders pattern continuationBinder guard body =>
        cases guard
        all_goals
          simp +arith at hn
          simp (config := { contextual := true }) (disch := omega)
            [mapPaperValue, mapPaperComputation, mapPaperPattern, mapConstructorBranch,
              mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
              mapTypeArguments, subst_liftSubN_cancel, mapAdapterMetadata_cancel, mapViewMetadata_cancel,
              mapOperationInstance_cancel, List.attach_map_val, List.attach_map,
              List.map_map, Function.comp_def, map_eq_self_iff, map_attach_eq_iff, List.map_inj_left, liftSubN_add, h_value, h_computation,
              h_pattern, h_constructorBranch, h_guardedBranch, h_valueArm,
              h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
              mapPaperComputation_recursive_eq]
    · intro x hn depth argument
      cases x
      all_goals
        simp +arith at hn
        simp (config := { contextual := true }) (disch := omega)
          [mapPaperValue, mapPaperComputation, mapPaperPattern, mapConstructorBranch,
            mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
            mapTypeArguments, subst_liftSubN_cancel, mapAdapterMetadata_cancel, mapViewMetadata_cancel,
            mapOperationInstance_cancel, List.attach_map_val, List.attach_map,
            List.map_map, Function.comp_def, map_eq_self_iff, map_attach_eq_iff, List.map_inj_left, liftSubN_add, h_value, h_computation,
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
           exact h_value value (by omega) depth argument)
        | (intro name value hmem
           have hsmall := List.sizeOf_lt_of_mem hmem
           simp +arith at hsmall
           exact h_value value (by omega) depth argument)
        | (intro child hmem
           have hsmall := List.sizeOf_lt_of_mem hmem
           simp (disch := omega) [h_value, h_computation, h_pattern, h_constructorBranch,
             h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper])
    · intro x hn depth argument
      cases x
      all_goals
        simp +arith at hn
        simp (config := { contextual := true }) (disch := omega)
          [mapPaperValue, mapPaperComputation, mapPaperPattern, mapConstructorBranch,
            mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
            mapTypeArguments, subst_liftSubN_cancel, mapAdapterMetadata_cancel, mapViewMetadata_cancel,
            mapOperationInstance_cancel, List.attach_map_val, List.attach_map,
            List.map_map, Function.comp_def, map_eq_self_iff, map_attach_eq_iff, List.map_inj_left, liftSubN_add, h_value, h_computation,
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
           exact h_value value (by omega) depth argument)
        | (intro name value hmem
           have hsmall := List.sizeOf_lt_of_mem hmem
           simp +arith at hsmall
           exact h_value value (by omega) depth argument)
        | (intro child hmem
           have hsmall := List.sizeOf_lt_of_mem hmem
           simp (disch := omega) [h_value, h_computation, h_pattern, h_constructorBranch,
             h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper])

theorem mapPaperValue_cancel (depth : Nat) (argument : Ty) (x : Value) :
    mapPaperValue (liftSubN depth (instantiateSubstitution [argument]))
      (mapPaperValue (liftSubN depth shiftTypeSubstitution) x) = x :=
  (cancelAt_all (sizeOf x)).value x rfl depth argument

theorem mapPaperComputation_cancel (depth : Nat) (argument : Ty) (x : Computation) :
    mapPaperComputation (liftSubN depth (instantiateSubstitution [argument]))
      (mapPaperComputation (liftSubN depth shiftTypeSubstitution) x) = x :=
  (cancelAt_all (sizeOf x)).computation x rfl depth argument

theorem mapPaperPattern_cancel (depth : Nat) (argument : Ty) (x : PatternPlan) :
    mapPaperPattern (liftSubN depth (instantiateSubstitution [argument]))
      (mapPaperPattern (liftSubN depth shiftTypeSubstitution) x) = x :=
  (cancelAt_all (sizeOf x)).pattern x rfl depth argument

theorem mapConstructorBranch_cancel (depth : Nat) (argument : Ty) (x : ConstructorBranch) :
    mapConstructorBranch (liftSubN depth (instantiateSubstitution [argument]))
      (mapConstructorBranch (liftSubN depth shiftTypeSubstitution) x) = x :=
  (cancelAt_all (sizeOf x)).constructorBranch x rfl depth argument

theorem mapGuardedBranch_cancel (depth : Nat) (argument : Ty) (x : GuardedBranch) :
    mapGuardedBranch (liftSubN depth (instantiateSubstitution [argument]))
      (mapGuardedBranch (liftSubN depth shiftTypeSubstitution) x) = x :=
  (cancelAt_all (sizeOf x)).guardedBranch x rfl depth argument

theorem mapValueArm_cancel (depth : Nat) (argument : Ty) (x : ValueArm) :
    mapValueArm (liftSubN depth (instantiateSubstitution [argument]))
      (mapValueArm (liftSubN depth shiftTypeSubstitution) x) = x :=
  (cancelAt_all (sizeOf x)).valueArm x rfl depth argument

theorem mapOperationArm_cancel (depth : Nat) (argument : Ty) (x : OperationArm) :
    mapOperationArm (liftSubN depth (instantiateSubstitution [argument]))
      (mapOperationArm (liftSubN depth shiftTypeSubstitution) x) = x :=
  (cancelAt_all (sizeOf x)).operationArm x rfl depth argument

theorem mapHandlerPlan_cancel (depth : Nat) (argument : Ty) (x : HandlerPlan) :
    mapHandlerPlan (liftSubN depth (instantiateSubstitution [argument]))
      (mapHandlerPlan (liftSubN depth shiftTypeSubstitution) x) = x :=
  (cancelAt_all (sizeOf x)).handler x rfl depth argument

theorem mapMapperPlan_cancel (depth : Nat) (argument : Ty) (x : MapperPlan) :
    mapMapperPlan (liftSubN depth (instantiateSubstitution [argument]))
      (mapMapperPlan (liftSubN depth shiftTypeSubstitution) x) = x :=
  (cancelAt_all (sizeOf x)).mapper x rfl depth argument

theorem mapTemplateBody_cancel (depth : Nat) (argument : Ty) (x : TemplateBody) :
    mapTemplateBody (liftSubN depth (instantiateSubstitution [argument]))
      (mapTemplateBody (liftSubN depth shiftTypeSubstitution) x) = x := by
  cases x
  simp [mapTemplateBody, liftSubN_add, List.map_map, Function.comp_def, map_eq_self_iff, map_attach_eq_iff, mapPaperComputation_cancel]

theorem OperationDeclaration_substAmbient_cancel (depth : Nat) (argument : Ty) (x : OperationDeclaration) :
    OperationDeclaration.substAmbient (liftSubN depth (instantiateSubstitution [argument]))
      (OperationDeclaration.substAmbient (liftSubN depth shiftTypeSubstitution) x) = x := by
  cases x
  simp [OperationDeclaration.substAmbient, liftSubN_add, List.map_map, Function.comp_def, map_eq_self_iff, map_attach_eq_iff, mapPaperComputation_cancel]

theorem mapNominalConstructor_cancel (depth : Nat) (argument : Ty) (x : NominalConstructor) :
    mapNominalConstructor (liftSubN depth (instantiateSubstitution [argument]))
      (mapNominalConstructor (liftSubN depth shiftTypeSubstitution) x) = x := by
  cases x
  simp [mapNominalConstructor, liftSubN_add, List.map_map, Function.comp_def, map_eq_self_iff, map_attach_eq_iff, mapPaperComputation_cancel]

theorem mapPrimitiveSignature_cancel (depth : Nat) (argument : Ty) (x : PrimitiveSignature) :
    mapPrimitiveSignature (liftSubN depth (instantiateSubstitution [argument]))
      (mapPrimitiveSignature (liftSubN depth shiftTypeSubstitution) x) = x := by
  cases x
  simp [mapPrimitiveSignature, liftSubN_add, List.map_map, Function.comp_def, map_eq_self_iff, map_attach_eq_iff, mapPaperComputation_cancel]

theorem mapDeclarationTable_cancel (depth : Nat) (argument : Ty) (d : DeclarationTable) :
    mapDeclarationTable (liftSubN depth (instantiateSubstitution [argument]))
      (mapDeclarationTable (liftSubN depth shiftTypeSubstitution) d) = d := by
  cases d
  simp [mapDeclarationTable, List.map_map, Function.comp_def, map_eq_self_iff, map_attach_eq_iff, OperationDeclaration_substAmbient_cancel,
    mapNominalConstructor_cancel, mapPrimitiveSignature_cancel, mapTemplateBody_cancel]

theorem mapTypeEnvironment_cancel (argument : Ty) (e : TypeEnvironment) :
    mapTypeEnvironment (instantiateSubstitution [argument])
      (mapTypeEnvironment shiftTypeSubstitution e) = e := by
  have h := subst_liftSubN_cancel 0 argument
  simp only [liftSubN] at h
  simp [mapTypeEnvironment, List.map_map, Function.comp_def, map_eq_self_iff, map_attach_eq_iff, h]

theorem mapGraphEnvironment_cancel (argument : Ty) (g : GraphEnvironment) :
    mapGraphEnvironment (instantiateSubstitution [argument])
      (mapGraphEnvironment shiftTypeSubstitution g) = g := by
  simp only [mapGraphEnvironment, List.map_map, Function.comp_def, map_eq_self_iff, map_attach_eq_iff]
  intro entry _
  rcases entry with ⟨identity, ty⟩
  exact congrArg (fun t => (identity, t)) (subst_liftSubN_cancel 0 argument ty)

/-- Only an explicit value type-application redex reduces here. -/
def typeBetaValue : Value → Option Value
  | .typeApplication (.typeAbstraction body) argument =>
      some (mapPaperValue (instantiateSubstitution [argument]) body)
  | _ => none

theorem typeBetaValue_shape (body : Value) (argument : Ty) :
    typeBetaValue (.typeApplication (.typeAbstraction body) argument) =
      some (mapPaperValue (instantiateSubstitution [argument]) body) := rfl

/-- Use the existing explicit simultaneous typing substitution theorem. -/
theorem instantiate_body {d g e body bodyType} (argument : Ty)
    (h : PaperValueTyped (mapDeclarationTable shiftTypeSubstitution d)
      (mapGraphEnvironment shiftTypeSubstitution g)
      (mapTypeEnvironment shiftTypeSubstitution e) body bodyType) :
    PaperValueTyped d g e (mapPaperValue (instantiateSubstitution [argument]) body)
      (instantiateType [argument] bodyType) := by
  have result := PaperValueTyped.subst_explicit (instantiateSubstitution [argument]) h
  have hd := mapDeclarationTable_cancel 0 argument d
  simp only [liftSubN] at hd
  simpa only [hd, mapGraphEnvironment_cancel, mapTypeEnvironment_cancel, instantiateType] using result

theorem typeBetaValue_applicable {d g e body argument resultType}
    (h : PaperValueTyped d g e (.typeApplication (.typeAbstraction body) argument) resultType) :
    typeBetaValue (.typeApplication (.typeAbstraction body) argument) =
      some (mapPaperValue (instantiateSubstitution [argument]) body) ∧
    PaperValueTyped d g e (mapPaperValue (instantiateSubstitution [argument]) body) resultType := by
  constructor
  · rfl
  · cases h with
    | typeApplication hf =>
      cases hf with
      | typeAbstraction hb => exact instantiate_body argument hb

theorem typeBetaValue_preservation {d g e value next resultType}
    (h : PaperValueTyped d g e value resultType)
    (hs : typeBetaValue value = some next) : PaperValueTyped d g e next resultType := by
  cases value with
  | typeApplication function argument =>
    cases function with
    | typeAbstraction body =>
      have he : mapPaperValue (instantiateSubstitution [argument]) body = next := Option.some.inj hs
      exact he ▸ (typeBetaValue_applicable h).2
    | _ => simp [typeBetaValue] at hs
  | _ => simp [typeBetaValue] at hs

/-- The context lift performs only type beta; Force/Delay is a second step. -/
def typeBetaForce : Computation → Option Computation
  | .force value => (typeBetaValue value).map Computation.force
  | _ => none

theorem typeBetaForce_preservation {d g e source next resultType}
    (h : PaperComputationTyped d g e source resultType)
    (hs : typeBetaForce source = some next) : PaperComputationTyped d g e next resultType := by
  cases source with
  | force value =>
    cases h with
    | force hv =>
      cases he : typeBetaValue value with
      | none => simp [typeBetaForce, he] at hs
      | some nextValue =>
        have hn : Computation.force nextValue = next := by simpa [typeBetaForce, he] using hs
        exact hn ▸ PaperComputationTyped.force (typeBetaValue_preservation hv he)
  | _ => simp [typeBetaForce] at hs

/-- Precisely two distinct reductions, with a typing judgment at each endpoint. -/
theorem force_typeBeta_delay {d g e body argument resultType}
    (h : PaperComputationTyped d g e
      (.force (.typeApplication (.typeAbstraction (.delay body)) argument)) resultType) :
    let body' := mapPaperComputation (instantiateSubstitution [argument]) body
    typeBetaForce (.force (.typeApplication (.typeAbstraction (.delay body)) argument)) =
        some (.force (.delay body')) ∧
    PaperComputationTyped d g e (.force (.delay body')) resultType ∧
    PaperCoreStep.step (.force (.delay body')) = some body' ∧
    PaperComputationTyped d g e body' resultType := by
  dsimp
  have first : typeBetaForce (.force (.typeApplication (.typeAbstraction (.delay body)) argument)) =
      some (.force (.delay (mapPaperComputation (instantiateSubstitution [argument]) body))) := by
    simp [typeBetaForce, typeBetaValue, mapPaperValue]
  have middle := typeBetaForce_preservation h first
  exact ⟨first, middle, rfl, PaperCoreStep.preservation middle rfl⟩

/-- Nested forall and mu binders retain their rigid variables and shift the argument. -/
theorem nested_poly_mu (argument : Ty) :
    instantiateType [argument] (.poly (.mu (.callable (.var 2) (.var 0)))) =
      .poly (.mu (.callable (mapVars Nat.succ (mapVars Nat.succ argument)) (.var 0))) := by
  rfl

/-- A shared ambient variable survives beta; it is not replaced by the argument. -/
theorem shared_variable_countercase (argument : Ty) :
    instantiateType [argument] (.poly (.mu (.var 3))) = .poly (.mu (.var 2)) := rfl

end YulangClosure.PaperTypes.PaperTypeBetaExecution
