import YulangClosure.PaperExecutionTypingSubstitution
import YulangClosure.PaperCoreStep

/-!
Type-application beta preservation for the manuscript-explicit paper judgments.
One substitution acts on every represented syntax component, and cancellation
restores the same arbitrary shared declaration, graph, and term contexts.
This local redex theorem does not establish the full machine or source bridge.
-/
namespace YulangClosure.PaperTypes.PaperTypeApplicationPreservation

/-- Insert a fresh block of type binders before the shared ambient variables. -/
def shiftTypeSubstitutionN (count index : Nat) : Ty := .var (index + count)

/-- Instantiation removes precisely the fresh block introduced by shifting. -/
theorem liftSubN_cancel (depth : Nat) (arguments : List Ty) :
    composeTypeSubstitution
      (liftSubN depth (instantiateSubstitution arguments))
      (liftSubN depth (shiftTypeSubstitutionN arguments.length)) = idSub := by
  induction depth with
  | zero =>
      funext index
      have hnone : lookupTypeArgument arguments (index + arguments.length) = none :=
        lookupTypeArgument_none_of_ge arguments _ (by omega)
      simp [composeTypeSubstitution, liftSubN, shiftTypeSubstitutionN, subst,
        instantiateSubstitution, hnone, idSub]
  | succ depth ih =>
      simp only [liftSubN, compose_liftSub, ih, liftSub_id]

@[simp] theorem subst_liftSubN_cancel (depth : Nat) (arguments : List Ty) (ty : Ty) :
    subst (liftSubN depth (instantiateSubstitution arguments))
      (subst (liftSubN depth (shiftTypeSubstitutionN arguments.length)) ty) = ty := by
  rw [subst_comp]
  change subst
    (composeTypeSubstitution (liftSubN depth (instantiateSubstitution arguments))
      (liftSubN depth (shiftTypeSubstitutionN arguments.length))) ty = ty
  rw [liftSubN_cancel, subst_id]

private theorem map_eq_self_iff {α : Type} (f : α → α) (xs : List α) :
    xs.map f = xs ↔ ∀ x ∈ xs, f x = x := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

private theorem map_attach_eq_iff {α : Type} (xs : List α)
    (f : {x // x ∈ xs} → α) :
    xs.attach.map f = xs ↔ ∀ x h, f ⟨x, h⟩ = x := by
  constructor
  · intro he x hx
    have hm : xs.attach.map f = xs.attach.map Subtype.val :=
      he.trans (List.attach_map_subtype_val xs).symm
    exact List.map_inj_left.mp hm ⟨x, hx⟩ (List.mem_attach _ _)
  · intro h
    calc
      xs.attach.map f = xs.attach.map Subtype.val := by
        apply List.map_congr_left
        intro x _
        exact h x.val x.property
      _ = xs := List.attach_map_subtype_val xs

private theorem mapPaperPattern_record_eq (σ : Nat → Ty)
    (fields : List (Label × PatternPlan × Option Computation)) (spread : Option TermName) :
    mapPaperPattern σ (.record fields spread) =
      .record (fields.map fun field =>
        (field.1, mapPaperPattern σ field.2.1, field.2.2.map (mapPaperComputation σ))) spread := by
  rw [mapPaperPattern]
  congr 1
  rw [← List.attach_map_val (l := fields)
    (f := fun field : Label × PatternPlan × Option Computation =>
      (field.1, mapPaperPattern σ field.2.1, field.2.2.map (mapPaperComputation σ)))]
  apply List.map_congr_left
  intro entry _
  rcases entry with ⟨⟨label, pattern, default⟩, hmem⟩
  cases default <;> rfl

private theorem mapAdapterMetadata_cancel (depth : Nat) (arguments : List Ty)
    (x : AdapterMetadata) :
    mapAdapterMetadata (liftSubN depth (instantiateSubstitution arguments))
      (mapAdapterMetadata (liftSubN depth (shiftTypeSubstitutionN arguments.length)) x) = x := by
  cases x
  simp [mapAdapterMetadata]

private theorem mapViewMetadata_cancel (depth : Nat) (arguments : List Ty)
    (x : ViewMetadata) :
    mapViewMetadata (liftSubN depth (instantiateSubstitution arguments))
      (mapViewMetadata (liftSubN depth (shiftTypeSubstitutionN arguments.length)) x) = x := by
  cases x
  simp [mapViewMetadata, mapTypeArguments, List.map_map, Function.comp_def]

private theorem mapOperationInstance_cancel (depth : Nat) (arguments : List Ty)
    (x : OperationInstance) :
    (x.subst (liftSubN depth (shiftTypeSubstitutionN arguments.length))).subst
      (liftSubN depth (instantiateSubstitution arguments)) = x := by
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

/-- One strong induction covers the mutually recursive raw syntax. -/
private structure CancelAt (n : Nat) : Prop where
  value : ∀ (x : Value), sizeOf x = n → ∀ (depth : Nat) (arguments : List Ty),
    mapPaperValue (liftSubN depth (instantiateSubstitution arguments))
      (mapPaperValue (liftSubN depth (shiftTypeSubstitutionN arguments.length)) x) = x
  computation : ∀ (x : Computation), sizeOf x = n → ∀ (depth : Nat) (arguments : List Ty),
    mapPaperComputation (liftSubN depth (instantiateSubstitution arguments))
      (mapPaperComputation (liftSubN depth (shiftTypeSubstitutionN arguments.length)) x) = x
  pattern : ∀ (x : PatternPlan), sizeOf x = n → ∀ (depth : Nat) (arguments : List Ty),
    mapPaperPattern (liftSubN depth (instantiateSubstitution arguments))
      (mapPaperPattern (liftSubN depth (shiftTypeSubstitutionN arguments.length)) x) = x
  constructorBranch : ∀ (x : ConstructorBranch), sizeOf x = n → ∀ (depth : Nat) (arguments : List Ty),
    mapConstructorBranch (liftSubN depth (instantiateSubstitution arguments))
      (mapConstructorBranch (liftSubN depth (shiftTypeSubstitutionN arguments.length)) x) = x
  guardedBranch : ∀ (x : GuardedBranch), sizeOf x = n → ∀ (depth : Nat) (arguments : List Ty),
    mapGuardedBranch (liftSubN depth (instantiateSubstitution arguments))
      (mapGuardedBranch (liftSubN depth (shiftTypeSubstitutionN arguments.length)) x) = x
  valueArm : ∀ (x : ValueArm), sizeOf x = n → ∀ (depth : Nat) (arguments : List Ty),
    mapValueArm (liftSubN depth (instantiateSubstitution arguments))
      (mapValueArm (liftSubN depth (shiftTypeSubstitutionN arguments.length)) x) = x
  operationArm : ∀ (x : OperationArm), sizeOf x = n → ∀ (depth : Nat) (arguments : List Ty),
    mapOperationArm (liftSubN depth (instantiateSubstitution arguments))
      (mapOperationArm (liftSubN depth (shiftTypeSubstitutionN arguments.length)) x) = x
  handler : ∀ (x : HandlerPlan), sizeOf x = n → ∀ (depth : Nat) (arguments : List Ty),
    mapHandlerPlan (liftSubN depth (instantiateSubstitution arguments))
      (mapHandlerPlan (liftSubN depth (shiftTypeSubstitutionN arguments.length)) x) = x
  mapper : ∀ (x : MapperPlan), sizeOf x = n → ∀ (depth : Nat) (arguments : List Ty),
    mapMapperPlan (liftSubN depth (instantiateSubstitution arguments))
      (mapMapperPlan (liftSubN depth (shiftTypeSubstitutionN arguments.length)) x) = x

private theorem cancelAt_all (n : Nat) : CancelAt n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    have h_value (x : Value) (h : sizeOf x < n) (depth : Nat) (arguments : List Ty) :=
      (ih (sizeOf x) h).value x rfl depth arguments
    have h_computation (x : Computation) (h : sizeOf x < n) (depth : Nat) (arguments : List Ty) :=
      (ih (sizeOf x) h).computation x rfl depth arguments
    have h_pattern (x : PatternPlan) (h : sizeOf x < n) (depth : Nat) (arguments : List Ty) :=
      (ih (sizeOf x) h).pattern x rfl depth arguments
    have h_constructorBranch (x : ConstructorBranch) (h : sizeOf x < n) (depth : Nat) (arguments : List Ty) :=
      (ih (sizeOf x) h).constructorBranch x rfl depth arguments
    have h_guardedBranch (x : GuardedBranch) (h : sizeOf x < n) (depth : Nat) (arguments : List Ty) :=
      (ih (sizeOf x) h).guardedBranch x rfl depth arguments
    have h_valueArm (x : ValueArm) (h : sizeOf x < n) (depth : Nat) (arguments : List Ty) :=
      (ih (sizeOf x) h).valueArm x rfl depth arguments
    have h_operationArm (x : OperationArm) (h : sizeOf x < n) (depth : Nat) (arguments : List Ty) :=
      (ih (sizeOf x) h).operationArm x rfl depth arguments
    have h_handler (x : HandlerPlan) (h : sizeOf x < n) (depth : Nat) (arguments : List Ty) :=
      (ih (sizeOf x) h).handler x rfl depth arguments
    have h_mapper (x : MapperPlan) (h : sizeOf x < n) (depth : Nat) (arguments : List Ty) :=
      (ih (sizeOf x) h).mapper x rfl depth arguments
    constructor
    · intro x hn depth arguments
      cases x with
      | typeAbstraction body =>
        have hs : sizeOf body < n := by simp +arith at hn; omega
        simpa only [mapPaperValue, liftSubN] using
          congrArg Value.typeAbstraction (h_value body hs (depth + 1) arguments)
      | _ =>
        all_goals
          simp +arith at hn
          simp (config := { contextual := true }) (disch := omega)
            [mapPaperValue, mapTypeArguments, mapAdapterMetadata_cancel, mapViewMetadata_cancel,
             List.attach_map_val, List.attach_map, List.map_map, Function.comp_def,
             map_eq_self_iff, map_attach_eq_iff, h_value, h_computation, mapPaperValue_record_eq]
        all_goals
          repeat' apply And.intro
        all_goals
          first
          | (intro label presence value hmem
             have hsmall := List.sizeOf_lt_of_mem hmem
             simp +arith at hsmall
             exact h_value value (by omega) depth arguments)
          | (intro name value hmem
             have hsmall := List.sizeOf_lt_of_mem hmem
             simp +arith at hsmall
             exact h_value value (by omega) depth arguments)
          | (intro child hmem
             have hsmall := List.sizeOf_lt_of_mem hmem
             simp (disch := omega) [h_value])
    · intro x hn depth arguments
      cases x
      all_goals
        simp +arith at hn
        simp (config := { contextual := true }) (disch := omega)
          [mapPaperComputation, mapTypeArguments, mapViewMetadata_cancel,
           mapOperationInstance_cancel, List.attach_map_val, List.attach_map, List.map_map,
           Function.comp_def, map_eq_self_iff, map_attach_eq_iff, h_value, h_computation,
           h_operationArm, h_handler, h_mapper, mapPaperComputation_recursive_eq]
      all_goals
        repeat' apply And.intro
      all_goals
        first
        | (intro label presence value hmem
           have hsmall := List.sizeOf_lt_of_mem hmem
           simp +arith at hsmall
           exact h_value value (by omega) depth arguments)
        | (intro name value hmem
           have hsmall := List.sizeOf_lt_of_mem hmem
           simp +arith at hsmall
           exact h_value value (by omega) depth arguments)
        | (intro child hmem
           have hsmall := List.sizeOf_lt_of_mem hmem
           simp (disch := omega) [h_value, h_constructorBranch, h_operationArm])
    · intro x hn depth arguments
      cases x
      all_goals
        simp +arith at hn
        simp (config := { contextual := true }) (disch := omega)
          [mapPaperPattern, mapTypeArguments, List.attach_map_val, List.attach_map, List.map_map,
           Function.comp_def, map_eq_self_iff, map_attach_eq_iff, h_value, h_computation,
           h_pattern, mapPaperPattern_record_eq]
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
    · intro x hn depth arguments
      cases x
      all_goals
        simp +arith at hn
        simp (config := { contextual := true }) (disch := omega)
          [mapConstructorBranch, h_computation]
      all_goals
        repeat' apply And.intro
      all_goals
        first
        | (intro label presence value hmem
           have hsmall := List.sizeOf_lt_of_mem hmem
           simp +arith at hsmall
           exact h_value value (by omega) depth arguments)
        | (intro name value hmem
           have hsmall := List.sizeOf_lt_of_mem hmem
           simp +arith at hsmall
           exact h_value value (by omega) depth arguments)
        | (intro child hmem
           have hsmall := List.sizeOf_lt_of_mem hmem
           simp (disch := omega) [h_value, h_computation, h_pattern, h_constructorBranch,
             h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper])
    · intro x hn depth arguments
      cases x with
      | mk pattern guard body =>
        cases guard
        all_goals
          simp +arith at hn
          simp (config := { contextual := true }) (disch := omega)
            [mapGuardedBranch, h_computation, h_pattern]
    · intro x hn depth arguments
      cases x
      all_goals
        simp +arith at hn
        simp (config := { contextual := true }) (disch := omega)
          [mapValueArm, h_guardedBranch]
      all_goals
        repeat' apply And.intro
      all_goals
        first
        | (intro label presence value hmem
           have hsmall := List.sizeOf_lt_of_mem hmem
           simp +arith at hsmall
           exact h_value value (by omega) depth arguments)
        | (intro name value hmem
           have hsmall := List.sizeOf_lt_of_mem hmem
           simp +arith at hsmall
           exact h_value value (by omega) depth arguments)
        | (intro child hmem
           have hsmall := List.sizeOf_lt_of_mem hmem
           simp (disch := omega) [h_value, h_computation, h_pattern, h_constructorBranch,
             h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper])
    · intro x hn depth arguments
      cases x with
      | mk operation rigidBinders pattern continuationBinder guard body =>
        cases guard
        all_goals
          simp +arith at hn
          simp (config := { contextual := true }) (disch := omega)
            [mapOperationArm, liftSubN_add, h_computation, h_pattern]
    · intro x hn depth arguments
      cases x
      all_goals
        simp +arith at hn
        simp (config := { contextual := true }) (disch := omega)
          [mapHandlerPlan, List.attach_map_val, List.attach_map, List.map_map, Function.comp_def,
           map_attach_eq_iff]
      all_goals
        repeat' apply And.intro
      all_goals
        first
        | (intro label presence value hmem
           have hsmall := List.sizeOf_lt_of_mem hmem
           simp +arith at hsmall
           exact h_value value (by omega) depth arguments)
        | (intro name value hmem
           have hsmall := List.sizeOf_lt_of_mem hmem
           simp +arith at hsmall
           exact h_value value (by omega) depth arguments)
        | (intro child hmem
           have hsmall := List.sizeOf_lt_of_mem hmem
           simp (disch := omega) [h_valueArm, h_operationArm])
    · intro x hn depth arguments
      cases x
      all_goals
        simp +arith at hn
        simp (config := { contextual := true }) (disch := omega)
          [mapMapperPlan, mapOperationInstance_cancel, h_computation]
      all_goals
        repeat' apply And.intro
      all_goals
        first
        | (intro label presence value hmem
           have hsmall := List.sizeOf_lt_of_mem hmem
           simp +arith at hsmall
           exact h_value value (by omega) depth arguments)
        | (intro name value hmem
           have hsmall := List.sizeOf_lt_of_mem hmem
           simp +arith at hsmall
           exact h_value value (by omega) depth arguments)
        | (intro child hmem
           have hsmall := List.sizeOf_lt_of_mem hmem
           simp (disch := omega) [h_value, h_computation, h_pattern, h_constructorBranch,
             h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper])


theorem mapPaperValue_cancel (depth : Nat) (arguments : List Ty) (x : Value) :
    mapPaperValue (liftSubN depth (instantiateSubstitution arguments))
      (mapPaperValue (liftSubN depth (shiftTypeSubstitutionN arguments.length)) x) = x :=
  (cancelAt_all (sizeOf x)).value x rfl depth arguments

theorem mapPaperComputation_cancel (depth : Nat) (arguments : List Ty) (x : Computation) :
    mapPaperComputation (liftSubN depth (instantiateSubstitution arguments))
      (mapPaperComputation (liftSubN depth (shiftTypeSubstitutionN arguments.length)) x) = x :=
  (cancelAt_all (sizeOf x)).computation x rfl depth arguments

theorem mapPaperPattern_cancel (depth : Nat) (arguments : List Ty) (x : PatternPlan) :
    mapPaperPattern (liftSubN depth (instantiateSubstitution arguments))
      (mapPaperPattern (liftSubN depth (shiftTypeSubstitutionN arguments.length)) x) = x :=
  (cancelAt_all (sizeOf x)).pattern x rfl depth arguments

theorem mapConstructorBranch_cancel (depth : Nat) (arguments : List Ty) (x : ConstructorBranch) :
    mapConstructorBranch (liftSubN depth (instantiateSubstitution arguments))
      (mapConstructorBranch (liftSubN depth (shiftTypeSubstitutionN arguments.length)) x) = x :=
  (cancelAt_all (sizeOf x)).constructorBranch x rfl depth arguments

theorem mapGuardedBranch_cancel (depth : Nat) (arguments : List Ty) (x : GuardedBranch) :
    mapGuardedBranch (liftSubN depth (instantiateSubstitution arguments))
      (mapGuardedBranch (liftSubN depth (shiftTypeSubstitutionN arguments.length)) x) = x :=
  (cancelAt_all (sizeOf x)).guardedBranch x rfl depth arguments

theorem mapValueArm_cancel (depth : Nat) (arguments : List Ty) (x : ValueArm) :
    mapValueArm (liftSubN depth (instantiateSubstitution arguments))
      (mapValueArm (liftSubN depth (shiftTypeSubstitutionN arguments.length)) x) = x :=
  (cancelAt_all (sizeOf x)).valueArm x rfl depth arguments

theorem mapOperationArm_cancel (depth : Nat) (arguments : List Ty) (x : OperationArm) :
    mapOperationArm (liftSubN depth (instantiateSubstitution arguments))
      (mapOperationArm (liftSubN depth (shiftTypeSubstitutionN arguments.length)) x) = x :=
  (cancelAt_all (sizeOf x)).operationArm x rfl depth arguments

theorem mapHandlerPlan_cancel (depth : Nat) (arguments : List Ty) (x : HandlerPlan) :
    mapHandlerPlan (liftSubN depth (instantiateSubstitution arguments))
      (mapHandlerPlan (liftSubN depth (shiftTypeSubstitutionN arguments.length)) x) = x :=
  (cancelAt_all (sizeOf x)).handler x rfl depth arguments

theorem mapMapperPlan_cancel (depth : Nat) (arguments : List Ty) (x : MapperPlan) :
    mapMapperPlan (liftSubN depth (instantiateSubstitution arguments))
      (mapMapperPlan (liftSubN depth (shiftTypeSubstitutionN arguments.length)) x) = x :=
  (cancelAt_all (sizeOf x)).mapper x rfl depth arguments

theorem mapTemplateBody_cancel (depth : Nat) (arguments : List Ty) (x : TemplateBody) :
    mapTemplateBody (liftSubN depth (instantiateSubstitution arguments))
      (mapTemplateBody (liftSubN depth (shiftTypeSubstitutionN arguments.length)) x) = x := by
  cases x
  simp [mapTemplateBody, liftSubN_add, List.map_map, Function.comp_def, mapPaperComputation_cancel]

theorem mapOperationDeclaration_cancel (depth : Nat) (arguments : List Ty)
    (x : OperationDeclaration) :
    OperationDeclaration.substAmbient (liftSubN depth (instantiateSubstitution arguments))
      (OperationDeclaration.substAmbient (liftSubN depth (shiftTypeSubstitutionN arguments.length)) x) = x := by
  cases x
  simp [OperationDeclaration.substAmbient, liftSubN_add]

theorem mapNominalConstructor_cancel (depth : Nat) (arguments : List Ty)
    (x : NominalConstructor) :
    mapNominalConstructor (liftSubN depth (instantiateSubstitution arguments))
      (mapNominalConstructor (liftSubN depth (shiftTypeSubstitutionN arguments.length)) x) = x := by
  cases x
  simp [mapNominalConstructor, liftSubN_add, List.map_map, Function.comp_def]

theorem mapPrimitiveSignature_cancel (depth : Nat) (arguments : List Ty)
    (x : PrimitiveSignature) :
    mapPrimitiveSignature (liftSubN depth (instantiateSubstitution arguments))
      (mapPrimitiveSignature (liftSubN depth (shiftTypeSubstitutionN arguments.length)) x) = x := by
  cases x
  simp [mapPrimitiveSignature, liftSubN_add, List.map_map, Function.comp_def]

theorem mapDeclarationTable_cancel (depth : Nat) (arguments : List Ty)
    (declarations : DeclarationTable) :
    mapDeclarationTable (liftSubN depth (instantiateSubstitution arguments))
      (mapDeclarationTable (liftSubN depth (shiftTypeSubstitutionN arguments.length)) declarations) = declarations := by
  cases declarations
  simp [mapDeclarationTable, List.map_map, Function.comp_def, mapOperationDeclaration_cancel,
    mapNominalConstructor_cancel, mapPrimitiveSignature_cancel, mapTemplateBody_cancel]

theorem mapTypeEnvironment_cancel (arguments : List Ty) (environment : TypeEnvironment) :
    mapTypeEnvironment (instantiateSubstitution arguments)
      (mapTypeEnvironment (shiftTypeSubstitutionN arguments.length) environment) = environment := by
  simpa only [liftSubN, mapTypeEnvironment] using
    (show (environment.map (subst (liftSubN 0 (shiftTypeSubstitutionN arguments.length)))).map
      (subst (liftSubN 0 (instantiateSubstitution arguments))) = environment by
      simp [List.map_map, Function.comp_def])

theorem mapGraphEnvironment_cancel (arguments : List Ty) (environment : GraphEnvironment) :
    mapGraphEnvironment (instantiateSubstitution arguments)
      (mapGraphEnvironment (shiftTypeSubstitutionN arguments.length) environment) = environment := by
  simp only [mapGraphEnvironment, List.map_map, Function.comp_def]
  apply (map_eq_self_iff _ _).mpr
  intro entry _
  rcases entry with ⟨identity, ty⟩
  have cancel := subst_liftSubN_cancel 0 arguments ty
  simpa only [liftSubN, Function.comp_apply, Prod.mk.injEq, true_and] using cancel

/-- The value-level administrative beta step, before any Force/Delay step. -/
def typeBetaValue : Value → Option Value
  | .typeApplication (.typeAbstraction body) argument =>
      some (mapPaperValue (instantiateSubstitution [argument]) body)
  | _ => none

/-- Lift only the type-beta step into the operand of Force. -/
def typeBetaForce : Computation → Option Computation
  | .force value => (typeBetaValue value).map Computation.force
  | _ => none

theorem typeBetaValue_shape (body : Value) (argument : Ty) :
    typeBetaValue (.typeApplication (.typeAbstraction body) argument) =
      some (mapPaperValue (instantiateSubstitution [argument]) body) := rfl

/-- Apply simultaneous substitution, then restore all three shared contexts. -/
theorem instantiate_body {d : DeclarationTable} {g : GraphEnvironment}
    {e : TypeEnvironment} {body : Value} {bodyType : Ty} (argument : Ty)
    (hb : PaperValueTyped (mapDeclarationTable shiftTypeSubstitution d)
      (mapGraphEnvironment shiftTypeSubstitution g)
      (mapTypeEnvironment shiftTypeSubstitution e) body bodyType) :
    PaperValueTyped d g e (mapPaperValue (instantiateSubstitution [argument]) body)
      (instantiateType [argument] bodyType) := by
  have transported := PaperValueTyped.subst_explicit
    (instantiateSubstitution [argument]) hb
  have hd := mapDeclarationTable_cancel 0 [argument] d
  change mapDeclarationTable (instantiateSubstitution [argument])
    (mapDeclarationTable shiftTypeSubstitution d) = d at hd
  have hg := mapGraphEnvironment_cancel [argument] g
  change mapGraphEnvironment (instantiateSubstitution [argument])
    (mapGraphEnvironment shiftTypeSubstitution g) = g at hg
  have he := mapTypeEnvironment_cancel [argument] e
  change mapTypeEnvironment (instantiateSubstitution [argument])
    (mapTypeEnvironment shiftTypeSubstitution e) = e at he
  simpa only [hd, hg, he, instantiateType] using transported

theorem typeBetaValue_applicable {d g e body argument resultType}
    (hv : PaperValueTyped d g e
      (.typeApplication (.typeAbstraction body) argument) resultType) :
    typeBetaValue (.typeApplication (.typeAbstraction body) argument) =
        some (mapPaperValue (instantiateSubstitution [argument]) body) ∧
      PaperValueTyped d g e (mapPaperValue (instantiateSubstitution [argument]) body)
        resultType := by
  cases hv with
  | typeApplication abstraction =>
      cases abstraction with
      | typeAbstraction hb => exact ⟨rfl, instantiate_body argument hb⟩

theorem typeBetaValue_preservation {d g e value next resultType}
    (hv : PaperValueTyped d g e value resultType)
    (hs : typeBetaValue value = some next) :
    PaperValueTyped d g e next resultType := by
  cases value with
  | typeApplication function argument =>
      cases function with
      | typeAbstraction body =>
          have happ := typeBetaValue_applicable hv
          have heq := Option.some.inj (happ.1.symm.trans hs)
          exact heq ▸ happ.2
      | _ => simp [typeBetaValue] at hs
  | _ => simp [typeBetaValue] at hs

theorem typeBetaForce_preservation {d g e source next resultType}
    (hc : PaperComputationTyped d g e source resultType)
    (hs : typeBetaForce source = some next) :
    PaperComputationTyped d g e next resultType := by
  cases source with
  | force value =>
      cases hc with
      | force hv =>
          cases hb : typeBetaValue value with
          | none => simp [typeBetaForce, hb] at hs
          | some value' =>
              have heq : Computation.force value' = next := by
                simpa [typeBetaForce, hb] using hs
              exact heq ▸ PaperComputationTyped.force (typeBetaValue_preservation hv hb)
  | _ => simp [typeBetaForce] at hs

/-- Keep both the beta endpoint and the subsequent Force/Delay endpoint typed. -/
theorem force_typeBeta_delay {d g e body argument resultType}
    (hc : PaperComputationTyped d g e
      (.force (.typeApplication (.typeAbstraction (.delay body)) argument)) resultType) :
    let body' := mapPaperComputation (instantiateSubstitution [argument]) body
    typeBetaForce (.force (.typeApplication (.typeAbstraction (.delay body)) argument)) =
        some (.force (.delay body')) ∧
      PaperComputationTyped d g e (.force (.delay body')) resultType ∧
      PaperCoreStep.step (.force (.delay body')) = some body' ∧
      PaperComputationTyped d g e body' resultType := by
  dsimp
  have beta : typeBetaForce
      (.force (.typeApplication (.typeAbstraction (.delay body)) argument)) =
      some (.force (.delay (mapPaperComputation (instantiateSubstitution [argument]) body))) := by
    simp [typeBetaForce, typeBetaValue, mapPaperValue]
  have hmid := typeBetaForce_preservation hc beta
  exact ⟨beta, hmid, rfl, PaperCoreStep.preservation hmid rfl⟩

/-- Response and result are independently instantiated at the same beta step. -/
theorem typeBetaContinuation_applicable {d g e owners binder body responseType resultType}
    (argument : Ty)
    (hb : PaperComputationTyped (mapDeclarationTable shiftTypeSubstitution d)
      (mapGraphEnvironment shiftTypeSubstitution g)
      (responseType :: mapTypeEnvironment shiftTypeSubstitution e) body resultType) :
    let value' := Value.continuation owners binder
      (mapPaperComputation (instantiateSubstitution [argument]) body)
    typeBetaValue (.typeApplication
      (.typeAbstraction (.continuation owners binder body)) argument) = some value' ∧
      PaperValueTyped d g e value'
        (.kont (instantiateType [argument] responseType)
          (instantiateType [argument] resultType)) := by
  have hv : PaperValueTyped d g e
      (.typeApplication (.typeAbstraction (.continuation owners binder body)) argument)
      (instantiateType [argument] (.kont responseType resultType)) :=
    .typeApplication (.typeAbstraction (.continuation (.continuation hb)))
  simpa only [mapPaperValue, instantiateType, subst] using typeBetaValue_applicable hv

/-- Instantiation remains capture-avoiding under nested universal and recursive binders. -/
theorem nested_poly_mu (argument : Ty) :
    instantiateType [argument] (.poly (.mu (.callable (.var 2) (.var 0)))) =
      .poly (.mu (.callable (mapVars Nat.succ (mapVars Nat.succ argument)) (.var 0))) := rfl

/-- An ambient variable stays shared instead of becoming the beta argument. -/
theorem shared_variable_countercase (argument : Ty) :
    instantiateType [argument] (.poly (.mu (.var 3))) = .poly (.mu (.var 2)) := rfl

end YulangClosure.PaperTypes.PaperTypeApplicationPreservation
