import YulangClosure.PaperExecutionSyntax

/-!
Unfinished simultaneous type-substitution construction for the explicitly
represented partial paper judgments, including records, required projection,
and declared lookup. The standalone record-map equality is checked, but the
mutual proof still has an index mismatch; this module does not compile. R6 and
R7 handoffs preserve diagnostics. This is not the full paper theorem; omitted
rules and graph/source correspondence remain open.
-/
namespace YulangClosure.PaperTypes

theorem argsSyntax_subst (σ : Nat → Ty) (types : List Ty) :
    argsSyntax (types.map (subst σ)) = subst σ (argsSyntax types) := by
  induction types with
  | nil => rfl
  | cons head tail ih => simp [argsSyntax, subst, ih]

@[simp] theorem literalType_subst (σ : Nat → Ty) (literal : Literal) :
    subst σ (literalType literal) = literalType literal := by
  cases literal <;> rfl

@[simp] theorem lookupTypeEnvironment_subst (σ : Nat → Ty)
    (environment : TypeEnvironment) (index : Nat) :
    lookupTypeEnvironment (mapTypeEnvironment σ environment) index =
      (lookupTypeEnvironment environment index).map (subst σ) := by
  induction environment generalizing index with
  | nil => cases index <;> rfl
  | cons head tail ih =>
      cases index with
      | zero => rfl
      | succ index => exact ih index

@[simp] theorem lookupGraphEnvironment_subst (σ : Nat → Ty)
    (environment : GraphEnvironment) (index : Nat) :
    lookupGraphEnvironment (mapGraphEnvironment σ environment) index =
      (lookupGraphEnvironment environment index).map (subst σ) := by
  induction environment with
  | nil => rfl
  | cons head tail ih =>
      cases head with
      | mk identity ty =>
          by_cases h : identity = index
          · simp [lookupGraphEnvironment, mapGraphEnvironment, h]
          · simp [lookupGraphEnvironment, mapGraphEnvironment, h]
            change lookupGraphEnvironment (mapGraphEnvironment σ tail) index =
              (lookupGraphEnvironment tail index).map (subst σ)
            rw [ih]

theorem RecordShape.subst (σ : Nat → Ty) {recordType : Ty} {labels required : List Label}
    (shape : RecordShape recordType labels required) :
    RecordShape (subst σ recordType) labels required := by
  induction shape with
  | nil => exact .nil
  | required _ unique ih => exact .required ih unique
  | optional _ unique ih => exact .optional ih unique

theorem RecordField.subst (σ : Nat → Ty) {recordType fieldType : Ty}
    {label : Label} {presence : Presence}
    (field : RecordField recordType label presence fieldType) :
    RecordField (subst σ recordType) label presence (subst σ fieldType) := by
  induction field with
  | here => exact .here
  | there _ ih => exact .there ih

@[simp] theorem mapRecordFields_labels (σ : Nat → Ty)
    (fields : List (Label × Presence × Value)) :
    (mapRecordFields σ fields).map Prod.fst = fields.map Prod.fst := by
  simp [mapRecordFields, List.map_map, Function.comp_def]

mutual
  theorem ValuesTyped.subst (σ : Nat → Ty) {declarations : DeclarationTable}
      {graphTypes : GraphEnvironment} {environment : TypeEnvironment}
      {values : List Value} {types : List Ty}
      (derivation : ValuesTyped declarations graphTypes environment values types) :
      ValuesTyped (mapDeclarationTable σ declarations) (mapGraphEnvironment σ graphTypes)
        (mapTypeEnvironment σ environment) (values.map (mapPaperValue σ)) (types.map (subst σ)) := by
    cases derivation with
    | nil => exact .nil
    | cons value values =>
        simpa [mapTypeEnvironment] using
          ValuesTyped.cons (PaperValueTyped.subst σ value) (ValuesTyped.subst σ values)

  theorem ValuesAllTyped.subst (σ : Nat → Ty) {declarations : DeclarationTable}
      {graphTypes : GraphEnvironment} {environment : TypeEnvironment}
      {values : List Value} {ty : Ty}
      (derivation : ValuesAllTyped declarations graphTypes environment values ty) :
      ValuesAllTyped (mapDeclarationTable σ declarations) (mapGraphEnvironment σ graphTypes)
        (mapTypeEnvironment σ environment) (values.map (mapPaperValue σ)) (subst σ ty) := by
    cases derivation with
    | nil => exact .nil
    | cons value values =>
        simpa [mapTypeEnvironment] using
          ValuesAllTyped.cons (PaperValueTyped.subst σ value) (ValuesAllTyped.subst σ values)

  theorem RecordPayloadsTyped.subst (σ : Nat → Ty) {declarations : DeclarationTable}
      {graphTypes : GraphEnvironment} {environment : TypeEnvironment}
      {fields : List (Label × Presence × Value)} {recordType : Ty}
      (derivation : RecordPayloadsTyped declarations graphTypes environment fields recordType) :
      RecordPayloadsTyped (mapDeclarationTable σ declarations) (mapGraphEnvironment σ graphTypes)
        (mapTypeEnvironment σ environment) (mapRecordFields σ fields) (subst σ recordType) := by
    cases derivation with
    | nil => exact .nil
    | cons field value fields =>
        exact .cons (RecordField.subst σ field) (PaperValueTyped.subst σ value)
          (RecordPayloadsTyped.subst σ fields)

  theorem PaperValueTyped.subst (σ : Nat → Ty) {declarations : DeclarationTable}
      {graphTypes : GraphEnvironment} {environment : TypeEnvironment}
      {value : Value} {ty : Ty}
      (derivation : PaperValueTyped declarations graphTypes environment value ty) :
      PaperValueTyped (mapDeclarationTable σ declarations) (mapGraphEnvironment σ graphTypes)
        (mapTypeEnvironment σ environment) (mapPaperValue σ value) (subst σ ty) := by
    cases derivation with
    | «variable» lookup =>
        simp only [mapPaperValue]
        apply PaperValueTyped.variable
        simpa [lookupTypeEnvironment_subst] using congrArg (Option.map (subst σ)) lookup
    | graphReference lookup =>
        simp only [mapPaperValue]
        apply PaperValueTyped.graphReference
        simpa [lookupGraphEnvironment_subst] using congrArg (Option.map (subst σ)) lookup
    | literal =>
        simpa [mapPaperValue] using (PaperValueTyped.literal :
          PaperValueTyped (mapDeclarationTable σ declarations) (mapGraphEnvironment σ graphTypes)
            (mapTypeEnvironment σ environment) _ _)
    | tuple values =>
        simpa [mapPaperValue, argsSyntax_subst] using
          (PaperValueTyped.tuple (ValuesTyped.subst σ values))
    | sequence values =>
        simpa [mapPaperValue, mapDeclarationTable, subst] using
          PaperValueTyped.sequence (ValuesAllTyped.subst σ values)
    | @record _ fields recordType labels required shape unique allRequired payloads =>
        have unique' := unique
        have required' := allRequired
        rw [← mapRecordFields_labels σ] at unique'
        have required'' : ∀ label, label ∈ required →
            label ∈ (mapRecordFields σ fields).map Prod.fst := by
          simpa only [mapRecordFields_labels] using required'
        simpa [mapPaperValue, mapRecordFields, List.attach_map_val] using
          PaperValueTyped.record (RecordShape.subst σ shape) unique' required''
            (RecordPayloadsTyped.subst σ payloads)
    | delay body =>
        simpa [mapPaperValue, subst] using PaperValueTyped.delay (PaperComputationTyped.subst σ body)
    | valueLambda body =>
        simpa [mapPaperValue, mapPaperComputation, mapTypeEnvironment, subst] using
          PaperValueTyped.valueLambda (PaperComputationTyped.subst σ body)
    | computationLambda body =>
        simpa [mapPaperValue, mapPaperComputation, mapTypeEnvironment, subst] using
          PaperValueTyped.computationLambda (PaperComputationTyped.subst σ body)
    | injectLeft value =>
        simpa [mapPaperValue, subst] using PaperValueTyped.injectLeft (PaperValueTyped.subst σ value)
    | injectRight value =>
        simpa [mapPaperValue, subst] using PaperValueTyped.injectRight (PaperValueTyped.subst σ value)
    | both left right =>
        simpa [mapPaperValue, subst] using
          PaperValueTyped.both (PaperValueTyped.subst σ left) (PaperValueTyped.subst σ right)
    | topView value =>
        simpa [mapPaperValue, subst] using PaperValueTyped.topView (PaperValueTyped.subst σ value)
    | view value =>
        simpa [mapPaperValue] using PaperValueTyped.view (PaperValueTyped.subst σ value)

  theorem PaperComputationTyped.subst (σ : Nat → Ty) {declarations : DeclarationTable}
      {graphTypes : GraphEnvironment} {environment : TypeEnvironment}
      {computation : Computation} {ty : Ty}
      (derivation : PaperComputationTyped declarations graphTypes environment computation ty) :
      PaperComputationTyped (mapDeclarationTable σ declarations) (mapGraphEnvironment σ graphTypes)
        (mapTypeEnvironment σ environment) (mapPaperComputation σ computation) (subst σ ty) := by
    cases derivation with
    | ret value =>
        simpa [mapPaperComputation] using PaperComputationTyped.ret (PaperValueTyped.subst σ value)
    | letE first body =>
        simpa [mapPaperComputation, mapTypeEnvironment] using
          PaperComputationTyped.letE (PaperComputationTyped.subst σ first)
            (PaperComputationTyped.subst σ body)
    | force thunk =>
        simpa [mapPaperComputation] using PaperComputationTyped.force (PaperValueTyped.subst σ thunk)
    | call function thunk =>
        simpa [mapPaperComputation] using
          PaperComputationTyped.call (PaperValueTyped.subst σ function)
            (PaperValueTyped.subst σ thunk)
    | field value field =>
        simpa [mapPaperComputation] using
          PaperComputationTyped.field (PaperValueTyped.subst σ value) (RecordField.subst σ field)
    | lookup value field =>
        simpa [mapPaperComputation, subst] using
          PaperComputationTyped.lookup (PaperValueTyped.subst σ value) (RecordField.subst σ field)
    | fail => simpa [mapPaperComputation, subst] using PaperComputationTyped.fail
end

end YulangClosure.PaperTypes
