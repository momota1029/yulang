import YulangClosure.PaperExecutionSyntax

/-!
Unfinished simultaneous type-substitution attempt for the explicitly
represented core typing rules in `PaperExecutionSyntax`. This revision does
not compile: mutual induction over the four judgments and several constructor
cases still need repair. It is not a proof of the full paper theorem. The
source module lists omitted rules and a placeholder graph guard that must be
resolved before the parent can close.
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
    | fail => simpa [mapPaperComputation, subst] using PaperComputationTyped.fail
end

end YulangClosure.PaperTypes
