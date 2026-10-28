import YulangClosure.PaperExecutionBinderLaws
import YulangClosure.DeclSubst

/-!
Arbitrary type-substitution transport for the explicitly represented partial
paper typing judgments, including records, required projection, and declared
lookup. The represented judgments are only a subset of the full paper system;
full source/native correspondence and omitted rules remain open.
-/
namespace YulangClosure.PaperTypes

theorem typingArgsSyntax_subst (σ : Nat → Ty) (types : List Ty) :
    argsSyntax (types.map (subst σ)) = subst σ (argsSyntax types) := by
  induction types with
  | nil => rfl
  | cons head tail ih => simp [argsSyntax, subst, ih]

/-- Simultaneous substitution preserves the cons-derived tuple binder order. -/
theorem mapTypeEnvironment_extendTupleEnvironment (σ : Nat → Ty)
    (types : List Ty) (environment : TypeEnvironment) :
    mapTypeEnvironment σ (extendTupleEnvironment types environment) =
      extendTupleEnvironment (types.map (subst σ)) (mapTypeEnvironment σ environment) := by
  simp [mapTypeEnvironment, extendTupleEnvironment]

theorem instantiateType_subst (arguments : List Ty) (σ : Nat → Ty)
    (arity : Nat) (arityEq : arguments.length = arity) (body : Ty) :
    subst σ (instantiateType arguments body) =
      instantiateType (mapOperationArguments σ arguments)
        (subst (liftSubN arity σ) body) := by
  unfold instantiateType
  calc
    subst σ (subst (instantiateSubstitution arguments) body) =
        subst (fun i => subst σ (instantiateSubstitution arguments i)) body :=
      subst_comp (instantiateSubstitution arguments) σ body
    _ = subst (fun i =>
          subst (instantiateSubstitution (mapOperationArguments σ arguments))
            (liftSubN arity σ i)) body := by
      rw [instantiateSubstitution_commutes arguments σ arity arityEq]
    _ = subst (instantiateSubstitution (mapOperationArguments σ arguments))
          (subst (liftSubN arity σ) body) :=
      (subst_comp (liftSubN arity σ)
        (instantiateSubstitution (mapOperationArguments σ arguments)) body).symm

/-- All formal types use the very same invocation instance as the result. -/
theorem instantiateFormalTypes_subst (arguments : List Ty) (σ : Nat → Ty)
    (arity : Nat) (arityEq : arguments.length = arity) (formals : List Ty) :
    (formals.map (instantiateType arguments)).map (subst σ) =
      (formals.map (subst (liftSubN arity σ))).map
        (instantiateType (mapTypeArguments σ arguments)) := by
  induction formals with
  | nil => rfl
  | cons formal rest ih =>
      simp only [List.map_cons, instantiateType_subst arguments σ arity arityEq,
        mapOperationArguments, mapTypeArguments, ih]

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

theorem OperationDeclarationResolved.typeTransport (σ : Nat → Ty)
    {operations : List OperationDeclaration} {operation : DeclarationId}
    {declaration : OperationDeclaration}
    (resolved : OperationDeclarationResolved operations operation declaration) :
    OperationDeclarationResolved
      (operations.map (OperationDeclaration.substAmbient σ)) operation
      (declaration.substAmbient σ) := by
  rcases resolved with ⟨hmember, hidentity, hunique⟩
  refine ⟨List.mem_map.mpr ⟨declaration, hmember, rfl⟩, ?_, ?_⟩
  · simpa [OperationDeclaration.substAmbient] using hidentity
  · intro other hother hotherIdentity
    rcases List.mem_map.mp hother with ⟨original, horiginal, rfl⟩
    have horiginalIdentity : original.identity = operation := by
      simpa [OperationDeclaration.substAmbient] using hotherIdentity
    have heq := hunique original horiginal horiginalIdentity
    subst original
    rfl

@[simp] theorem templateIdentity_mapTemplateBody (σ : Nat → Ty) (declaration : TemplateBody) :
    templateIdentity (mapTemplateBody σ declaration) = templateIdentity declaration := by
  cases declaration
  rfl

/-- Mapping retains the unique code identity and the entire mapped entry. -/
theorem TemplateDeclarationResolved.typeTransport (σ : Nat → Ty)
    {templates : List TemplateBody} {identity : Nat} {declaration : TemplateBody}
    (resolved : TemplateDeclarationResolved templates identity declaration) :
    TemplateDeclarationResolved (templates.map (mapTemplateBody σ)) identity
      (mapTemplateBody σ declaration) := by
  rcases resolved with ⟨hmember, hidentity, hunique⟩
  refine ⟨List.mem_map.mpr ⟨declaration, hmember, rfl⟩, ?_, ?_⟩
  · simpa only [templateIdentity_mapTemplateBody] using hidentity
  · intro other hother hotherIdentity
    rcases List.mem_map.mp hother with ⟨original, horiginal, rfl⟩
    have horiginalIdentity : templateIdentity original = identity := by
      simpa only [templateIdentity_mapTemplateBody] using hotherIdentity
    have heq := hunique original horiginal horiginalIdentity
    subst original
    rfl

@[simp] theorem mapRecordFields_labels (σ : Nat → Ty)
    (fields : List (Label × Presence × Value)) :
    (mapRecordFields σ fields).map Prod.fst = fields.map Prod.fst := by
  simp [mapRecordFields, List.map_map, Function.comp_def]

theorem mapPaperValue_record_eq (σ : Nat → Ty) (fields : List (Label × Presence × Value)) :
    mapPaperValue σ (.record fields) = .record (mapRecordFields σ fields) := by
  simp only [mapPaperValue]
  exact congrArg Value.record (List.attach_map_val (l := fields)
    (f := fun field : Label × Presence × Value =>
      (field.1, field.2.1, mapPaperValue σ field.2.2)))

theorem PaperValueTyped.subst_explicit (σ : Nat → Ty) {declarations : DeclarationTable}
    {graphTypes : GraphEnvironment} {environment : TypeEnvironment}
    {value : Value} {ty : Ty}
    (derivation : PaperValueTyped declarations graphTypes environment value ty) :
    PaperValueTyped (mapDeclarationTable σ declarations) (mapGraphEnvironment σ graphTypes)
      (mapTypeEnvironment σ environment) (mapPaperValue σ value) (subst σ ty) := by
  exact PaperValueTyped.rec
    (motive_1 := fun declarations graphTypes e values types _ => ∀ σ, ValuesTyped (mapDeclarationTable σ declarations)
      (mapGraphEnvironment σ graphTypes) (mapTypeEnvironment σ e)
      (values.map (mapPaperValue σ)) (types.map (subst σ)))
    (motive_2 := fun declarations graphTypes e values ty _ => ∀ σ, ValuesAllTyped (mapDeclarationTable σ declarations)
      (mapGraphEnvironment σ graphTypes) (mapTypeEnvironment σ e)
      (values.map (mapPaperValue σ)) (subst σ ty))
    (motive_3 := fun declarations graphTypes e fields ty _ => ∀ σ, RecordPayloadsTyped (mapDeclarationTable σ declarations)
      (mapGraphEnvironment σ graphTypes) (mapTypeEnvironment σ e)
      (mapRecordFields σ fields) (subst σ ty))
    (motive_4 := fun declarations graphTypes e value ty _ => ∀ σ, PaperValueTyped (mapDeclarationTable σ declarations)
      (mapGraphEnvironment σ graphTypes) (mapTypeEnvironment σ e)
      (mapPaperValue σ value) (subst σ ty))
    (motive_5 := fun declarations graphTypes e computation ty _ => ∀ σ, PaperComputationTyped (mapDeclarationTable σ declarations)
      (mapGraphEnvironment σ graphTypes) (mapTypeEnvironment σ e)
      (mapPaperComputation σ computation) (subst σ ty))
    (motive_6 := fun declarations graphTypes e continuation response result _ => ∀ σ,
      PaperContinuationTyped (mapDeclarationTable σ declarations) (mapGraphEnvironment σ graphTypes)
        (mapTypeEnvironment σ e) (mapPaperValue σ continuation) (subst σ response) (subst σ result))
    (by intro declarations graphTypes environment σ; exact ValuesTyped.nil)
    (by intro declarations graphTypes environment value values ty types hvalue hvalues ihValue ihValues σ
        have ihValue := ihValue σ
        have ihValues := ihValues σ
        simpa [mapTypeEnvironment] using ValuesTyped.cons ihValue ihValues)
    (by intro declarations graphTypes environment ty σ; exact ValuesAllTyped.nil)
    (by intro declarations graphTypes environment value values ty hvalue hvalues ihValue ihValues σ
        have ihValue := ihValue σ
        have ihValues := ihValues σ
        simpa [mapTypeEnvironment] using ValuesAllTyped.cons ihValue ihValues)
    (by intro declarations graphTypes environment recordType σ; exact RecordPayloadsTyped.nil)
    (by intro declarations graphTypes label tag value fields recordType presence fieldType environment hfield hvalue hfields ihValue ihFields σ
        have ihValue := ihValue σ
        have ihFields := ihFields σ
        simpa [mapRecordFields] using RecordPayloadsTyped.cons
          (RecordField.subst σ hfield) ihValue ihFields)
    (by intro declarations graphTypes environment index ty lookup σ
        simp only [mapPaperValue]
        apply PaperValueTyped.variable
        simpa [lookupTypeEnvironment_subst] using congrArg (Option.map (subst σ)) lookup)
    (by intro declarations graphTypes environment identity ty lookup σ
        simp only [mapPaperValue]
        apply PaperValueTyped.graphReference
        simpa [lookupGraphEnvironment_subst] using congrArg (Option.map (subst σ)) lookup)
    (by intro declarations graphTypes environment literal σ
        simpa [mapPaperValue] using (PaperValueTyped.literal :
          PaperValueTyped (mapDeclarationTable σ declarations) (mapGraphEnvironment σ graphTypes)
            (mapTypeEnvironment σ environment) _ _))
    (by intro declarations graphTypes environment values types hvalues ihValues σ
        have ihValues := ihValues σ
        simpa [mapPaperValue, typingArgsSyntax_subst] using PaperValueTyped.tuple ihValues)
    (by intro declarations graphTypes environment values elementType hvalues ihValues σ
        have ihValues := ihValues σ
        simpa [mapPaperValue, mapDeclarationTable, subst] using PaperValueTyped.sequence ihValues)
    (by intro declarations graphTypes environment fields recordType labels required shape unique allRequired hfields ihFields σ
        have ihFields := ihFields σ
        have unique' : (mapRecordFields σ fields).map Prod.fst |>.Nodup := by
          simpa only [mapRecordFields_labels] using unique
        have required' : ∀ label, label ∈ required → label ∈ (mapRecordFields σ fields).map Prod.fst := by
          simpa only [mapRecordFields_labels] using allRequired
        have result := PaperValueTyped.record (RecordShape.subst σ shape) unique' required' ihFields
        simpa only [mapPaperValue_record_eq] using result)
    (by intro declarations graphTypes environment body resultType hbody ihBody σ
        have ihBody := ihBody σ
        simpa [mapPaperValue, subst] using PaperValueTyped.delay ihBody)
    (by intro declarations graphTypes environment profile parameter body inputType outputType hbody ihBody σ
        have ihBody := ihBody σ
        simpa [mapPaperValue, mapPaperComputation, mapTypeEnvironment, subst] using
          PaperValueTyped.valueLambda ihBody)
    (by intro declarations graphTypes environment profile parameter body inputType outputType hbody ihBody σ
        have ihBody := ihBody σ
        simpa [mapPaperValue, mapPaperComputation, mapTypeEnvironment, subst] using
          PaperValueTyped.computationLambda ihBody)
    (by intro declarations graphTypes environment function argumentAdapter resultAdapter
          inputType outputType adaptedInputType adaptedOutputType
          hfunction hargument hresult ihFunction ihArgument ihResult σ
        simpa only [mapPaperValue, subst, mapTypeEnvironment, List.map_cons] using
          PaperValueTyped.wrap (ihFunction σ) (ihArgument σ) (ihResult σ))
    (by intro declarations graphTypes environment value left right hvalue ihValue σ
        have ihValue := ihValue σ
        simpa [mapPaperValue, subst] using PaperValueTyped.injectLeft ihValue)
    (by intro declarations graphTypes environment value left right hvalue ihValue σ
        have ihValue := ihValue σ
        simpa [mapPaperValue, subst] using PaperValueTyped.injectRight ihValue)
    (by intro declarations graphTypes environment value left right hleft hright ihLeft ihRight σ
        have ihLeft := ihLeft σ
        have ihRight := ihRight σ
        simpa [mapPaperValue, subst] using PaperValueTyped.both ihLeft ihRight)
    (by intro declarations graphTypes environment value ty hvalue ihValue σ
        have ihValue := ihValue σ
        simpa [mapPaperValue, subst] using PaperValueTyped.topView ihValue)
    (by intro declarations graphTypes environment metadata value ty hvalue ihValue σ
        have ihValue := ihValue σ
        simpa [mapPaperValue] using PaperValueTyped.view ihValue)
    (by intro declarations graphTypes environment owners binder body responseType resultType hcontinuation ihContinuation σ
        have ihContinuation := ihContinuation σ
        have ihContinuation' :
            PaperContinuationTyped (mapDeclarationTable σ declarations)
              (mapGraphEnvironment σ graphTypes) (mapTypeEnvironment σ environment)
              (.continuation owners binder (mapPaperComputation σ body))
              (subst σ responseType) (subst σ resultType) := by
          simpa [mapPaperValue] using ihContinuation
        simpa [mapPaperValue, subst] using PaperValueTyped.continuation ihContinuation')
    (by intro declarations graphTypes environment body bodyType hbody ihBody σ
        have transported := ihBody (liftSub σ)
        change PaperValueTyped
          (mapDeclarationTable (liftSub σ) (mapDeclarationTable shiftTypeSubstitution declarations))
          (mapGraphEnvironment (liftSub σ) (mapGraphEnvironment shiftTypeSubstitution graphTypes))
          (mapTypeEnvironment (liftSub σ) (mapTypeEnvironment shiftTypeSubstitution environment))
          (mapPaperValue (liftSub σ) body) (subst (liftSub σ) bodyType) at transported
        rw [show mapDeclarationTable (liftSub σ) (mapDeclarationTable shiftTypeSubstitution declarations) =
            mapDeclarationTable shiftTypeSubstitution (mapDeclarationTable σ declarations) from
              mapDeclarationTable_shift_substitution_commutes 0 σ declarations,
          mapGraphEnvironment_shift_substitution_commutes,
          mapTypeEnvironment_shift_substitution_commutes] at transported
        simpa only [mapPaperValue, subst] using PaperValueTyped.typeAbstraction transported)
    (by intro declarations graphTypes environment function body argument hfunction ihFunction σ
        have ihFunction := ihFunction σ
        have ihFunction' :
            PaperValueTyped (mapDeclarationTable σ declarations) (mapGraphEnvironment σ graphTypes)
              (mapTypeEnvironment σ environment) (mapPaperValue σ function)
              (.poly (subst (liftSub σ) body)) := by
          simpa [subst] using ihFunction
        have commuteRaw := instantiateType_subst [argument] σ 1 rfl body
        have commute :
            subst σ (instantiateType [argument] body) =
              instantiateType [subst σ argument] (subst (liftSub σ) body) := by
          simpa [instantiateType, mapOperationArguments, liftSubN] using commuteRaw
        have result := PaperValueTyped.typeApplication
          (argument := subst σ argument) ihFunction'
        have result' :
            PaperValueTyped (mapDeclarationTable σ declarations) (mapGraphEnvironment σ graphTypes)
              (mapTypeEnvironment σ environment)
              (mapPaperValue σ (.typeApplication function argument))
              (instantiateType [subst σ argument] (subst (liftSub σ) body)) := by
          simpa [mapPaperValue] using result
        rw [commute]
        exact result')
    (by intro declarations graphTypes environment value body hvalue ihValue σ
        have ihValue := ihValue σ
        have commuteRaw := instantiateType_subst [.mu body] σ 1 rfl body
        have commute :
            subst σ (instantiateType [.mu body] body) =
              instantiateType [.mu (subst (liftSub σ) body)] (subst (liftSub σ) body) := by
          simpa [instantiateType, mapOperationArguments, liftSubN, subst] using commuteRaw
        have ihValue' :
            PaperValueTyped (mapDeclarationTable σ declarations) (mapGraphEnvironment σ graphTypes)
              (mapTypeEnvironment σ environment) (mapPaperValue σ value)
              (instantiateType [.mu (subst (liftSub σ) body)] (subst (liftSub σ) body)) := by
          rw [← commute]
          exact ihValue
        simpa [mapPaperValue, subst] using PaperValueTyped.roll ihValue')
    (by intro declarations graphTypes environment value ty hvalue ihValue σ
        have ihValue := ihValue σ
        simpa [mapPaperComputation] using PaperComputationTyped.ret ihValue)
    (by intro declarations graphTypes environment first body firstType resultType hfirst hbody ihFirst ihBody σ
        have ihFirst := ihFirst σ
        have ihBody := ihBody σ
        simpa [mapPaperComputation, mapTypeEnvironment] using
          PaperComputationTyped.letE ihFirst ihBody)
    (by intro declarations graphTypes environment thunk resultType hthunk ihThunk σ
        have ihThunk := ihThunk σ
        simpa [mapPaperComputation] using PaperComputationTyped.force ihThunk)
    (by intro declarations graphTypes environment function thunk argumentType resultType hfunction hthunk ihFunction ihThunk σ
        have ihFunction := ihFunction σ
        have ihThunk := ihThunk σ
        simpa [mapPaperComputation] using PaperComputationTyped.call ihFunction ihThunk)
    (by intro declarations graphTypes environment tuple binders body types resultType
          arity htuple hbody ihTuple ihBody σ
        have arity' : binders.length = (types.map (subst σ)).length := by
          simpa only [List.length_map] using arity
        have tupleTyping := ihTuple σ
        rw [← typingArgsSyntax_subst σ types] at tupleTyping
        have bodyTyping := ihBody σ
        rw [mapTypeEnvironment_extendTupleEnvironment] at bodyTyping
        simpa only [mapPaperComputation] using
          PaperComputationTyped.split arity' tupleTyping bodyTyping)
    (by intro declarations graphTypes environment value leftBinder left rightBinder right
          leftType rightType resultType hvalue hleft hright ihValue ihLeft ihRight σ
        simpa only [mapPaperComputation, mapTypeEnvironment, List.map_cons] using
          PaperComputationTyped.unionCase (ihValue σ) (ihLeft σ) (ihRight σ))
    (by intro declarations graphTypes environment value recordType label fieldType hvalue hfield ihValue σ
        have ihValue := ihValue σ
        simpa [mapPaperComputation] using
          PaperComputationTyped.field ihValue (RecordField.subst σ hfield))
    (by intro declarations graphTypes environment value recordType label presence fieldType hvalue hfield ihValue σ
        have ihValue := ihValue σ
        simpa [mapPaperComputation, subst] using
          PaperComputationTyped.lookup ihValue (RecordField.subst σ hfield))
    (by intro declarations graphTypes environment operation arguments payload declaration resolved arity payloadTyping ihPayload σ
        have ihPayload := ihPayload σ
        have resolved' := OperationDeclarationResolved.typeTransport σ resolved
        have commute := operation_declaration_instantiation_subst declaration arguments σ arity
        have payloadType :
            subst σ (declaration.instantiate arguments).payloadType =
              ((declaration.substAmbient σ).instantiate (mapOperationArguments σ arguments)).payloadType := by
          simpa [OperationInstance.subst] using congrArg OperationInstance.payloadType commute
        have responseType :
            subst σ (declaration.instantiate arguments).responseType =
              ((declaration.substAmbient σ).instantiate (mapOperationArguments σ arguments)).responseType := by
          simpa [OperationInstance.subst] using congrArg OperationInstance.responseType commute
        have payloadTyping' :
            PaperValueTyped (mapDeclarationTable σ declarations) (mapGraphEnvironment σ graphTypes)
              (mapTypeEnvironment σ environment) (mapPaperValue σ payload)
              ((declaration.substAmbient σ).instantiate (mapOperationArguments σ arguments)).payloadType := by
          rw [← payloadType]
          exact ihPayload
        have arity' : (mapOperationArguments σ arguments).length =
            (declaration.substAmbient σ).typeArity := by
          simp [mapOperationArguments, OperationDeclaration.substAmbient, arity]
        rw [responseType]
        simpa [mapPaperComputation, mapTypeArguments, mapOperationArguments] using
          PaperComputationTyped.perform resolved' arity' payloadTyping')
    (by intro declarations graphTypes environment opInstance payload continuation declaration arguments resultType
          resolved arity instanceEq payloadTyping continuationTyping ihPayload ihContinuation σ
        have ihPayload := ihPayload σ
        have ihContinuation := ihContinuation σ
        have resolved' := OperationDeclarationResolved.typeTransport σ resolved
        have commute := operation_declaration_instantiation_subst declaration arguments σ arity
        have instance' : opInstance.subst σ =
            (declaration.substAmbient σ).instantiate (mapOperationArguments σ arguments) := by
          rw [instanceEq]
          exact commute
        have payloadType :
            subst σ (declaration.instantiate arguments).payloadType =
              ((declaration.substAmbient σ).instantiate (mapOperationArguments σ arguments)).payloadType := by
          simpa [OperationInstance.subst] using congrArg OperationInstance.payloadType commute
        have responseType :
            subst σ (declaration.instantiate arguments).responseType =
              ((declaration.substAmbient σ).instantiate (mapOperationArguments σ arguments)).responseType := by
          simpa [OperationInstance.subst] using congrArg OperationInstance.responseType commute
        have payloadTyping' :
            PaperValueTyped (mapDeclarationTable σ declarations) (mapGraphEnvironment σ graphTypes)
              (mapTypeEnvironment σ environment) (mapPaperValue σ payload)
              ((declaration.substAmbient σ).instantiate (mapOperationArguments σ arguments)).payloadType := by
          rw [← payloadType]
          exact ihPayload
        have continuationTyping' :
            PaperContinuationTyped (mapDeclarationTable σ declarations) (mapGraphEnvironment σ graphTypes)
              (mapTypeEnvironment σ environment) (mapPaperValue σ continuation)
              ((declaration.substAmbient σ).instantiate (mapOperationArguments σ arguments)).responseType
              (subst σ resultType) := by
          rw [← responseType]
          exact ihContinuation
        have arity' : (mapOperationArguments σ arguments).length =
            (declaration.substAmbient σ).typeArity := by
          simp [mapOperationArguments, OperationDeclaration.substAmbient, arity]
        simpa [mapPaperComputation] using
          PaperComputationTyped.request resolved' arity' instance' payloadTyping' continuationTyping')
    (by intro declarations graphTypes environment continuation response responseType resultType hcontinuation hresponse
          ihContinuation ihResponse σ
        have ihContinuation := ihContinuation σ
        have ihResponse := ihResponse σ
        simpa [mapPaperComputation] using PaperComputationTyped.resume ihContinuation ihResponse)
    (by intro declarations graphTypes environment value body hvalue ihValue σ
        have ihValue := ihValue σ
        have commuteRaw := instantiateType_subst [.mu body] σ 1 rfl body
        have commute :
            subst σ (instantiateType [.mu body] body) =
              instantiateType [.mu (subst (liftSub σ) body)] (subst (liftSub σ) body) := by
          simpa [instantiateType, mapOperationArguments, liftSubN, subst] using commuteRaw
        have ihValue' :
            PaperValueTyped (mapDeclarationTable σ declarations) (mapGraphEnvironment σ graphTypes)
              (mapTypeEnvironment σ environment) (mapPaperValue σ value)
              (.mu (subst (liftSub σ) body)) := by
          simpa [subst] using ihValue
        have result := PaperComputationTyped.unroll ihValue'
        have result' :
            PaperComputationTyped (mapDeclarationTable σ declarations) (mapGraphEnvironment σ graphTypes)
              (mapTypeEnvironment σ environment) (mapPaperComputation σ (.unroll value))
              (instantiateType [.mu (subst (liftSub σ) body)] (subst (liftSub σ) body)) := by
          simpa [mapPaperComputation] using result
        rw [commute]
        exact result')
    (by intro declarations graphTypes environment identity typeArguments arguments
          typeArity formals result body resolved arity argumentsTyping ihArguments σ
        have resolved' := TemplateDeclarationResolved.typeTransport σ resolved
        have arity' : (mapTypeArguments σ typeArguments).length = typeArity := by
          simpa only [mapTypeArguments, List.length_map] using arity
        have argumentsTyping' :
            ValuesTyped (mapDeclarationTable σ declarations) (mapGraphEnvironment σ graphTypes)
              (mapTypeEnvironment σ environment) (arguments.map (mapPaperValue σ))
              ((formals.map (subst (liftSubN typeArity σ))).map
                (instantiateType (mapTypeArguments σ typeArguments))) := by
          rw [← instantiateFormalTypes_subst typeArguments σ typeArity arity formals]
          exact ihArguments σ
        have commute := instantiateType_subst typeArguments σ typeArity arity result
        rw [commute]
        simpa [mapPaperComputation, mapTemplateBody, mapTypeArguments, mapOperationArguments] using
          PaperComputationTyped.template resolved' arity' argumentsTyping')
    (by intro declarations graphTypes environment value left right hvalue ihValue σ
        simpa only [mapPaperComputation, subst] using
          PaperComputationTyped.chooseLeft (ihValue σ))
    (by intro declarations graphTypes environment value left right hvalue ihValue σ
        simpa only [mapPaperComputation, subst] using
          PaperComputationTyped.chooseRight (ihValue σ))
    (by intro declarations graphTypes environment value resultType hvalue ihValue σ
        simpa only [mapPaperComputation, subst] using
          PaperComputationTyped.absurd (resultType := subst σ resultType) (ihValue σ))
    (by intro declarations graphTypes environment metadata body resultType hbody ihBody σ
        simpa only [mapPaperComputation] using
          (PaperComputationTyped.expose (metadata := mapViewMetadata σ metadata) (ihBody σ)))
    (by intro declarations graphTypes environment reason ty σ; simpa [mapPaperComputation, subst] using PaperComputationTyped.fail)
    (by intro declarations graphTypes environment owners binder body responseType resultType hbody ihBody σ
        have ihBody := ihBody σ
        simpa [mapPaperValue, mapPaperComputation, mapTypeEnvironment, subst] using
          PaperContinuationTyped.continuation ihBody)
    derivation σ


theorem ValuesTyped.typeTransport (σ : Nat → Ty) {declarations : DeclarationTable}
    {graphTypes : GraphEnvironment} {environment : TypeEnvironment}
    {values : List Value} {types : List Ty}
    (derivation : ValuesTyped declarations graphTypes environment values types) :
    ValuesTyped (mapDeclarationTable σ declarations) (mapGraphEnvironment σ graphTypes)
      (mapTypeEnvironment σ environment) (values.map (mapPaperValue σ)) (types.map (subst σ)) := by
  induction values generalizing types environment with
  | nil =>
      cases derivation
      exact .nil
  | cons value values ih =>
      cases derivation with
      | cons head tail =>
          simpa [mapTypeEnvironment] using ValuesTyped.cons
            (PaperValueTyped.subst_explicit σ head) (ih tail)

theorem ValuesAllTyped.typeTransport (σ : Nat → Ty) {declarations : DeclarationTable}
    {graphTypes : GraphEnvironment} {environment : TypeEnvironment}
    {values : List Value} {ty : Ty}
    (derivation : ValuesAllTyped declarations graphTypes environment values ty) :
    ValuesAllTyped (mapDeclarationTable σ declarations) (mapGraphEnvironment σ graphTypes)
      (mapTypeEnvironment σ environment) (values.map (mapPaperValue σ)) (subst σ ty) := by
  induction values generalizing ty environment with
  | nil =>
      cases derivation
      exact .nil
  | cons value values ih =>
      cases derivation with
      | cons head tail =>
          simpa [mapTypeEnvironment] using ValuesAllTyped.cons
            (PaperValueTyped.subst_explicit σ head) (ih tail)

theorem RecordPayloadsTyped.typeTransport (σ : Nat → Ty) {declarations : DeclarationTable}
    {graphTypes : GraphEnvironment} {environment : TypeEnvironment}
    {fields : List (Label × Presence × Value)} {recordType : Ty}
    (derivation : RecordPayloadsTyped declarations graphTypes environment fields recordType) :
    RecordPayloadsTyped (mapDeclarationTable σ declarations) (mapGraphEnvironment σ graphTypes)
      (mapTypeEnvironment σ environment) (mapRecordFields σ fields) (subst σ recordType) := by
  induction fields generalizing recordType environment with
  | nil =>
      cases derivation
      exact .nil
  | cons field fields ih =>
      cases derivation with
      | cons fieldProof valueProof tail =>
          exact .cons (RecordField.subst σ fieldProof)
            (PaperValueTyped.subst_explicit σ valueProof) (ih tail)



theorem PaperComputationTyped.typeTransport (σ : Nat → Ty)
    {declarations : DeclarationTable} {graphTypes : GraphEnvironment}
    {environment : TypeEnvironment} {computation : Computation} {ty : Ty}
    (derivation : PaperComputationTyped declarations graphTypes environment computation ty) :
    PaperComputationTyped (mapDeclarationTable σ declarations)
      (mapGraphEnvironment σ graphTypes) (mapTypeEnvironment σ environment)
      (mapPaperComputation σ computation) (subst σ ty) := by
  have transported := PaperValueTyped.subst_explicit σ (PaperValueTyped.delay derivation)
  simp only [mapPaperValue, subst] at transported
  cases transported with
  | delay body => exact body


theorem PaperContinuationTyped.typeTransport (σ : Nat → Ty)
    {declarations : DeclarationTable} {graphTypes : GraphEnvironment}
    {environment : TypeEnvironment} {continuation : Value} {response result : Ty}
    (derivation : PaperContinuationTyped declarations graphTypes environment
      continuation response result) :
    PaperContinuationTyped (mapDeclarationTable σ declarations) (mapGraphEnvironment σ graphTypes)
      (mapTypeEnvironment σ environment) (mapPaperValue σ continuation)
      (subst σ response) (subst σ result) := by
  cases derivation with
  | continuation body =>
      simp only [mapPaperValue]
      apply PaperContinuationTyped.continuation
      simpa only [mapTypeEnvironment, List.map_cons] using
        PaperComputationTyped.typeTransport σ body


/-- Invocation inversion recovers the one declaration/instance and exact result. -/
theorem PaperComputationTyped.templateInversion
    {declarations : DeclarationTable} {graphTypes : GraphEnvironment}
    {environment : TypeEnvironment} {identity : Nat} {typeArguments : List Ty}
    {arguments : List Value} {resultType : Ty}
    (derivation : PaperComputationTyped declarations graphTypes environment
      (.template identity typeArguments arguments) resultType) :
    ∃ typeArity formals result body,
      TemplateDeclarationResolved declarations.templates identity
        (.mk identity typeArity formals result body) ∧
      typeArguments.length = typeArity ∧
      ValuesTyped declarations graphTypes environment arguments
        (formals.map (instantiateType typeArguments)) ∧
      resultType = instantiateType typeArguments result := by
  cases derivation with
  | template resolved arity argumentsTyping =>
      exact ⟨_, _, _, _, resolved, arity, argumentsTyping, rfl⟩

/-- Raw split inversion retains its exact body result and explicit binder arity. -/
theorem PaperComputationTyped.splitInversion
    {declarations : DeclarationTable} {graphTypes : GraphEnvironment}
    {environment : TypeEnvironment} {tuple : Value} {binders : List TermName}
    {body : Computation} {resultType : Ty}
    (derivation : PaperComputationTyped declarations graphTypes environment
      (.split tuple binders body) resultType) :
    ∃ types, binders.length = types.length ∧
      PaperValueTyped declarations graphTypes environment tuple (argsSyntax types) ∧
      PaperComputationTyped declarations graphTypes (extendTupleEnvironment types environment)
        body resultType := by
  cases derivation with
  | split arity tupleTyping bodyTyping => exact ⟨_, arity, tupleTyping, bodyTyping⟩

/-- Tuple introduction composes with split using the same ordered component list. -/
theorem PaperComputationTyped.splitTuple
    {declarations : DeclarationTable} {graphTypes : GraphEnvironment}
    {environment : TypeEnvironment} {values : List Value} {types : List Ty}
    {binders : List TermName} {body : Computation} {resultType : Ty}
    (valuesTyping : ValuesTyped declarations graphTypes environment values types)
    (arity : binders.length = types.length)
    (bodyTyping : PaperComputationTyped declarations graphTypes
      (extendTupleEnvironment types environment) body resultType) :
    PaperComputationTyped declarations graphTypes environment (.split (.tuple values) binders body)
      resultType := by
  exact .split arity (.tuple valuesTyping) bodyTyping

/-- Inversion retains the exact overall result type in both branch premises. -/
theorem PaperComputationTyped.unionCaseInversion
    {declarations : DeclarationTable} {graphTypes : GraphEnvironment}
    {environment : TypeEnvironment} {value : Value}
    {leftBinder rightBinder : TermName} {left right : Computation} {resultType : Ty}
    (derivation : PaperComputationTyped declarations graphTypes environment
      (.unionCase value leftBinder left rightBinder right) resultType) :
    ∃ leftType rightType,
      PaperValueTyped declarations graphTypes environment value (.union leftType rightType) ∧
      PaperComputationTyped declarations graphTypes (leftType :: environment) left resultType ∧
      PaperComputationTyped declarations graphTypes (rightType :: environment) right resultType := by
  cases derivation with
  | unionCase valueTyping leftTyping rightTyping =>
      exact ⟨_, _, valueTyping, leftTyping, rightTyping⟩

/-- Left injection composes with union typing; both branch premises remain. -/
theorem PaperComputationTyped.unionCaseInjectLeft
    {declarations : DeclarationTable} {graphTypes : GraphEnvironment}
    {environment : TypeEnvironment} {value : Value}
    {leftBinder rightBinder : TermName} {left right : Computation}
    {leftType rightType resultType : Ty}
    (valueTyping : PaperValueTyped declarations graphTypes environment value leftType)
    (leftTyping : PaperComputationTyped declarations graphTypes (leftType :: environment) left resultType)
    (rightTyping : PaperComputationTyped declarations graphTypes (rightType :: environment) right resultType) :
    PaperComputationTyped declarations graphTypes environment
      (.unionCase (.injectLeft value) leftBinder left rightBinder right) resultType := by
  exact .unionCase (.injectLeft valueTyping) leftTyping rightTyping

/-- Right injection composes with union typing; both branch premises remain. -/
theorem PaperComputationTyped.unionCaseInjectRight
    {declarations : DeclarationTable} {graphTypes : GraphEnvironment}
    {environment : TypeEnvironment} {value : Value}
    {leftBinder rightBinder : TermName} {left right : Computation}
    {leftType rightType resultType : Ty}
    (valueTyping : PaperValueTyped declarations graphTypes environment value rightType)
    (leftTyping : PaperComputationTyped declarations graphTypes (leftType :: environment) left resultType)
    (rightTyping : PaperComputationTyped declarations graphTypes (rightType :: environment) right resultType) :
    PaperComputationTyped declarations graphTypes environment
      (.unionCase (.injectRight value) leftBinder left rightBinder right) resultType := by
  exact .unionCase (.injectRight valueTyping) leftTyping rightTyping

/-- Invert actual raw wrap typing, recovering every endpoint and body premise. -/
theorem PaperValueTyped.wrapInversion
    {declarations : DeclarationTable} {graphTypes : GraphEnvironment}
    {environment : TypeEnvironment} {function : Value}
    {argumentAdapter resultAdapter : Computation} {ty : Ty}
    (derivation : PaperValueTyped declarations graphTypes environment
      (.wrap function argumentAdapter resultAdapter) ty) :
    ∃ inputType outputType adaptedInputType adaptedOutputType,
      ty = .callable adaptedInputType adaptedOutputType ∧
      PaperValueTyped declarations graphTypes environment function (.callable inputType outputType) ∧
      PaperComputationTyped declarations graphTypes (adaptedInputType :: environment)
        argumentAdapter inputType ∧
      PaperComputationTyped declarations graphTypes (outputType :: environment)
        resultAdapter adaptedOutputType := by
  cases derivation with
  | wrap functionTyping argumentTyping resultTyping =>
      exact ⟨_, _, _, _, rfl, functionTyping, argumentTyping, resultTyping⟩

/-- Consume the outer input thunk and obtain the outer output via existing Call. -/
theorem PaperComputationTyped.callWrapped
    {declarations : DeclarationTable} {graphTypes : GraphEnvironment}
    {environment : TypeEnvironment} {function thunk : Value}
    {argumentAdapter resultAdapter : Computation}
    {inputType outputType adaptedInputType adaptedOutputType : Ty}
    (functionTyping : PaperValueTyped declarations graphTypes environment function
      (.callable inputType outputType))
    (argumentTyping : PaperComputationTyped declarations graphTypes (adaptedInputType :: environment)
      argumentAdapter inputType)
    (resultTyping : PaperComputationTyped declarations graphTypes (outputType :: environment)
      resultAdapter adaptedOutputType)
    (thunkTyping : PaperValueTyped declarations graphTypes environment thunk (.thunk adaptedInputType)) :
    PaperComputationTyped declarations graphTypes environment
      (.call (.wrap function argumentAdapter resultAdapter) thunk) adaptedOutputType := by
  exact .call (.wrap functionTyping argumentTyping resultTyping) thunkTyping


/-- The shared captured type remains free beneath the new universal binder. -/
theorem typeAbstractionSharedVariable (declarations : DeclarationTable)
    (graphTypes : GraphEnvironment) :
    PaperValueTyped declarations graphTypes [.var 0]
      (.typeAbstraction (.variable 0)) (.poly (.var 1)) := by
  apply PaperValueTyped.typeAbstraction
  exact PaperValueTyped.variable rfl

/-- An explicit shared operation, graph entry, and captured variable all shift. -/
theorem typeAbstractionSharedContexts :
    let declarations : DeclarationTable :=
      { operations := [{ identity := 7, typeArity := 0, payloadTemplate := .var 0, responseTemplate := .var 0 }],
        nominalConstructors := [], primitives := [], templates := [], nativeListIdentity := 9 };
    (mapDeclarationTable shiftTypeSubstitution declarations).operations =
      [{ identity := 7, typeArity := 0, payloadTemplate := .var 1, responseTemplate := .var 1 }] ∧
    mapGraphEnvironment shiftTypeSubstitution [(5, .var 0)] = [(5, .var 1)] ∧
    mapTypeEnvironment shiftTypeSubstitution [.var 0] = [.var 1] ∧
    PaperValueTyped declarations [(5, .var 0)] [.var 0]
      (.typeAbstraction (.variable 0)) (.poly (.var 1)) := by
  exact ⟨rfl, rfl, rfl, typeAbstractionSharedVariable _ _⟩


theorem resumeVariableBoolInt (declarations : DeclarationTable) :
    PaperComputationTyped declarations []
      [.kont (.base .bool) (.base .int)]
      (.resume (.variable 0) (.literal (.boolean true))) (.base .int) := by
  apply PaperComputationTyped.resume
  · exact PaperValueTyped.variable rfl
  · exact PaperValueTyped.literal

theorem resumeVariableWrongResponseImpossible (declarations : DeclarationTable) :
    ¬ PaperComputationTyped declarations []
      [.kont (.base .bool) (.base .int)]
      (.resume (.variable 0) (.literal (.boolean true))) (.base .bool) := by
  intro derivation
  cases derivation with
  | resume continuation response =>
      cases continuation <;> simp_all [lookupTypeEnvironment]

theorem typeApplicationBoolVariable (declarations : DeclarationTable) :
    PaperValueTyped declarations [] [.poly (.var 0)]
      (.typeApplication (.variable 0) (.base .bool)) (.base .bool) := by
  have functionTyping :
      PaperValueTyped declarations [] [.poly (.var 0)] (.variable 0) (.poly (.var 0)) :=
    PaperValueTyped.variable rfl
  simpa [instantiateType, instantiateSubstitution, lookupTypeArgument, subst] using
    (PaperValueTyped.typeApplication functionTyping)

theorem rollVariable (declarations : DeclarationTable) :
    PaperValueTyped declarations [] [.mu (.var 0)]
      (.roll (.variable 0)) (.mu (.var 0)) := by
  apply PaperValueTyped.roll
  exact PaperValueTyped.variable rfl

theorem unrollVariable (declarations : DeclarationTable) :
    PaperComputationTyped declarations [] [.mu (.var 0)]
      (.unroll (.variable 0)) (.mu (.var 0)) := by
  have valueTyping :
      PaperValueTyped declarations [] [.mu (.var 0)] (.variable 0) (.mu (.var 0)) :=
    PaperValueTyped.variable rfl
  simpa [instantiateType, instantiateSubstitution, lookupTypeArgument, subst] using
    (PaperComputationTyped.unroll valueTyping)


end YulangClosure.PaperTypes
