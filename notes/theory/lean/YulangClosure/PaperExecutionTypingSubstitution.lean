import YulangClosure.PaperExecutionSyntax
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
    (motive_1 := fun e values types _ => ValuesTyped (mapDeclarationTable σ declarations)
      (mapGraphEnvironment σ graphTypes) (mapTypeEnvironment σ e)
      (values.map (mapPaperValue σ)) (types.map (subst σ)))
    (motive_2 := fun e values ty _ => ValuesAllTyped (mapDeclarationTable σ declarations)
      (mapGraphEnvironment σ graphTypes) (mapTypeEnvironment σ e)
      (values.map (mapPaperValue σ)) (subst σ ty))
    (motive_3 := fun e fields ty _ => RecordPayloadsTyped (mapDeclarationTable σ declarations)
      (mapGraphEnvironment σ graphTypes) (mapTypeEnvironment σ e)
      (mapRecordFields σ fields) (subst σ ty))
    (motive_4 := fun e value ty _ => PaperValueTyped (mapDeclarationTable σ declarations)
      (mapGraphEnvironment σ graphTypes) (mapTypeEnvironment σ e)
      (mapPaperValue σ value) (subst σ ty))
    (motive_5 := fun e computation ty _ => PaperComputationTyped (mapDeclarationTable σ declarations)
      (mapGraphEnvironment σ graphTypes) (mapTypeEnvironment σ e)
      (mapPaperComputation σ computation) (subst σ ty))
    (motive_6 := fun e continuation response result _ =>
      PaperContinuationTyped (mapDeclarationTable σ declarations) (mapGraphEnvironment σ graphTypes)
        (mapTypeEnvironment σ e) (mapPaperValue σ continuation) (subst σ response) (subst σ result))
    (by intro environment; exact ValuesTyped.nil)
    (by intro environment value values ty types hvalue hvalues ihValue ihValues
        simpa [mapTypeEnvironment] using ValuesTyped.cons ihValue ihValues)
    (by intro environment ty; exact ValuesAllTyped.nil)
    (by intro environment value values ty hvalue hvalues ihValue ihValues
        simpa [mapTypeEnvironment] using ValuesAllTyped.cons ihValue ihValues)
    (by intro environment recordType; exact RecordPayloadsTyped.nil)
    (by intro label tag value fields recordType presence fieldType environment hfield hvalue hfields ihValue ihFields
        simpa [mapRecordFields] using RecordPayloadsTyped.cons
          (RecordField.subst σ hfield) ihValue ihFields)
    (by intro environment index ty lookup
        simp only [mapPaperValue]
        apply PaperValueTyped.variable
        simpa [lookupTypeEnvironment_subst] using congrArg (Option.map (subst σ)) lookup)
    (by intro environment identity ty lookup
        simp only [mapPaperValue]
        apply PaperValueTyped.graphReference
        simpa [lookupGraphEnvironment_subst] using congrArg (Option.map (subst σ)) lookup)
    (by intro environment literal
        simpa [mapPaperValue] using (PaperValueTyped.literal :
          PaperValueTyped (mapDeclarationTable σ declarations) (mapGraphEnvironment σ graphTypes)
            (mapTypeEnvironment σ environment) _ _))
    (by intro environment values types hvalues ihValues
        simpa [mapPaperValue, typingArgsSyntax_subst] using PaperValueTyped.tuple ihValues)
    (by intro environment values elementType hvalues ihValues
        simpa [mapPaperValue, mapDeclarationTable, subst] using PaperValueTyped.sequence ihValues)
    (by intro environment fields recordType labels required shape unique allRequired hfields ihFields
        have unique' : (mapRecordFields σ fields).map Prod.fst |>.Nodup := by
          simpa only [mapRecordFields_labels] using unique
        have required' : ∀ label, label ∈ required → label ∈ (mapRecordFields σ fields).map Prod.fst := by
          simpa only [mapRecordFields_labels] using allRequired
        have result := PaperValueTyped.record (RecordShape.subst σ shape) unique' required' ihFields
        simpa only [mapPaperValue_record_eq] using result)
    (by intro environment body resultType hbody ihBody
        simpa [mapPaperValue, subst] using PaperValueTyped.delay ihBody)
    (by intro environment profile parameter body inputType outputType hbody ihBody
        simpa [mapPaperValue, mapPaperComputation, mapTypeEnvironment, subst] using
          PaperValueTyped.valueLambda ihBody)
    (by intro environment profile parameter body inputType outputType hbody ihBody
        simpa [mapPaperValue, mapPaperComputation, mapTypeEnvironment, subst] using
          PaperValueTyped.computationLambda ihBody)
    (by intro environment value left right hvalue ihValue
        simpa [mapPaperValue, subst] using PaperValueTyped.injectLeft ihValue)
    (by intro environment value left right hvalue ihValue
        simpa [mapPaperValue, subst] using PaperValueTyped.injectRight ihValue)
    (by intro environment value left right hleft hright ihLeft ihRight
        simpa [mapPaperValue, subst] using PaperValueTyped.both ihLeft ihRight)
    (by intro environment value ty hvalue ihValue
        simpa [mapPaperValue, subst] using PaperValueTyped.topView ihValue)
    (by intro environment metadata value ty hvalue ihValue
        simpa [mapPaperValue] using PaperValueTyped.view ihValue)
    (by intro environment owners binder body responseType resultType hcontinuation ihContinuation
        have ihContinuation' :
            PaperContinuationTyped (mapDeclarationTable σ declarations)
              (mapGraphEnvironment σ graphTypes) (mapTypeEnvironment σ environment)
              (.continuation owners binder (mapPaperComputation σ body))
              (subst σ responseType) (subst σ resultType) := by
          simpa [mapPaperValue] using ihContinuation
        simpa [mapPaperValue, subst] using PaperValueTyped.continuation ihContinuation')
    (by intro environment function body argument hfunction ihFunction
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
    (by intro environment value body hvalue ihValue
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
    (by intro environment value ty hvalue ihValue
        simpa [mapPaperComputation] using PaperComputationTyped.ret ihValue)
    (by intro environment first body firstType resultType hfirst hbody ihFirst ihBody
        simpa [mapPaperComputation, mapTypeEnvironment] using
          PaperComputationTyped.letE ihFirst ihBody)
    (by intro environment thunk resultType hthunk ihThunk
        simpa [mapPaperComputation] using PaperComputationTyped.force ihThunk)
    (by intro environment function thunk argumentType resultType hfunction hthunk ihFunction ihThunk
        simpa [mapPaperComputation] using PaperComputationTyped.call ihFunction ihThunk)
    (by intro environment value recordType label fieldType hvalue hfield ihValue
        simpa [mapPaperComputation] using
          PaperComputationTyped.field ihValue (RecordField.subst σ hfield))
    (by intro environment value recordType label presence fieldType hvalue hfield ihValue
        simpa [mapPaperComputation, subst] using
          PaperComputationTyped.lookup ihValue (RecordField.subst σ hfield))
    (by intro environment operation arguments payload declaration resolved arity payloadTyping ihPayload
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
    (by intro environment opInstance payload continuation declaration arguments resultType
          resolved arity instanceEq payloadTyping continuationTyping ihPayload ihContinuation
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
    (by intro environment continuation response responseType resultType hcontinuation hresponse
          ihContinuation ihResponse
        simpa [mapPaperComputation] using PaperComputationTyped.resume ihContinuation ihResponse)
    (by intro environment value body hvalue ihValue
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
    (by intro environment reason ty; simpa [mapPaperComputation, subst] using PaperComputationTyped.fail)
    (by intro environment owners binder body responseType resultType hbody ihBody
        simpa [mapPaperValue, mapPaperComputation, mapTypeEnvironment, subst] using
          PaperContinuationTyped.continuation ihBody)
    derivation


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



theorem PaperContinuationTyped.typeTransport (σ : Nat → Ty)
    {declarations : DeclarationTable} {graphTypes : GraphEnvironment}
    {environment : TypeEnvironment} {owners : List OwnerName} {binder : TermName}
    {body : Computation} {response result : Ty}
    (derivation : PaperContinuationTyped declarations graphTypes environment
      (.continuation owners binder body) response result) :
    PaperContinuationTyped (mapDeclarationTable σ declarations) (mapGraphEnvironment σ graphTypes)
      (mapTypeEnvironment σ environment) (.continuation owners binder (mapPaperComputation σ body))
      (subst σ response) (subst σ result) := by
  have transported := PaperValueTyped.subst_explicit σ (PaperValueTyped.continuation derivation)
  simp only [mapPaperValue, subst] at transported
  cases transported with
  | continuation body => exact body

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
