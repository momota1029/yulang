import YulangClosure.PaperExecutionTypingSubstitution

/-!
The two operation-mapper adapter premises of the paper's lines 694–719.
This is separate evidence for adapters, not a mapOperation computation rule,
execution preservation, or a source/native correspondence theorem.
-/
namespace YulangClosure.PaperTypes

/-- Both concrete instances and both code derivations share one declaration
and the same captured declaration, graph, and term contexts. -/
inductive MapperPlanTyped (declarations : DeclarationTable) (graphTypes : GraphEnvironment)
    (environment : TypeEnvironment) : MapperPlan → Prop where
  | mk {source target : OperationInstance} {payload response : Computation}
      {declaration : OperationDeclaration} {sourceArguments targetArguments : List Ty} :
      OperationDeclarationResolved declarations.operations source.identity declaration →
      sourceArguments.length = declaration.typeArity →
      targetArguments.length = declaration.typeArity →
      source = declaration.instantiate sourceArguments →
      target = declaration.instantiate targetArguments →
      PaperComputationTyped declarations graphTypes (source.payloadType :: environment)
        payload target.payloadType →
      PaperComputationTyped declarations graphTypes (target.responseType :: environment)
        response source.responseType →
      MapperPlanTyped declarations graphTypes environment (.mk source target payload response)

/-- Inversion retains both witness lists and the complete instance equalities,
including the encoded typeArguments fields. -/
theorem MapperPlanTyped.inversion
    {declarations : DeclarationTable} {graphTypes : GraphEnvironment}
    {environment : TypeEnvironment} {source target : OperationInstance}
    {payload response : Computation}
    (derivation : MapperPlanTyped declarations graphTypes environment
      (.mk source target payload response)) :
    ∃ declaration sourceArguments targetArguments,
      OperationDeclarationResolved declarations.operations source.identity declaration ∧
      sourceArguments.length = declaration.typeArity ∧
      targetArguments.length = declaration.typeArity ∧
      source = declaration.instantiate sourceArguments ∧
      target = declaration.instantiate targetArguments ∧
      PaperComputationTyped declarations graphTypes (source.payloadType :: environment)
        payload target.payloadType ∧
      PaperComputationTyped declarations graphTypes (target.responseType :: environment)
        response source.responseType := by
  cases derivation with
  | mk resolved sourceArity targetArity sourceEq targetEq payloadTyping responseTyping =>
      exact ⟨_, _, _, resolved, sourceArity, targetArity, sourceEq, targetEq,
        payloadTyping, responseTyping⟩

/-- Both sides refer to the one resolved operation/member identity. -/
theorem MapperPlanTyped.sameIdentity
    {declarations : DeclarationTable} {graphTypes : GraphEnvironment}
    {environment : TypeEnvironment} {source target : OperationInstance}
    {payload response : Computation}
    (derivation : MapperPlanTyped declarations graphTypes environment
      (.mk source target payload response)) :
    source.identity = target.identity := by
  obtain ⟨declaration, sourceArguments, targetArguments, _, _, _, sourceEq, targetEq, _, _⟩ :=
    MapperPlanTyped.inversion derivation
  exact (congrArg OperationInstance.identity sourceEq).trans
    (congrArg OperationInstance.identity targetEq).symm

/-- Arbitrary simultaneous substitution transports the actual mapped plan and
both adapters, with the same mapped declaration and shared captured tail. -/
theorem MapperPlanTyped.typeTransport (σ : Nat → Ty)
    {declarations : DeclarationTable} {graphTypes : GraphEnvironment}
    {environment : TypeEnvironment} {mapper : MapperPlan}
    (derivation : MapperPlanTyped declarations graphTypes environment mapper) :
    MapperPlanTyped (mapDeclarationTable σ declarations) (mapGraphEnvironment σ graphTypes)
      (mapTypeEnvironment σ environment) (mapMapperPlan σ mapper) := by
  cases mapper with
  | mk source target payload response =>
      obtain ⟨declaration, sourceArguments, targetArguments, resolved, sourceArity, targetArity,
        sourceEq, targetEq, payloadTyping, responseTyping⟩ :=
          MapperPlanTyped.inversion derivation
      simp only [mapMapperPlan]
      refine MapperPlanTyped.mk
        (declaration := declaration.substAmbient σ)
        (sourceArguments := mapOperationArguments σ sourceArguments)
        (targetArguments := mapOperationArguments σ targetArguments) ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · exact OperationDeclarationResolved.typeTransport σ resolved
      · simpa [mapOperationArguments, OperationDeclaration.substAmbient] using sourceArity
      · simpa [mapOperationArguments, OperationDeclaration.substAmbient] using targetArity
      · rw [sourceEq]
        exact operation_declaration_instantiation_subst declaration sourceArguments σ sourceArity
      · rw [targetEq]
        exact operation_declaration_instantiation_subst declaration targetArguments σ targetArity
      · simpa only [mapTypeEnvironment, List.map_cons, OperationInstance.subst] using
          PaperComputationTyped.typeTransport σ payloadTyping
      · simpa only [mapTypeEnvironment, List.map_cons, OperationInstance.subst] using
          PaperComputationTyped.typeTransport σ responseTyping

/-- Unary operation used solely to distinguish the two adapter polarities. -/
def mapperPolarityDeclaration : OperationDeclaration :=
  { identity := 17, typeArity := 1, payloadTemplate := .var 0, responseTemplate := .var 0 }

def mapperPolarityTable : DeclarationTable :=
  { operations := [mapperPolarityDeclaration], nominalConstructors := [], primitives := [],
    templates := [], nativeListIdentity := 0 }

def mapperPolaritySource : OperationInstance :=
  mapperPolarityDeclaration.instantiate [.base .bool]

def mapperPolarityTarget : OperationInstance :=
  mapperPolarityDeclaration.instantiate [.base .int]

def mapperPolarityGood : MapperPlan :=
  .mk mapperPolaritySource mapperPolarityTarget
    (.ret (.literal (.integer 0))) (.ret (.literal (.boolean true)))

def mapperPolarityBad : MapperPlan :=
  .mk mapperPolaritySource mapperPolarityTarget
    (.ret (.literal (.integer 0))) (.ret (.literal (.integer 0)))

/-- Bool→Int payload code and Int→Bool response code satisfy the premises. -/
theorem mapperPolarityGoodTyped : MapperPlanTyped mapperPolarityTable [] [] mapperPolarityGood := by
  unfold mapperPolarityGood
  apply MapperPlanTyped.mk
    (declaration := mapperPolarityDeclaration)
    (sourceArguments := [.base .bool]) (targetArguments := [.base .int])
  · refine ⟨by simp [mapperPolarityTable], rfl, ?_⟩
    intro other hmember _
    simpa only [mapperPolarityTable, List.mem_singleton] using hmember
  · rfl
  · rfl
  · rfl
  · rfl
  · exact .ret .literal
  · exact .ret .literal

/-- Changing only the response code to Int-returning code violates its Bool
result requirement. This is a typing-polarity discriminator, not execution. -/
theorem mapperPolarityBadNotTyped : ¬ MapperPlanTyped mapperPolarityTable [] [] mapperPolarityBad := by
  intro derivation
  change MapperPlanTyped mapperPolarityTable [] []
    (.mk mapperPolaritySource mapperPolarityTarget
      (.ret (.literal (.integer 0))) (.ret (.literal (.integer 0)))) at derivation
  obtain ⟨declaration, sourceArguments, targetArguments, resolved, sourceArity, targetArity,
    sourceEq, targetEq, payloadTyping, responseTyping⟩ := MapperPlanTyped.inversion derivation
  change PaperComputationTyped mapperPolarityTable [] [.base .int]
    (.ret (.literal (.integer 0))) (.base .bool) at responseTyping
  cases responseTyping with
  | ret valueTyping => cases valueTyping

end YulangClosure.PaperTypes
