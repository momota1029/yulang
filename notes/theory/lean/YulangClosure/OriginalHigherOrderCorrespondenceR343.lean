import YulangClosure.OriginalSourceContinuationR342

/-! R343 candidate projection of the actual selected source with an explicit
native request-carrier Return and declaration-derived forcing consumer.
This proves HigherOrder steps, not a Rust/original-EI simulation. Receipt,
owner, live-world, view and source-to-original predicate correspondence remain open.
-/
namespace YulangClosure.OriginalHigherOrderCorrespondenceR343
open HigherOrder HigherOrder.Safety
open OriginalSourceScopedInterpretationR335 OriginalSourcePrimitiveBridgeR336
open OriginalTickDeclaredResponseR321

def forceAdapter (a : Ty) : Adapter := .mk (.thunk a) a (.force (.var 0)) [] []

theorem force_adapter_typed (env : Context) (a : Ty) :
    AdapterTyped env (forceAdapter a) (.thunk a) a := .mk (.force (.var rfl))

def operationCarrierValue (receipt : ReceiptTemplate) (op : OperationInstance) : Value :=
  .lambda .value receipt op.payloadType (.thunk op.responseType) op.responseType
    (.ret (.delay (.request op (.var 0) (.ret (.var 0))))) (forceAdapter op.responseType)

theorem operation_carrier_value_typed (env : Context) (receipt : ReceiptTemplate)
    (op : OperationInstance) :
    ValueTyped env (operationCarrierValue receipt op) (.callable op.payloadType op.responseType) :=
  .lambdaValue (.ret (.delay (.request (.var rfl) (.ret (.var rfl)))))
    (force_adapter_typed env _)

def intType : Ty := .base .int

/- Partial projection only certified below for the canonical R315 initializer.
Primitive lookup deliberately uses that initializer's full scoped inventory.
This is not a general source interpreter or native simulation. -/
mutual
  def project (origin : OriginalSource.Declaration) (receipts : Nat → ReceiptTemplate)
      (arguments results : Nat → Ty) : Nat → List (Option OriginalSource.Name) →
      OriginalSource.Source .expression → Option Comp
    | 0, _, _ => none
    | fuel + 1, names, raw =>
      match raw with
      | .name mark name => if mark.annotation.isSome then none else
          (OriginalSourceContinuationR342.indexOf name names).map fun index => .ret (.var index)
      | .primitive mark identifier => do
          if mark.annotation.isSome then none else do
            let entry ← (primitiveTable origin [] OriginalModuleContextBindingR315.makeInitializer).find?
              (fun entry => entry.site == mark.site && entry.identifier == identifier)
            let op ← sourceRequest origin entry.key .primitiveDeclarationInstance
            pure (.ret (operationCarrierValue (receipts mark.site) (embedOperation op)))
      | .lambda mark formal pattern body =>
          if mark.annotation.isSome || formal.annotation.isSome || formal.outerComputation then none else
          match pattern with
          | .varPattern _ name => if name = formal.name then do
              let body ← project origin receipts arguments results fuel (some name :: names) body
              pure (.ret (.lambda .value (receipts mark.site) (arguments mark.site)
                (results mark.site) (results mark.site) body (OriginalSourceContinuationR342.identityAdapter (results mark.site))))
            else none
          | _ => none
      | .app mark callee argument => if mark.annotation.isSome then none else do
          let callee ← project origin receipts arguments results fuel names callee
          let argument ← project origin receipts arguments results fuel names argument
          pure (sourceApply callee argument)
      | .block mark statements last => if mark.annotation.isSome then none else
          projectStatements origin receipts arguments results fuel names statements last
      | .literal mark (.int integer) => if mark.annotation.isSome then none else pure (.ret (.int integer))
      | _ => none

  def projectStatements (origin : OriginalSource.Declaration) (receipts : Nat → ReceiptTemplate)
      (arguments results : Nat → Ty) : Nat → List (Option OriginalSource.Name) →
      OriginalSource.Source .statements → OriginalSource.Source .expression → Option Comp
    | 0, _, _, _ => none
    | fuel + 1, names, .statementsNil, last => project origin receipts arguments results fuel names last
    | fuel + 1, names, .statementsCons (.expressionS _ first) rest, last => do
        let first ← project origin receipts arguments results fuel names first
        let rest ← projectStatements origin receipts arguments results fuel (none :: names) rest last
        pure (.bind first rest)
    | _, _, _, _ => none
end

def tickValue (receipts : Nat → ReceiptTemplate) : Value :=
  operationCarrierValue (receipts 4) (embedOperation tickOperation)

def body (a : Ty) (receipts : Nat → ReceiptTemplate) : Comp :=
  .bind (sourceApply (.ret (tickValue receipts)) (.ret (.var 0)))
    (.ret (OriginalSourceContinuationR342.identityValue a receipts))

def makeValue (a : Ty) (receipts : Nat → ReceiptTemplate) : Value :=
  .lambda .value (receipts 0) intType (.callable a a) (.callable a a)
    (body a receipts) (OriginalSourceContinuationR342.identityAdapter (.callable a a))

def argumentTypes (a : Ty) (site : Nat) : Ty := if site = 0 then intType else a
def resultTypes (a : Ty) (site : Nat) : Ty := if site = 0 then .callable a a else a

/-- Computed from the authentic decoded source, not a supplied phase body. -/
theorem actual_source_projection (origin : OriginalSource.Declaration) (a : Ty)
    (receipts : Nat → ReceiptTemplate) :
    project origin receipts (argumentTypes a) (resultTypes a) 16 []
      OriginalModuleContextBindingR315.makeInitializer = some (.ret (makeValue a receipts)) := by
  have table := tick_source_table origin
  dsimp only [OriginalModuleContextBindingR315.makeInitializer] at table
  dsimp only [OriginalModuleContextBindingR315.makeInitializer, project, projectStatements,
    OriginalSourceContinuationR342.indexOf, argumentTypes, resultTypes]
  simp only [Option.isSome_none, Bool.or_false, Bool.false_eq_true, ↓reduceIte]
  rw [table]
  change (do
    let body ← (do
      let first ← (do
        let callee ← (do
          let op ← sourceRequest origin (tickPrimitive origin).key .primitiveDeclarationInstance
          pure (Comp.ret (operationCarrierValue (receipts 4) (embedOperation op))))
        pure (sourceApply callee (.ret (.var 0))))
      pure (Comp.bind first (.ret (OriginalSourceContinuationR342.identityValue a receipts))))
    pure (Comp.ret (.lambda .value (receipts 0) intType (.callable a a) (.callable a a)
      body (OriginalSourceContinuationR342.identityAdapter (.callable a a))))) = _
  rw [(tick_original_program origin).2, tick_request_resolves]
  rfl

theorem body_typed (a : Ty) (receipts : Nat → ReceiptTemplate) :
    CompTyped (extend emptyContext intType) (body a receipts) (.callable a a) := by
  apply CompTyped.bind
  · exact sourceApply_typed (.ret (operation_carrier_value_typed _ _ _)) (.ret (.var rfl))
  · exact .ret (OriginalSourceContinuationR342.identity_value_typed _ a receipts)

theorem make_value_typed (a : Ty) (receipts : Nat → ReceiptTemplate) :
    ValueTyped emptyContext (makeValue a receipts) (.callable intType (.callable a a)) :=
  .lambdaValue (body_typed a receipts) (OriginalSourceContinuationR342.identity_adapter_typed _ _)

def program (a : Ty) (receipts : Nat → ReceiptTemplate) (seed : Int) : Comp :=
  sourceApply (.ret (makeValue a receipts)) (.ret (.int seed))

def makePlan (a : Ty) (receipts : Nat → ReceiptTemplate) (seed : Int) : LambdaEntryPlan :=
  ⟨.value, receipts 0, intType, .callable a a, .callable a a,
    body a receipts, OriginalSourceContinuationR342.identityAdapter (.callable a a), .delay (.ret (.int seed))⟩

def tickPlan (receipts : Nat → ReceiptTemplate) (seed : Int) : LambdaEntryPlan :=
  ⟨.value, receipts 4, intType, .thunk intType, intType,
    .ret (.delay (.request (embedOperation tickOperation) (.var 0) (.ret (.var 0)))),
    forceAdapter intType, .delay (.ret (.int seed))⟩

/-- The declaration consumer has already forced the request carrier. It is not
saved as a second post-response consumer. Native owner/view frames are not modeled. -/
def savedContext (a : Ty) (receipts : Nat → ReceiptTemplate) : EvalContext :=
  .bind (.bind .hole (.ret (OriginalSourceContinuationR342.identityValue a receipts)))
    (.ret (.var 0))

def saved (a : Ty) (receipts : Nat → ReceiptTemplate) (seed : Int) : Interaction.Saved :=
  ⟨embedOperation tickOperation, .int seed, .ret (.var 0), savedContext a receipts⟩

def events (a : Ty) (receipts : Nat → ReceiptTemplate) (seed : Int) : List Event :=
  [.silent, .lambdaEntry (makePlan a receipts seed), .silent, .silent, .silent,
    .lambdaEntry (tickPlan receipts seed), .silent, .silent, .silent, .silent]

/-- Local phase equation: request-carrier Return is consumed before publication.
This is independent HigherOrder syntax, not a native delimiter/receipt theorem. -/
theorem forcing_consumer_before_request (op : OperationInstance) (payload : Value) :
    Steps (consumeResult (.ret (.delay (.request op payload (.ret (.var 0)))))
      (forceAdapter op.responseType)) [.silent, .silent]
      (.request op payload (.ret (.var 0))) :=
  .cons .bindReturn (.cons .force (.refl _))

theorem actual_prefix (a : Ty) (receipts : Nat → ReceiptTemplate) (seed : Int) :
    Steps (program a receipts seed) (events a receipts seed) (saved a receipts seed).request := by
  refine .cons .bindReturn ?_
  change Steps (.dynamicCall (makeValue a receipts) (.delay (.ret (.int seed)))) _ _
  refine .cons .callLambda ?_
  change Steps (.bind (.bind (.force (.delay (.ret (.int seed)))) (body a receipts))
    (.ret (.var 0))) _ _
  refine .cons (.bind (.bind .force)) ?_
  refine .cons (.bind .bindReturn) ?_
  change Steps (.bind (.bind (sourceApply (.ret (tickValue receipts)) (.ret (.int seed)))
    (.ret (OriginalSourceContinuationR342.identityValue a receipts))) (.ret (.var 0))) _ _
  refine .cons (.bind (.bind .bindReturn)) ?_
  refine .cons (.bind (.bind .callLambda)) ?_
  refine .cons (.bind (.bind (.bind (.bind .force)))) ?_
  refine .cons (.bind (.bind (.bind .bindReturn))) ?_
  exact OriginalSourceContinuationR342.plug_steps (savedContext a receipts)
    (forcing_consumer_before_request (embedOperation tickOperation) (.int seed))

theorem program_typed (a : Ty) (receipts : Nat → ReceiptTemplate) (seed : Int) :
    CompTyped emptyContext (program a receipts seed) (.callable a a) :=
  sourceApply_typed (.ret (make_value_typed a receipts)) (.ret .int)

theorem actual_capture_typed (a : Ty) (receipts : Nat → ReceiptTemplate) (seed : Int) :
    Interaction.SavedTyped (saved a receipts seed) (.callable a a) :=
  Interaction.capture_typed
    (trace_preservation (actual_prefix a receipts seed) (program_typed a receipts seed))

theorem actual_response_return (a : Ty) (receipts : Nat → ReceiptTemplate) (seed : Int)
    (response : Value) :
    Steps ((saved a receipts seed).resume response) [.silent, .silent]
      (.ret (OriginalSourceContinuationR342.identityValue a receipts)) := by
  refine .cons (.bind .bindReturn) ?_
  refine .cons .bindReturn ?_
  exact .refl _

/-- The selected source projection feeds the existing capture/resume consumer
with every original TypedCall response, whole view chain and literal outer context.
No source/native relation, world or original Inputs membership is assumed. -/
theorem decoded_source_prefix_and_return (origin : OriginalSource.Declaration)
    (a : Ty) (receipts : Nat → ReceiptTemplate) (seed : Int)
    (suffix : EvalContext) (result : Ty)
    (hsuffix : ContextTyped emptyContext suffix (.callable a a) result) :
    ∃ raw : OriginalSource.Source .expression,
      OriginalModuleContextBindingR315.decodeMake 16
        OriginalModuleContextBindingR315.Native.Make.rootInitializer = some raw ∧
      project origin receipts (argumentTypes a) (resultTypes a) 16 [] raw =
        some (.ret (makeValue a receipts)) ∧
      sourceRequest origin (tickRequest origin).operands.callee.key
        .primitiveDeclarationInstance = some tickOperation ∧
      Steps (suffix.plug (program a receipts seed)) (events a receipts seed)
        (suffix.plug (saved a receipts seed).request) ∧
      ∀ response, TypedCall.ValueTyped Original.emptyContext response tickOperation.responseType →
        CompTyped emptyContext
          (suffix.plug ((saved a receipts seed).resume (embedValue response))) result ∧
        Steps (suffix.plug ((saved a receipts seed).resume (embedValue response)))
          [.silent, .silent] (suffix.plug (.ret (OriginalSourceContinuationR342.identityValue a receipts))) := by
  refine ⟨OriginalModuleContextBindingR315.makeInitializer,
    OriginalModuleContextBindingR315.make_initializer_decoded,
    actual_source_projection origin a receipts, tick_request_resolves origin,
    OriginalSourceContinuationR342.plug_steps suffix (actual_prefix a receipts seed), ?_⟩
  intro response typed
  exact ⟨plug_typed hsuffix (Interaction.saved_resume_typed (actual_capture_typed a receipts seed)
    (embedValue_typed typed (empty_embedding emptyContext))),
    OriginalSourceContinuationR342.plug_steps suffix (actual_response_return a receipts seed _)⟩

end YulangClosure.OriginalHigherOrderCorrespondenceR343
