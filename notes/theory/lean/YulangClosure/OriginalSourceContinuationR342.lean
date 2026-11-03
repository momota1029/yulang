import YulangClosure.OriginalSourcePrimitiveBridgeR336
import YulangClosure.HigherOrderEmbedding
import YulangClosure.HigherOrderInteraction

/-!
R342: actual R315 source constructor projection and a higher-order execution
prefix. The existing TypedCall fragment cannot return the final source lambda.
The HigherOrder candidate keeps that lambda and its body consumer literally.
Receipt data is universally quantified; no original receipt/EI interpretation,
native simulation, arbitrary Inputs law or R159 admission is inferred here.
-/
namespace YulangClosure.OriginalSourceContinuationR342

open OriginalSourceScopedInterpretationR335 OriginalSourcePrimitiveBridgeR336
open OriginalTickDeclaredResponseR321
open HigherOrder HigherOrder.Safety

def intType : Ty := .base .int

def identityAdapter (a : Ty) : Adapter := .mk a a (.ret (.var 0)) [] []

theorem identity_adapter_typed (env : Context) (a : Ty) :
    AdapterTyped env (identityAdapter a) a a := .mk (.ret (.var rfl))

def operationValue (receipt : ReceiptTemplate) (op : OperationInstance) : Value :=
  .lambda .value receipt op.payloadType op.responseType op.responseType
    (.request op (.var 0) (.ret (.var 0))) (identityAdapter op.responseType)

theorem operation_value_typed (env : Context) (receipt : ReceiptTemplate)
    (op : OperationInstance) :
    ValueTyped env (operationValue receipt op) (.callable op.payloadType op.responseType) :=
  .lambdaValue (.request (.var rfl) (.ret (.var rfl))) (identity_adapter_typed env _)

/-- Ordinary lexical lookup counts discarded-result binders, without naming
them as source variables. This avoids capturing seed beneath callee/discard. -/
def indexOf (name : OriginalSource.Name) : List (Option OriginalSource.Name) → Option Nat
  | [] => none
  | head :: tail => if head = some name then some 0 else (indexOf name tail).map Nat.succ

/- Partial syntax projection, not an alternate source typing relation.
Unsupported constructors/annotations fail explicitly. Primitive code can only
come from R335/R336's full original Key and physical declaration resolution.
The supplied type/receipt decorations carry no semantic success assumptions. -/
mutual
  def project (origin : OriginalSource.Declaration) (receipts : Nat → ReceiptTemplate)
      (arguments results : Nat → Ty) : Nat → List (Option OriginalSource.Name) →
      OriginalSource.Source .expression → Option Comp
    | 0, _, _ => none
    | fuel + 1, names, raw =>
      match raw with
      | .name mark name => if mark.annotation.isSome then none else
          (indexOf name names).map fun index => .ret (.var index)
      | .primitive mark identifier => do
          if mark.annotation.isSome then none else do
            let entry ← (primitiveTable origin [] OriginalModuleContextBindingR315.makeInitializer).find?
              (fun entry => entry.site == mark.site && entry.identifier == identifier)
            let op ← sourceRequest origin entry.key .primitiveDeclarationInstance
            pure (.ret (operationValue (receipts mark.site) (embedOperation op)))
      | .lambda mark formal pattern body =>
          if mark.annotation.isSome || formal.annotation.isSome || formal.outerComputation then none else
          match pattern with
          | .varPattern _ name => if name = formal.name then do
              let body ← project origin receipts arguments results fuel (some name :: names) body
              pure (.ret (.lambda .value (receipts mark.site) (arguments mark.site)
                (results mark.site) (results mark.site) body (identityAdapter (results mark.site))))
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
  operationValue (receipts 4) (embedOperation tickOperation)

def identityValue (a : Ty) (receipts : Nat → ReceiptTemplate) : Value :=
  .lambda .value (receipts 2) a a a (.ret (.var 0)) (identityAdapter a)

def body (a : Ty) (receipts : Nat → ReceiptTemplate) : Comp :=
  .bind (sourceApply (.ret (tickValue receipts)) (.ret (.var 0)))
    (.ret (identityValue a receipts))

def makeValue (a : Ty) (receipts : Nat → ReceiptTemplate) : Value :=
  .lambda .value (receipts 0) intType (.callable a a) (.callable a a)
    (body a receipts) (identityAdapter (.callable a a))

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
    indexOf, argumentTypes, resultTypes]
  simp only [Option.isSome_none, Bool.or_false, Bool.false_eq_true, ↓reduceIte]
  rw [table]
  change (do
    let body ← (do
      let first ← (do
        let callee ← (do
          let op ← sourceRequest origin (tickPrimitive origin).key .primitiveDeclarationInstance
          pure (Comp.ret (operationValue (receipts 4) (embedOperation op))))
        pure (sourceApply callee (.ret (.var 0))))
      pure (Comp.bind first (.ret (identityValue a receipts))))
    pure (Comp.ret (.lambda .value (receipts 0) intType (.callable a a) (.callable a a)
      body (identityAdapter (.callable a a))))) = _
  rw [(tick_original_program origin).2, tick_request_resolves]
  rfl

theorem identity_value_typed (env : Context) (a : Ty) (receipts : Nat → ReceiptTemplate) :
    ValueTyped env (identityValue a receipts) (.callable a a) :=
  .lambdaValue (.ret (.var rfl)) (identity_adapter_typed env a)

theorem body_typed (a : Ty) (receipts : Nat → ReceiptTemplate) :
    CompTyped (extend emptyContext intType) (body a receipts) (.callable a a) := by
  apply CompTyped.bind
  · exact sourceApply_typed (.ret (operation_value_typed _ _ _)) (.ret (.var rfl))
  · exact .ret (identity_value_typed _ a receipts)

theorem make_value_typed (a : Ty) (receipts : Nat → ReceiptTemplate) :
    ValueTyped emptyContext (makeValue a receipts) (.callable intType (.callable a a)) :=
  .lambdaValue (body_typed a receipts) (identity_adapter_typed _ _)

def program (a : Ty) (receipts : Nat → ReceiptTemplate) (seed : Int) : Comp :=
  sourceApply (.ret (makeValue a receipts)) (.ret (.int seed))

def makePlan (a : Ty) (receipts : Nat → ReceiptTemplate) (seed : Int) : LambdaEntryPlan :=
  ⟨.value, receipts 0, intType, .callable a a, .callable a a,
    body a receipts, identityAdapter (.callable a a), .delay (.ret (.int seed))⟩

def tickPlan (receipts : Nat → ReceiptTemplate) (seed : Int) : LambdaEntryPlan :=
  ⟨.value, receipts 4, intType, intType, intType,
    .request (embedOperation tickOperation) (.var 0) (.ret (.var 0)),
    identityAdapter intType, .delay (.ret (.int seed))⟩

/-- Primitive declared-result consumer, original block discard/final lambda,
then make's declared-result consumer, in their actual nested order. -/
def savedContext (a : Ty) (receipts : Nat → ReceiptTemplate) : EvalContext :=
  .bind (.bind (.bind .hole (.ret (.var 0))) (.ret (identityValue a receipts)))
    (.ret (.var 0))

def saved (a : Ty) (receipts : Nat → ReceiptTemplate) (seed : Int) : Interaction.Saved :=
  ⟨embedOperation tickOperation, .int seed, .ret (.var 0), savedContext a receipts⟩

def events (a : Ty) (receipts : Nat → ReceiptTemplate) (seed : Int) : List Event :=
  [.silent, .lambdaEntry (makePlan a receipts seed), .silent, .silent, .silent,
    .lambdaEntry (tickPlan receipts seed), .silent, .silent]

/-- Eight actual constructor rules, starting before callee Bind and Delay.
No requesting-head, completed body or finite-prefix premise is supplied. -/
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
    (.ret (identityValue a receipts))) (.ret (.var 0))) _ _
  refine .cons (.bind (.bind .bindReturn)) ?_
  change Steps (.bind (.bind (.dynamicCall (tickValue receipts) (.delay (.ret (.int seed))))
    (.ret (identityValue a receipts))) (.ret (.var 0))) _ _
  refine .cons (.bind (.bind .callLambda)) ?_
  change Steps (.bind (.bind (.bind (.bind (.force (.delay (.ret (.int seed))))
    (.request (embedOperation tickOperation) (.var 0) (.ret (.var 0))))
    (.ret (.var 0))) (.ret (identityValue a receipts))) (.ret (.var 0))) _ _
  refine .cons (.bind (.bind (.bind (.bind .force)))) ?_
  refine .cons (.bind (.bind (.bind .bindReturn))) ?_
  exact .refl _

theorem program_typed (a : Ty) (receipts : Nat → ReceiptTemplate) (seed : Int) :
    CompTyped emptyContext (program a receipts seed) (.callable a a) :=
  sourceApply_typed (.ret (make_value_typed a receipts)) (.ret .int)

theorem actual_capture_typed (a : Ty) (receipts : Nat → ReceiptTemplate) (seed : Int) :
    Interaction.SavedTyped (saved a receipts seed) (.callable a a) :=
  Interaction.capture_typed
    (trace_preservation (actual_prefix a receipts seed) (program_typed a receipts seed))

/-- A response is consumed once by tick's result adapter, discarded by the
original expression statement, then make returns the actual identity lambda.
No special response, response views, or finished suffix are assumed. -/
theorem actual_response_return (a : Ty) (receipts : Nat → ReceiptTemplate) (seed : Int)
    (response : Value) :
    Steps ((saved a receipts seed).resume response) [.silent, .silent, .silent]
      (.ret (identityValue a receipts)) := by
  refine .cons (.bind (.bind .bindReturn)) ?_
  refine .cons (.bind .bindReturn) ?_
  refine .cons .bindReturn ?_
  exact .refl _

theorem actual_request_suspended (a : Ty) (receipts : Nat → ReceiptTemplate) (seed : Int) :
    Suspended (saved a receipts seed).request ∧
    ¬ ∃ event next, Safety.Step (saved a receipts seed).request event next := by
  refine ⟨Interaction.saved_request_suspended _, ?_⟩
  rintro ⟨event, next, step⟩
  exact Interaction.publication_has_no_internal_step _ step

theorem plug_step {m n : Comp} {event : Event} (suffix : EvalContext) (step : Safety.Step m event n) :
    Safety.Step (suffix.plug m) event (suffix.plug n) := by
  induction suffix with
  | hole => exact step
  | bind _ _ ih => exact .bind ih
  | scope _ _ ih => exact .scope ih
  | expose _ _ _ ih => exact .expose ih

theorem plug_steps {m n : Comp} {trace : List Event} (suffix : EvalContext) (steps : Steps m trace n) :
    Steps (suffix.plug m) trace (suffix.plug n) := by
  induction steps with
  | refl => exact .refl _
  | cons step _ ih => exact .cons (plug_step suffix step) ih

/-- A concrete source projection, reached capture and named response consumer.
Every original typed response (including all view lists) is embedded whole.
The SAME literal outer context is used by the prefix and every resumed result.
This is a HigherOrder value-typing result, not the R336 Control theorem. -/
theorem actual_source_response_consumer (origin : OriginalSource.Declaration)
    (a : Ty) (receipts : Nat → ReceiptTemplate) (seed : Int)
    (suffix : EvalContext) (result : Ty)
    (hsuffix : ContextTyped emptyContext suffix (.callable a a) result) :
    project origin receipts (argumentTypes a) (resultTypes a) 16 []
      OriginalModuleContextBindingR315.makeInitializer = some (.ret (makeValue a receipts)) ∧
    sourceRequest origin (tickRequest origin).operands.callee.key
      .primitiveDeclarationInstance = some tickOperation ∧
    Steps (suffix.plug (program a receipts seed)) (events a receipts seed)
      (suffix.plug (saved a receipts seed).request) ∧
    Interaction.SavedTyped (saved a receipts seed) (.callable a a) ∧
    ∀ response, TypedCall.ValueTyped Original.emptyContext response tickOperation.responseType →
      CompTyped emptyContext (suffix.plug ((saved a receipts seed).resume (embedValue response))) result := by
  refine ⟨actual_source_projection origin a receipts, tick_request_resolves origin,
    plug_steps suffix (actual_prefix a receipts seed), actual_capture_typed a receipts seed, ?_⟩
  intro response typed
  apply plug_typed hsuffix
  apply Interaction.saved_resume_typed (actual_capture_typed a receipts seed)
  exact embedValue_typed typed (empty_embedding emptyContext)

/-- Authentication starts at R315's retained native initializer decoder.
Both the native source root and the actual post-response lambda are outputs.
This joins syntax/typing/prefix data, without asserting a native simulation. -/
theorem decoded_source_prefix_and_return (origin : OriginalSource.Declaration)
    (a : Ty) (receipts : Nat → ReceiptTemplate) (seed : Int)
    (suffix : EvalContext) (result : Ty)
    (hsuffix : ContextTyped emptyContext suffix (.callable a a) result) :
    ∃ raw : OriginalSource.Source .expression,
      OriginalModuleContextBindingR315.decodeMake 16
        OriginalModuleContextBindingR315.Native.Make.rootInitializer = some raw ∧
      project origin receipts (argumentTypes a) (resultTypes a) 16 [] raw =
        some (.ret (makeValue a receipts)) ∧
      Steps (suffix.plug (program a receipts seed)) (events a receipts seed)
        (suffix.plug (saved a receipts seed).request) ∧
      ∀ response, TypedCall.ValueTyped Original.emptyContext response tickOperation.responseType →
        CompTyped emptyContext
          (suffix.plug ((saved a receipts seed).resume (embedValue response))) result ∧
        Steps (suffix.plug ((saved a receipts seed).resume (embedValue response)))
          [.silent, .silent, .silent] (suffix.plug (.ret (identityValue a receipts))) := by
  have consumer := actual_source_response_consumer origin a receipts seed suffix result hsuffix
  refine ⟨OriginalModuleContextBindingR315.makeInitializer,
    OriginalModuleContextBindingR315.make_initializer_decoded, consumer.1, consumer.2.2.1, ?_⟩
  intro response typed
  exact ⟨consumer.2.2.2.2 response typed,
    plug_steps suffix (actual_response_return a receipts seed (embedValue response))⟩

/-- The exact old type image has no callable result. This explains the missing
R336 Control application; it does not refute a future richer correspondence. -/
theorem callable_not_old_type (old : Original.Ty) (a b : Ty) :
    embedTy old ≠ .callable a b := by cases old <;> intro h <;> cases h

end YulangClosure.OriginalSourceContinuationR342
