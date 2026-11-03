import YulangClosure.OriginalModuleContextBindingR315
import YulangClosure.CallDeclaredLiteralResponse

/-!
R321 partial source-declaration construction only. The actual R315 make/tick
occurrence below supplies the declaration/request premise of the existing
formal literal-response consumer. It supplies neither an actual formal Call
prefix from the native trace nor a full original EI interpretation/Union.
All nonliteral response domains and original EI/R159 obligations remain open.
-/
namespace YulangClosure.OriginalTickDeclaredResponseR321


/-- The full exported annotation is translated structurally, including effects,
variables, holes and tuple fields. The existing ground interpreter remains
partial; unsuccessful interpretation never removes an original source case. -/
def annotation : OriginalModuleContextBindingR315.Native.Make.AnnotationType → PrimitiveOperation.Annotation OriginalModuleContextBindingR315.Native.Make.EffectRow OriginalModuleContextBindingR315.Native.Make.Position
  | .mk (.unit) effects => .primitive effects .unit
  | .mk (.int) effects => .primitive effects .int
  | .mk (.bool) effects => .primitive effects .bool
  | .mk (.str) effects => .primitive effects .string
  | .mk (.variable name) effects => .variable effects name
  | .mk (.hole position) effects => .hole effects position
  | .mk (.tuple items) effects => .tuple effects (items.map annotation)
  | .mk (.function argument result) effects =>
      .function effects (annotation argument) (annotation result)

structure PositionKey where
  startByte : Nat
  endByte : Nat
  kind : String
  text : String
  deriving DecidableEq

def positionKey (p : OriginalModuleContextBindingR315.Native.Make.Position) : PositionKey :=
  ⟨p.startByte, p.endByte, p.kind, p.text⟩

/-- Original complete physical declaration identity, including family scope,
all original source positions and operation name. Signature is interpreted
separately; equal operation spellings do not identify source declarations. -/
structure OperationKey where
  name : String
  familyRealm : String
  familyPath : String
  familyDeclaration : PositionKey
  declaration : PositionKey
  namePosition : PositionKey
  signaturePosition : PositionKey
  startByte : Nat
  endByte : Nat
  visibility : String
  deriving DecidableEq

def operationKey (d : OriginalModuleContextBindingR315.Native.Make.OperationIdentity) : OperationKey :=
  ⟨d.name, d.familyRealm, d.familyPath, positionKey d.familyDeclaration,
    positionKey d.declaration, positionKey d.namePosition, positionKey d.signaturePosition,
    d.startByte, d.endByte, d.visibility⟩

def operationAt (ordinal : Nat) : Option OriginalModuleContextBindingR315.Native.Make.OperationIdentity := do
  let node ← OriginalModuleContextBindingR315.Native.Make.nodes.find? (fun node => node.ordinal == ordinal)
  match node.form with
  | .operation identity => some identity
  | _ => none

/-- Actual source ordinal 4, retained by R315's authenticated make export.
This is the tick operand inside make's statement-block App, rather than a
new operation chosen by spelling. -/
def tick : OriginalModuleContextBindingR315.Native.Make.OperationIdentity := (operationAt 4).get (by rfl)

def declaration (d : OriginalModuleContextBindingR315.Native.Make.OperationIdentity) :
    PrimitiveOperation.Declaration OperationKey OriginalModuleContextBindingR315.Native.Make.EffectRow OriginalModuleContextBindingR315.Native.Make.Position :=
  ⟨operationKey d, d.name, annotation d.signature⟩

/-- Every operation occurrence in the actual make source table, in source
order; duplicates remain. This is not a claim about the whole native module's
operation registration or its runtime numbering. -/
def operationInventory : List OriginalModuleContextBindingR315.Native.Make.OperationIdentity :=
  OriginalModuleContextBindingR315.Native.Make.nodes.filterMap fun node =>
    match node.form with
    | .operation identity => some identity
    | _ => none

def tickKeys : List OperationKey := operationInventory.map operationKey

def tickOperation : TypedCall.OperationInstance := PrimitiveOperation.instanceOf 0 .int .int

/-- Both syntax and exact original opcode lookup are outputs. This does not
assert that a native execution emitted the formal operation instance. -/
theorem tick_declaration_interpretation :
    operationAt 4 = some tick ∧
    OriginalModuleContextBindingR315.decodeMake 16 4 = some (.primitive ⟨4, none⟩ 12) ∧
    (declaration tick).signature = .function none (.primitive none .int) (.primitive none .int) ∧
    PrimitiveOperation.request tickKeys (declaration tick) = some tickOperation ∧
    PrimitiveOperation.expected (declaration tick) = some Original.Base.int := by
  have signature : (declaration tick).signature =
      .function none (.primitive none .int) (.primitive none .int) := by
    change annotation (.mk (.function (.mk .int none) (.mk .int none)) none) = _
    simp only [annotation]
  have identity : (declaration tick).identity = operationKey tick := rfl
  have keys : tickKeys = [operationKey tick] := rfl
  refine ⟨rfl, rfl, signature, ?_, ?_⟩
  · simp only [PrimitiveOperation.request, PrimitiveOperation.interpret, keys,
      PrimitiveOperation.number, identity, ↓reduceIte, signature, PrimitiveOperation.decode,
      PrimitiveOperation.primitive, Option.bind_eq_bind, Option.bind_some, Option.pure_def, tickOperation]
  · simp only [PrimitiveOperation.expected, signature, PrimitiveOperation.decode,
      PrimitiveOperation.primitive, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.map_some,
      PrimitiveOperation.Primitive.base]

/-- The declaration occurrence is the callee of the actual original App in
make's decoded body. This checks only the full original source inventory;
no semantic arm family is inferred from the single syntactic App. -/
theorem tick_source_application (origin : OriginalSource.Declaration) :
    (ComputedCallTypedFormationR310.requests origin []
      OriginalModuleContextBindingR315.makeInitializer).map
      (fun request => (request.original.site, request.original.calleeSite,
        request.original.argumentSite)) = [(3, 4, 5)] := by
  run_tac Lean.Meta.withTransparency .all <| Lean.Elab.Tactic.evalTactic (← `(tactic| rfl))

/-- The same actual source declaration now feeds the named existing response
consumer, eliminating its independently supplied request/signature equations.
All actual-prefix, completion, native acceptance and producer validity premises
are preserved. These formal-prefix premises are NOT derived from R315 events.
No equality to opaque OriginalSourceInterpretation.Inputs is introduced. -/
theorem actual_tick_request_completed_literal_response
    {W : Type} {sig : Control.Signature} {md : Control.Metadata W}
    {term : TypedCall.CallTerm} {world : W} {suffix : List Control.Frame}
    {result : Control.Ty} {n m : Nat} {s t : Control.CallState W}
    {payload : TypedCall.Value} {k : TypedCall.Comp}
    {observed : List TypedCall.ViewOccurrence}
    (hsuffix : Control.FramesTyped sig suffix (.original term.resultType) result)
    (hp : Prefix (Control.CallControlStep md) n (Control.CallState.initial term world suffix) s)
    (hhead : s.head = .requesting tickOperation payload k observed)
    (hpost : Prefix (Control.CallControlStep md) m s t)
    (hcomplete : ∃ op' payload' k', t.head = .requested op' payload' k')
    {role : NativeLiteral.Role} {sameValue : Prop} (datum : NativeLiteral.Datum)
    (haccept : NativeLiteral.Accepted (some Original.Base.int) role sameValue datum)
    (hproducer : NativeLiteral.WellFormed datum) :
    ∃ l : Original.Literal,
      NativeLiteral.readback datum = some l ∧ l.base = Original.Base.int ∧
      TypedCall.ValueTyped Original.emptyContext (TypedCall.literalResponse l) tickOperation.responseType ∧
      m = s.frames.length + 1 ∧
      t = s.requestBoundary md (s.frames.length + 1) ∧
      t.head = .requested tickOperation payload (Control.CallState.captureFrames s.frames k) ∧
      Control.CallStateTyped sig t result ∧ t.literalSuffix = suffix ∧
      TypedCall.CompTyped Original.emptyContext
        (Control.plugResponse (Control.CallState.captureFrames s.frames k) (TypedCall.literalResponse l)) term.resultType ∧
      TypedCall.CompTyped Original.emptyContext
        (TypedCall.plugFrames s.frames (Control.plugResponse k (TypedCall.literalResponse l))) term.resultType := by
  exact Control.actual_call_request_completed_declared_literal_response
    hsuffix hp hhead hpost hcomplete datum haccept hproducer
    tickKeys (declaration tick) tick_declaration_interpretation.2.2.2.1
    tick_declaration_interpretation.2.2.2.2

end YulangClosure.OriginalTickDeclaredResponseR321
