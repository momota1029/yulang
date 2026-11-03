import YulangClosure.OriginalSourceScopedInterpretationR335

/-!
R336: authentic source Key -> physical primitive declaration -> formal response
clause -> named captured-continuation consumer. The source resolver checks the
full R335 Key/use and then the actual retained native declaration identity.
There is no supplied registry, source judgment, EI child or guard-law callback.

The resulting clause concerns the existing formal TypedCall response calculus.
It is NOT a registered original Inputs clause or a proof of a R311 primitive
leaf. The formal reached-prefix and source/native correspondence obligations
are kept distinct. Authority: EI §§3.1, 3.3–3.4 and original SG primitive rule;
R315/R321 retain the actual make/tick source and physical declaration identity.
-/
namespace YulangClosure.OriginalSourcePrimitiveBridgeR336

open OriginalSource OriginalScopedClosure OriginalSourceInterpretation
open OriginalSourceEnvironment OriginalSourceChecking
open ComputedCallTypedFormationR310 SourceGraphRegistrationR297 OriginalSourceScopedInterpretationR335
open OriginalTickDeclaredResponseR321 OriginalSourceAuthenticatedEIR332

/-- The callee reference and primitive declaration use the SAME full source
Key. This resolves the original R311 callee-clause operand without moving to
its distinct incidence key or changing the surrounding original telescope. -/
theorem tick_callee_resolves (origin : Declaration) :
    readCallee origin [] OriginalModuleContextBindingR315.makeInitializer
      (tickRequest origin).operands.callee.key = some (tickRequest origin) := by
  with_unfolding_all
    change (match (tickRequest origin).operands.callee.key == (tickRequest origin).operands.callee.key with
      | true => some (tickRequest origin) | false => _) = _
  simp only [beq_self_eq_true]

/-- Readback into the UNCHANGED original clause used by R311's callee phase.
Every world/result/future field remains in that clause. Truth of the clause
is not inferred from syntax or the separate formal response typing below. -/
theorem tick_callee_clause_readback {s : Sorts} {View : Type}
    (inputs : Inputs s) (state : Decoded s View) (origin : Declaration)
    (raw : RawObservation s) :
    calleeClause inputs state origin [] OriginalModuleContextBindingR315.makeInitializer
      (tickRequest origin).operands.callee.key raw =
        some (clause inputs (.trace (raw.atInterface
          (state.interfaces ⟨(tickRequest origin).original.calleeSite, .synthesis⟩)))) := by
  simp only [calleeClause, tick_callee_resolves, Option.map_some]

/-- Interpret an authentic primitive occurrence by its original source ordinal
and physical declaration span. No name-only or endpoint-only lookup is used. -/
def sourceOperation (origin : Declaration) (key : Key) (use : AtomKind) :
    Option OriginalModuleContextBindingR315.Native.Make.OperationIdentity := do
  let entry ← readPrimitive origin [] OriginalModuleContextBindingR315.makeInitializer key use
  let operation ← operationAt entry.site
  if entry.identifier = operation.declaration.startByte then some operation else none

/-- The independently defined formal interpreter consumes the full physical
identity and full retained signature, rather than a fabricated numeric opcode. -/
def sourceRequest (origin : Declaration) (key : Key) (use : AtomKind) :
    Option TypedCall.OperationInstance := do
  let operation ← sourceOperation origin key use
  PrimitiveOperation.request tickKeys (declaration operation)

theorem tick_operation_resolves (origin : Declaration) :
    sourceOperation origin (tickRequest origin).operands.callee.key
      .primitiveDeclarationInstance = some tick := by
  simp only [sourceOperation, tick_scoped_declaration_resolves]
  change (operationAt 4 >>= fun operation =>
    if 12 = operation.declaration.startByte then some operation else none) = some tick
  rw [tick_declaration_interpretation.1]
  rfl

/-- Complete source-key falsifier: altered source origin/route/telescope/frame,
local scope/sort/slot or primitive-use cannot borrow this physical declaration. -/
theorem source_operation_exact (origin : Declaration) (key : Key) (use : AtomKind)
    (operation : OriginalModuleContextBindingR315.Native.Make.OperationIdentity) :
    sourceOperation origin key use = some operation ↔
      use = .primitiveDeclarationInstance ∧ (tickPrimitive origin).key = key ∧
        operation = tick := by
  constructor
  · intro found
    unfold sourceOperation at found
    cases resolved : readPrimitive origin [] OriginalModuleContextBindingR315.makeInitializer key use with
    | none => simp [resolved, Option.bind_eq_bind] at found
    | some entry =>
      obtain ⟨correct, sameKey, sameEntry⟩ := (tick_resolution_exact origin key use entry).mp resolved
      subst entry
      have canonical := tick_operation_resolves origin
      unfold sourceOperation at canonical
      rw [tick_scoped_declaration_resolves] at canonical
      rw [resolved] at found
      have same : some operation = some tick := found.symm.trans canonical
      exact ⟨correct, sameKey, Option.some.inj same⟩
  · rintro ⟨rfl, sameKey, rfl⟩
    rw [← sameKey, (tick_original_program origin).2]
    exact tick_operation_resolves origin

theorem tick_request_resolves (origin : Declaration) :
    sourceRequest origin (tickRequest origin).operands.callee.key
      .primitiveDeclarationInstance = some tickOperation := by
  simp only [sourceRequest, tick_operation_resolves]
  exact tick_declaration_interpretation.2.2.2.1

/-- Source scope/identity are consequences of successful resolution, before
any formal typing or semantic observation assumption is introduced. -/
theorem source_request_exact (origin : Declaration) (key : Key) (use : AtomKind)
    (operation : TypedCall.OperationInstance) :
    sourceRequest origin key use = some operation ↔
      use = .primitiveDeclarationInstance ∧ (tickPrimitive origin).key = key ∧
        operation = tickOperation := by
  constructor
  · intro found
    unfold sourceRequest at found
    cases resolved : sourceOperation origin key use with
    | none => simp [resolved, Option.bind_eq_bind] at found
    | some source =>
      obtain ⟨correct, sameKey, rfl⟩ := (source_operation_exact origin key use source).mp resolved
      rw [resolved] at found
      change PrimitiveOperation.request tickKeys (declaration tick) = some operation at found
      rw [tick_declaration_interpretation.2.2.2.1] at found
      have found := Option.some.inj found
      exact ⟨correct, sameKey, found.symm⟩
  · rintro ⟨rfl, sameKey, rfl⟩
    rw [← sameKey, (tick_original_program origin).2]
    exact tick_request_resolves origin

/-- Actual original row and complete physical identity are retained together
with the exact full formal response domain, including ordered duplicate views. -/
theorem resolved_source_response_domain (origin : Declaration) (key : Key)
    (use : AtomKind) (operation : TypedCall.OperationInstance)
    (found : sourceRequest origin key use = some operation) (value : TypedCall.Value) :
    ∃ row ∈ sourceInventory origin [] OriginalModuleContextBindingR315.makeInitializer,
      row.program = (tickPrimitive origin).program ∧
      use = .primitiveDeclarationInstance ∧ (tickPrimitive origin).key = key ∧
      (tickPrimitive origin).identifier = tick.declaration.startByte ∧
      operation = tickOperation ∧
      (TypedCall.ValueTyped Original.emptyContext value operation.responseType ↔
        ∃ integer views, value = response integer views) := by
  obtain ⟨correct, sameKey, rfl⟩ := (source_request_exact origin key use operation).mp found
  obtain ⟨_, _, row, member, _, same⟩ := primitive_resolution_authentic origin []
    OriginalModuleContextBindingR315.makeInitializer
    (tickRequest origin).operands.callee.key .primitiveDeclarationInstance
    (tickPrimitive origin) (tick_scoped_declaration_resolves origin)
  exact ⟨row, member, same, correct, sameKey, rfl, rfl, response_domain_exact value⟩

/-- Fixed formal response clause, computed from the source declaration. This
contains no arbitrary body callback and does not claim original trace Meaning.
It keeps every typed response and the SAME captured and residual continuation. -/
def formalResponseClause {s : Sorts} (origin : Declaration) (key : Key) (use : AtomKind)
    (frames : List TypedCall.ContextFrame) (continuation : TypedCall.Comp)
    (result : Original.Ty) : Option (Positive s) :=
  (sourceRequest origin key use).map fun operation =>
    .all {value : TypedCall.Value //
      TypedCall.ValueTyped Original.emptyContext value operation.responseType} fun value =>
      .both (.guard (TypedCall.CompTyped Original.emptyContext
        (Control.plugResponse (Control.CallState.captureFrames frames continuation) value.val) result))
        (.both (.guard (Control.plugResponse (Control.CallState.captureFrames frames continuation) value.val =
          TypedCall.plugFrames frames (Control.plugResponse continuation value.val)))
          (.guard (TypedCall.CompTyped Original.emptyContext
            (TypedCall.plugFrames frames (Control.plugResponse continuation value.val)) result)))

/-- Readback retains precisely the original formal response domain; it does
not substitute one native response sample or strip response view wrappers. -/
theorem formal_response_clause_exact {s : Sorts} (origin : Declaration)
    (frames : List TypedCall.ContextFrame) (continuation : TypedCall.Comp)
    (result : Original.Ty) (Z : Family s) :
    (∃ body : Positive s, formalResponseClause origin (tickRequest origin).operands.callee.key
      .primitiveDeclarationInstance frames continuation result = some body ∧ body.Holds Z) ↔
    ∀ integer views,
      TypedCall.CompTyped Original.emptyContext
        (Control.plugResponse (Control.CallState.captureFrames frames continuation)
          (response integer views)) result ∧
      Control.plugResponse (Control.CallState.captureFrames frames continuation) (response integer views) =
        TypedCall.plugFrames frames (Control.plugResponse continuation (response integer views)) ∧
      TypedCall.CompTyped Original.emptyContext
        (TypedCall.plugFrames frames (Control.plugResponse continuation (response integer views))) result := by
  simp only [formalResponseClause, tick_request_resolves, Option.map_some,
    Option.some.injEq, exists_eq_left', Positive.Holds, Subtype.forall]
  exact all_responses_iff _

/-- Apply the actual source response clause to the named Control consumer.
Unlike R332's completed-request theorem, neither a post-prefix, its length,
a terminal state nor completion is an input: the exact boundary is constructed.
The initial formal prefix and its actual requesting head remain independent
premises. Original Inputs, native correspondence and R159 admission are OPEN. -/
theorem source_bound_request_boundary
    {sorts : Sorts} (Z : Family sorts) (origin : Declaration)
    {W : Type} {sig : Control.Signature} {md : Control.Metadata W}
    {term : TypedCall.CallTerm} {world : W} {suffix : List Control.Frame}
    {result : Control.Ty} {n : Nat} {state : Control.CallState W}
    {payload : TypedCall.Value} {continuation : TypedCall.Comp}
    {observed : List TypedCall.ViewOccurrence}
    (hsuffix : Control.FramesTyped sig suffix (.original term.resultType) result)
    (hp : Prefix (Control.CallControlStep md) n
      (Control.CallState.initial term world suffix) state)
    (hhead : state.head = .requesting tickOperation payload continuation observed) :
    let boundary := state.requestBoundary md (state.frames.length + 1)
    Prefix (Control.CallControlStep md) (n + (state.frames.length + 1))
      (Control.CallState.initial term world suffix) boundary ∧
    Control.CallStateTyped sig boundary result ∧
    boundary = {state with
      world := (Control.CallState.requestWorldScopes md state.frames state.world state.scopeContext).1
      head := .requested tickOperation payload (Control.CallState.captureFrames state.frames continuation)
      frames := []
      scopeContext := (Control.CallState.requestWorldScopes md state.frames state.world state.scopeContext).2
      viewContext := observed} ∧
    boundary.resultType = term.resultType ∧ boundary.literalSuffix = suffix ∧
    TypedCall.ValueTyped Original.emptyContext payload tickOperation.payloadType ∧
    TypedCall.CompTyped (Original.extend Original.emptyContext tickOperation.responseType)
      (Control.CallState.captureFrames state.frames continuation) term.resultType ∧
    ∃ body : Positive sorts,
      formalResponseClause origin (tickRequest origin).operands.callee.key
        .primitiveDeclarationInstance state.frames continuation term.resultType = some body ∧ body.Holds Z := by
  have initial := Control.initial_call_request_boundary_response hsuffix hp hhead (response_typed 0 [])
  refine ⟨initial.1, initial.2.1, Control.call_request_state_boundary_complete md hhead,
    initial.2.2.2.2.1, initial.2.2.2.2.2.1, initial.2.2.2.2.2.2.1,
    initial.2.2.2.2.2.2.2.1, ?_⟩
  apply (formal_response_clause_exact origin state.frames continuation term.resultType Z).mpr
  intro integer views
  have checked := Control.initial_call_request_boundary_response hsuffix hp hhead
    (response_typed integer views)
  exact checked.2.2.2.2.2.2.2.2

end YulangClosure.OriginalSourcePrimitiveBridgeR336
