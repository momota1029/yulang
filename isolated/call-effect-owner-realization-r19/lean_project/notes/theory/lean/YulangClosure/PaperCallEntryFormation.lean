import YulangClosure.PaperExtendedExecution

/-!
The code-formation part of the operational manuscript, lines 362–395, and
corrected V5(4). A finite direct lambda/wrapper spine uses one already selected
owner. Wrapper argument code stays inside a delay; result adapters retain their
inner-to-outer order; only the lambda leaf receives the supplied literal View.

`ReceiptMetadata` is a selector of raw metadata, not an implementation or a law
about the corrected world. The source-shaped relation starts at `enter`, after
owner allocation, and preserves an enclosing scope. It does not turn a wrapped
`enter` into a second source `call`. Normalization of arbitrary callable values,
fresh owner/receipt construction, scope completion and current-world simulation
remain separate obligations. The original whole-language claim is unchanged.

The final theorem consumes the constructed code in the existing finite
interaction theorem. That executor has ordinary let frames but no owner/world
state: its traces are traces of the formed code, not an asserted execution of
the enclosing scope.
-/
namespace YulangClosure.PaperTypes.PaperCallEntryFormation

open PaperCoreControl

/-- The same selected owner and the actual lambda profile choose the literal
metadata attached at entry. No semantic property of this function is assumed. -/
abbrev ReceiptMetadata := OwnerName → AdapterMetadata → ViewMetadata

/-- Exactly the finite direct callable forms available after the independent
operand-observation/normalization obligation has been discharged. -/
inductive DirectCallableSpine : Value → Prop where
  | valueLambda (profile parameter body) :
      DirectCallableSpine (.lambda .value profile parameter body)
  | computationLambda (profile parameter body) :
      DirectCallableSpine (.lambda .computation profile parameter body)
  | wrap {function argumentAdapter resultAdapter} :
      DirectCallableSpine function →
      DirectCallableSpine (.wrap function argumentAdapter resultAdapter)

/-- O:366–370: form the suspended adapter, without evaluating its argument code. -/
def adaptedThunk (thunk : Value) (argumentAdapter : Computation) : Value :=
  .delay (.letE (.force thunk) argumentAdapter)

/-- Finite administrative formation, not a source Call evaluator. In particular
the recursive wrapper case retains the owner and never constructs `call`. -/
def entryCode (receipt : ReceiptMetadata) (owner : OwnerName) :
    Value → Value → Option Computation
  | .lambda .value profile _ body, thunk =>
      some (.letE (.force (.view (receipt owner profile) thunk)) body)
  | .lambda .computation profile _ body, thunk =>
      termSubstituteComputation
        (PaperCoreStep.singleReplacement (.view (receipt owner profile) thunk)) body
  | .wrap function argumentAdapter resultAdapter, thunk =>
      (entryCode receipt owner function (adaptedThunk thunk argumentAdapter)).map
        (fun code => .letE code resultAdapter)
  | _, _ => none

/-- The literal O:372–385 administrative steps, plus their active let/scope
contexts. The relation has no fresh-owner, world or receipt-construction rule. -/
inductive EnterStep (receipt : ReceiptMetadata) : Computation → Computation → Prop where
  | wrap (owner function thunk argumentAdapter resultAdapter) :
      EnterStep receipt (.enter owner (.wrap function argumentAdapter resultAdapter) thunk)
        (.letE (.enter owner function (adaptedThunk thunk argumentAdapter)) resultAdapter)
  | valueLambda (owner profile parameter body thunk) :
      EnterStep receipt (.enter owner (.lambda .value profile parameter body) thunk)
        (.letE (.force (.view (receipt owner profile) thunk)) body)
  | computationLambda {owner profile parameter body thunk code} :
      termSubstituteComputation
        (PaperCoreStep.singleReplacement (.view (receipt owner profile) thunk)) body =
          some code →
      EnterStep receipt (.enter owner (.lambda .computation profile parameter body) thunk) code
  | underLet {first next body} : EnterStep receipt first next →
      EnterStep receipt (.letE first body) (.letE next body)
  | underScope {owner first next} : EnterStep receipt first next →
      EnterStep receipt (.scope owner first) (.scope owner next)

inductive EnterTrace (receipt : ReceiptMetadata) : Computation → Computation → Prop where
  | refl (code) : EnterTrace receipt code code
  | tail {first middle last} : EnterTrace receipt first middle →
      EnterStep receipt middle last → EnterTrace receipt first last

theorem EnterTrace.trans {receipt first middle last}
    (left : EnterTrace receipt first middle) (right : EnterTrace receipt middle last) :
    EnterTrace receipt first last := by
  induction right with
  | refl => exact left
  | tail path step ih => exact .tail ih step

theorem EnterTrace.underLet {receipt first last} (path : EnterTrace receipt first last)
    (body : Computation) : EnterTrace receipt (.letE first body) (.letE last body) := by
  induction path with
  | refl => exact .refl _
  | tail path step ih => exact .tail ih (.underLet step)

theorem EnterTrace.underScope {receipt first last} (path : EnterTrace receipt first last)
    (owner : OwnerName) : EnterTrace receipt (.scope owner first) (.scope owner last) := by
  induction path with
  | refl => exact .refl _
  | tail path step ih => exact .tail ih (.underScope step)

/-- Ordinary surrounding lets stay outside the retained owner scope. -/
theorem EnterTrace.plug {receipt first last} (path : EnterTrace receipt first last)
    (stack : List Computation) : EnterTrace receipt (plug stack first) (plug stack last) := by
  induction stack generalizing first last with
  | nil => exact path
  | cons body rest ih => exact ih (path.underLet body)

theorem adaptedThunk_typed {d g e thunk argumentAdapter outerInput innerInput}
    (ht : PaperValueTyped d g e thunk (.thunk outerInput))
    (ha : PaperComputationTyped d g (outerInput :: e) argumentAdapter innerInput) :
    PaperValueTyped d g e (adaptedThunk thunk argumentAdapter) (.thunk innerInput) :=
  .delay (.letE (.force ht) ha)

/-- Construct the actual whole entry body and its finite source-shaped trace.
No body preservation, substitution success, or adapter safety is assumed.
All type and code witnesses are shared across the complete wrapper spine. -/
theorem spine_formation {d g e function thunk argument result}
    (spine : DirectCallableSpine function)
    (hf : PaperValueTyped d g e function (.callable argument result))
    (ht : PaperValueTyped d g e thunk (.thunk argument))
    (receipt : ReceiptMetadata) (owner : OwnerName) :
    ∃ code, entryCode receipt owner function thunk = some code ∧
      PaperComputationTyped d g e code result ∧
      EnterTrace receipt (.enter owner function thunk) code := by
  induction spine generalizing thunk argument result with
  | valueLambda profile parameter body =>
      cases hf with
      | valueLambda hb =>
          exact ⟨_, rfl, .letE (.force (.view ht)) hb,
            .tail (.refl _) (.valueLambda owner profile parameter body thunk)⟩
  | computationLambda profile parameter body =>
      cases hf with
      | computationLambda hb =>
          obtain ⟨code, hcode, htyped⟩ := hb.termSubstitute
            (PaperCoreStep.singleReplacement_typed
              (PaperValueTyped.view (metadata := receipt owner profile) ht))
          exact ⟨code, hcode, htyped, .tail (.refl _) (.computationLambda hcode)⟩
  | @wrap function argumentAdapter resultAdapter spine ih =>
      cases hf with
      | wrap hf ha hr =>
          obtain ⟨code, hcode, htyped, path⟩ :=
            ih hf (adaptedThunk_typed ht ha)
          refine ⟨.letE code resultAdapter, ?_, .letE htyped hr, ?_⟩
          · simp only [entryCode, hcode, Option.map_some]
          · exact (EnterTrace.tail (.refl _)
              (.wrap owner function thunk argumentAdapter resultAdapter)).trans
                (path.underLet resultAdapter)

/-- Start from the existing paper Call typing rule itself, and retain the
literal owner scope around the entire generated body. This does not execute
the fresh-owner allocation that precedes `enter`. -/
theorem call_spine_formation {d g e function thunk result}
    (hcall : PaperComputationTyped d g e (.call function thunk) result)
    (spine : DirectCallableSpine function)
    (receipt : ReceiptMetadata) (owner : OwnerName) :
    ∃ code, entryCode receipt owner function thunk = some code ∧
      PaperComputationTyped d g e code result ∧
      EnterTrace receipt (.enter owner function thunk) code ∧
      EnterTrace receipt (.scope owner (.enter owner function thunk)) (.scope owner code) := by
  cases hcall with
  | call hf ht =>
      obtain ⟨code, hcode, htyped, path⟩ := spine_formation spine hf ht receipt owner
      exact ⟨code, hcode, htyped, path, path.underScope owner⟩

/-- One shared constructed body supplies every finite admissible interaction
prefix. The trace here is explicitly the existing executor's trace of that
body; owner-scope/current-world execution is not silently erased into it. -/
theorem call_spine_finite_interaction {d g e function thunk result stack finalResult binder}
    (hd : PaperTemplateExecution.BodiesTyped d)
    (hcall : PaperComputationTyped d g e (.call function thunk) result)
    (spine : DirectCallableSpine function)
    (hstack : StackTyped d g e stack result finalResult)
    (receipt : ReceiptMetadata) (owner : OwnerName) :
    ∃ code, entryCode receipt owner function thunk = some code ∧
      PaperComputationTyped d g e code result ∧
      EnterTrace receipt (.scope owner (.enter owner function thunk)) (.scope owner code) ∧
      ∀ last, (path : PaperExtendedExecution.InteractionTrace d binder ⟨code, stack⟩ last) →
        PaperExtendedExecution.ProtocolTyped g e path →
        StateTyped d g e last finalResult ∧
        PaperComputationTyped d g e (erase last) finalResult ∧
        PaperExtendedExecution.InteractionErasure d binder
          (erase ⟨code, stack⟩) (erase last) := by
  obtain ⟨code, hcode, htyped, _, scopePath⟩ := call_spine_formation hcall spine receipt owner
  refine ⟨code, hcode, htyped, scopePath, ?_⟩
  intro last path protocol
  exact PaperExtendedExecution.finite_interaction hd ⟨result, htyped, hstack⟩ path protocol

/-- The current connected executor has no operand-View transition. This is an
obstruction in that partial executor, not stuckness of the corrected source. -/
theorem controlStep_force_view_none (d : DeclarationTable) (binder : TermName)
    (metadata : ViewMetadata) (thunk : Value) (stack : List Computation) :
    PaperExtendedExecution.controlStep d binder ⟨.force (.view metadata thunk), stack⟩ = none := by
  cases stack <;> rfl

/-- The actual Value-entry code reaches the precise missing observation seam
after one implemented let push, while retaining its exact typing and receipt.
The same owner scope is retained by the separate entry trace. No source-world
trace, progress or metadata erasure is inferred from this partial-executor fact. -/
theorem value_entry_view_frontier
    {d g e profile parameter body thunk result stack finalResult binder}
    (hcall : PaperComputationTyped d g e
      (.call (.lambda .value profile parameter body) thunk) result)
    (hstack : StackTyped d g e stack result finalResult)
    (receipt : ReceiptMetadata) (owner : OwnerName) :
    EnterTrace receipt
      (.scope owner (.enter owner (.lambda .value profile parameter body) thunk))
      (.scope owner (.letE (.force (.view (receipt owner profile) thunk)) body)) ∧
    PaperExtendedExecution.Trace d binder
      ⟨.letE (.force (.view (receipt owner profile) thunk)) body, stack⟩
      ⟨.force (.view (receipt owner profile) thunk), body :: stack⟩ ∧
    StateTyped d g e ⟨.force (.view (receipt owner profile) thunk), body :: stack⟩ finalResult ∧
    PaperExtendedExecution.controlStep d binder
      ⟨.force (.view (receipt owner profile) thunk), body :: stack⟩ = none := by
  cases hcall with
  | call hf ht =>
      cases hf with
      | valueLambda hb =>
          refine ⟨(EnterTrace.tail (.refl _)
            (.valueLambda owner profile parameter body thunk)).underScope owner,
            .tail (.refl _) ?_, ⟨_, .force (.view ht), .cons hb hstack⟩,
            controlStep_force_view_none d binder (receipt owner profile) thunk (body :: stack)⟩
          rfl

end YulangClosure.PaperTypes.PaperCallEntryFormation
