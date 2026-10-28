import YulangClosure.PaperCallEntryFormation
import YulangClosure.PaperViewExecution

/-!
Constructor facts for the actual identity/retained-relay spine, using the
existing paper syntax and typing relation. No source calculus, semantic
Function-membership relation, or safety-defined typing is introduced here.

The source correspondence is deliberately partial. `identity` represents
the unannotated Value-entry `\x -> x`; `relay` represents the Computation-entry
`\(thunk : [] (int -> int)) -> thunk`, whose Result consumes the retained
computation. The parameter types remain arbitrary in these proofs. The actual
identity closure and its delayed argument carrier are distinct raw values.

PaperValueTyped is not the source's contextual ValueMem. In particular these
results do not prove original ActualAdm, full D_F/P_F membership, receipt or
current-world guard validity, source annotation realization, or an instance of
SourceProblem.sourceJudgment. The finite interaction result uses precisely the
existing paper executor and its independent typed-response protocol; it does
not claim that this executor covers every original observation.
-/
namespace YulangClosure.PaperTypes.SourceIdentityLambda

open PaperCoreControl
open PaperCallEntryFormation

def identityBody : Computation := .ret (.variable 0)

def identity (profile : AdapterMetadata) (parameter : TermName) : Value :=
  .lambda .value profile parameter identityBody

def relayBody : Computation := .force (.variable 0)

def relay (profile : AdapterMetadata) (parameter : TermName) : Value :=
  .lambda .computation profile parameter relayBody

/-- The returned descriptor is exactly the formal's descriptor. This is a
syntax-directed Name/Return derivation, with no body-typing premise. -/
theorem identity_body_typed (d : DeclarationTable) (g : GraphEnvironment)
    (e : TypeEnvironment) (a : Ty) :
    PaperComputationTyped d g (a :: e) identityBody a :=
  .ret (.variable rfl)

/-- Actual introduction at every paper type, including latent values. This
does not assert a generalized source scheme or a full contextual descriptor. -/
theorem identity_typed (d : DeclarationTable) (g : GraphEnvironment)
    (e : TypeEnvironment) (a : Ty) (profile : AdapterMetadata)
    (parameter : TermName) :
    PaperValueTyped d g e (identity profile parameter) (.callable a a) :=
  .valueLambda (identity_body_typed d g e a)

/-- Construct Value entry from an independently typed whole carrier. The
literal receipt View is retained and the parameter binding remains a suffix. -/
theorem identity_entry_formation {d g e a carrier}
    (hc : PaperValueTyped d g e carrier (.thunk a))
    (profile : AdapterMetadata) (parameter : TermName)
    (receipt : ReceiptMetadata) (owner : OwnerName) :
    entryCode receipt owner (identity profile parameter) carrier =
        some (.letE (.force (.view (receipt owner profile) carrier)) identityBody) ∧
    PaperComputationTyped d g e
        (.letE (.force (.view (receipt owner profile) carrier)) identityBody) a ∧
    EnterTrace receipt
        (.scope owner (.enter owner (identity profile parameter) carrier))
        (.scope owner
          (.letE (.force (.view (receipt owner profile) carrier)) identityBody)) := by
  refine ⟨rfl, .letE (.force (.view hc)) (identity_body_typed d g e a), ?_⟩
  exact (EnterTrace.tail (.refl _)
    (.valueLambda owner profile parameter identityBody carrier)).underScope owner

/-- Result rebind substitutes the identical raw value, preserving every raw
provider/view field inside it. It does not reinterpret that value as a carrier. -/
theorem identity_result_substitution (value : Value) :
    termSubstituteComputation (PaperCoreStep.singleReplacement value) identityBody =
      some (.ret value) := by
  simp [termSubstituteComputation, identityBody, supportedTermComputation,
    supportedTermValue, replaceTermComputation, replaceTermValue,
    PaperCoreStep.singleReplacement]

/-- The identity suffix returns the argument's actual returned raw value.
The surrounding continuation is preserved literally. -/
theorem identity_result_step (value : Value) (stack : List Computation) :
    PaperCoreControl.controlStep ⟨.ret value, identityBody :: stack⟩ =
      some ⟨.ret value, stack⟩ := by
  simp only [PaperCoreControl.controlStep, identity_result_substitution, Option.map_some]

/-- All admitted finite interactions of an arbitrary represented argument
retain the typed identity suffix. Refl includes the zero-step prefix. There
is no Return or termination premise, and internal steps need no safety proof.
Only external response values use the existing protocol's typing condition. -/
theorem identity_argument_interactions
    {d g e a argument stack result binder last}
    (hd : PaperTemplateExecution.BodiesTyped d)
    (ha : PaperComputationTyped d g e argument a)
    (hs : StackTyped d g e stack a result)
    (path : PaperExtendedExecution.InteractionTrace d binder
      ⟨argument, identityBody :: stack⟩ last)
    (protocol : PaperExtendedExecution.ProtocolTyped g e path) :
    StateTyped d g e last result ∧
      PaperComputationTyped d g e (erase last) result ∧
      PaperExtendedExecution.InteractionErasure d binder
        (erase ⟨argument, identityBody :: stack⟩) (erase last) :=
  PaperExtendedExecution.finite_interaction hd
    ⟨a, ha, .cons (identity_body_typed d g e a) hs⟩ path protocol

/-- Fill an independently typed callable hole by the constructed identity,
then handle every represented finite interaction of the filled context.
The context's derivation is under a variable assumption, not under assumed
membership of this identity. The actual substitution is constructed, including
success of the partial substitution function. This is the paper syntactic
analogue of the missing original punctured-context instantiation action. -/
theorem identity_context_interactions
    {d g e a punctured result stack finalResult binder}
    (hd : PaperTemplateExecution.BodiesTyped d)
    (context : PaperComputationTyped d g (.callable a a :: e) punctured result)
    (hs : StackTyped d g e stack result finalResult)
    (profile : AdapterMetadata) (parameter : TermName) :
    ∃ filled,
      termSubstituteComputation
        (PaperCoreStep.singleReplacement (identity profile parameter)) punctured =
          some filled ∧
      PaperComputationTyped d g e filled result ∧
      ∀ last, (path : PaperExtendedExecution.InteractionTrace d binder
        ⟨filled, stack⟩ last) →
        PaperExtendedExecution.ProtocolTyped g e path →
        StateTyped d g e last finalResult ∧
          PaperComputationTyped d g e (erase last) finalResult ∧
          PaperExtendedExecution.InteractionErasure d binder
            (erase ⟨filled, stack⟩) (erase last) := by
  obtain ⟨filled, hfilled, htyped⟩ := context.termSubstitute
    (PaperCoreStep.singleReplacement_typed (identity_typed d g e a profile parameter))
  refine ⟨filled, hfilled, htyped, ?_⟩
  intro last path protocol
  exact PaperExtendedExecution.finite_interaction hd
    ⟨result, htyped, hs⟩ path protocol

/-- A genuine delayed argument enters the existing Force/View exposure rule.
Exposure is kept; this theorem does not erase it or claim its execution. -/
theorem identity_argument_exposure {d g e a argument stack result binder}
    (ha : PaperComputationTyped d g e argument a)
    (hs : StackTyped d g e stack a result)
    (metadata : ViewMetadata) :
    PaperViewExecution.controlStep d binder
      ⟨.force (.view metadata (.delay argument)), identityBody :: stack⟩ =
        some ⟨.expose metadata argument, identityBody :: stack⟩ ∧
    StateTyped d g e
      ⟨.expose metadata argument, identityBody :: stack⟩ result := by
  exact ⟨PaperViewExecution.controlStep_force_view_delay d binder metadata argument _,
    a, .expose ha, .cons (identity_body_typed d g e a) hs⟩

/-- Computation entry binds a thunk; Result performs its designated Force.
This is the actual retained relay body, not the identity's Value-entry body. -/
theorem relay_typed (d : DeclarationTable) (g : GraphEnvironment)
    (e : TypeEnvironment) (a : Ty) (profile : AdapterMetadata)
    (parameter : TermName) :
    PaperValueTyped d g e (relay profile parameter) (.callable a a) :=
  .computationLambda (.force (.variable rfl))

/-- No entry Force/rebind is invented: retained entry substitutes the received
View of C, and the source body then consumes that same carrier. -/
theorem relay_entry_formation {d g e a carrier}
    (hc : PaperValueTyped d g e carrier (.thunk a))
    (profile : AdapterMetadata) (parameter : TermName)
    (receipt : ReceiptMetadata) (owner : OwnerName) :
    entryCode receipt owner (relay profile parameter) carrier =
        some (.force (.view (receipt owner profile) carrier)) ∧
    PaperComputationTyped d g e
        (.force (.view (receipt owner profile) carrier)) a ∧
    EnterTrace receipt
        (.scope owner (.enter owner (relay profile parameter) carrier))
        (.scope owner (.force (.view (receipt owner profile) carrier))) := by
  have hsub : termSubstituteComputation
      (PaperCoreStep.singleReplacement (.view (receipt owner profile) carrier))
      relayBody = some (.force (.view (receipt owner profile) carrier)) := by
    simp [relayBody, termSubstituteComputation, supportedTermComputation,
      supportedTermValue, replaceTermComputation, replaceTermValue,
      PaperCoreStep.singleReplacement]
  refine ⟨hsub, .force (.view hc), ?_⟩
  exact (EnterTrace.tail (.refl _) (.computationLambda hsub)).underScope owner

/-- Construct the represented relay Call itself from its two constructors.
There is no assumed lambda, body, Call typing, or source judgment here.
This is a paper-core derivation, not the missing source derivation T. -/
theorem relay_identity_call_typed
    (d : DeclarationTable) (g : GraphEnvironment) (e : TypeEnvironment)
    (a : Ty) (relayProfile identityProfile : AdapterMetadata)
    (relayParameter identityParameter : TermName) :
    PaperComputationTyped d g e
      (.call (relay relayProfile relayParameter)
        (.delay (.ret (identity identityProfile identityParameter))))
      (.callable a a) :=
  .call (relay_typed d g e (.callable a a) relayProfile relayParameter)
    (.delay (.ret (identity_typed d g e a identityProfile identityParameter)))

/-- In this represented instance, C and W are provably distinct raw values.
This adds no second Call of W. -/
theorem carrier_ne_identity (profile : AdapterMetadata) (parameter : TermName) :
    Value.delay (.ret (identity profile parameter)) ≠ identity profile parameter := by
  intro h
  cases h

end YulangClosure.PaperTypes.SourceIdentityLambda
