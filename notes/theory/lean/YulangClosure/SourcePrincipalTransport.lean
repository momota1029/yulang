import YulangClosure.OriginalSourceEnvironment

/-!
The authentic source side of the outstanding principal-transport occurrence.

The source is BRD/AR/RZ's `top = lambda h. let rec f = lambda x. lambda y.
{first = h x, next = f {a = y}} in f`.  We construct its original raw AST and
run the existing, complete source builder.  In particular, recursive f stays
internal, both Apps retain their complete Call/effect premises, and the second
field stays below the first field's actual Return/rebind telescope.

The canonical source registry supplies h's exact returned-callee endpoint
through every original logical/Shared/runtime frame.  A concrete returned
object update then supplies its actual value/root without selecting a new
provider or source owner.  These are source-side construction facts.  There is
no native ExtrudeFresh-to-source registry map in this module: neither a
qualifying nonempty occurrence nor original principality is asserted.
-/
namespace YulangClosure.SourcePrincipalTransport

open OriginalSource OriginalSourceEnvironment OriginalSourceInterpretation

/-! Names: top=0, h=1, f=2, x=3, y=4. Source occurrence sites are independent. -/

def hName : Source .expression := .name ⟨17, none⟩ 1
def xName : Source .expression := .name ⟨18, none⟩ 3
def fName : Source .expression := .name ⟨21, none⟩ 2
def yName : Source .expression := .name ⟨24, none⟩ 4
def hCall : Source .expression := .app ⟨16, none⟩ hName xName
def argument : Source .expression :=
  .record ⟨22, none⟩ (.recordField 23 2 yName .recordNil)
def recursiveCall : Source .expression := .app ⟨20, none⟩ fName argument
def remainingFields : Source .recordItems :=
  .recordField 19 1 recursiveCall .recordNil
def fields : Source .recordItems := .recordField 15 0 hCall remainingFields
def body : Source .expression := .record ⟨14, none⟩ fields
def fInitializer : Source .expression :=
  .lambda ⟨8, none⟩ ⟨9, 3, none, false⟩ (.wild 10)
    (.lambda ⟨11, none⟩ ⟨12, 4, none, false⟩ (.wild 13) body)
def fBindings : Source .bindings := .binding 7 2 none fInitializer .bindingsNil
def topBody : Source .expression :=
  .block ⟨5, none⟩ (.statementsCons (.letS 6 true fBindings) .statementsNil)
    (.name ⟨25, none⟩ 2)
def topInitializer : Source .expression :=
  .lambda ⟨2, none⟩ ⟨3, 1, none, false⟩ (.wild 4) topBody
def program : Source .expression :=
  .block ⟨0, none⟩
    (.statementsCons (.letS 27 false
      (.binding 1 0 none topInitializer .bindingsNil)) .statementsNil)
    (.name ⟨26, none⟩ 0)

def hBinding : Binding :=
  {name := 1, owner := 3, kind := .formal, entry := some .value, singleUse := true}
def fBinding : Binding :=
  {name := 2, owner := 7, kind := .internal, component := some 6}
def xBinding : Binding :=
  {name := 3, owner := 9, kind := .formal, entry := some .value, singleUse := true}
def yBinding : Binding :=
  {name := 4, owner := 12, kind := .formal, entry := some .value, singleUse := true}
def recursiveContext : Context := [fBinding, hBinding]
def xContext : Context := xBinding :: recursiveContext
def bodyContext : Context := yBinding :: xContext

def hOwner : CallOwner := .application 16 bodyContext 17 18
def recursiveOwner : CallOwner := .application 20 bodyContext 21 22

/-- The complete original builder, including initializer/publication scopes,
constructs precisely these three closures and two original App owners. -/
theorem program_call_owners :
    sourceCallOwners [] program =
      [.closure 2 [] 3 4 5,
       .closure 8 recursiveContext 9 10 11,
       .closure 11 xContext 12 13 14,
       hOwner, recursiveOwner] := by
  simp only [sourceCallOwners, program, topInitializer, topBody, fBindings,
    fInitializer, body, fields, hCall, remainingFields, recursiveCall, argument,
    hName, xName, fName, yName, sourceRules, statementRulesK, statementsRulesK,
    bindingsRulesK, expressionRulesK]
  rfl

/-- The two Names in this actual body have different original binding roles:
h is a captured ordinary formal; recursive f is not a published instance. -/
theorem actual_body_bindings :
    lookupBinding bodyContext 1 = some hBinding ∧
    lookupBinding bodyContext 2 = some fBinding ∧
    fBinding.kind = .internal ∧ fBinding.component = some 6 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The recursive Name is built without a publishedInstance binder or a
separate description choice. Its complete local clauses are still present. -/
theorem recursive_name_is_monomorphic :
    sourceRules bodyContext fName =
      .rule .name 21 bodyContext
        [.atom {(atom .resolvedSameBinding 21 bodyContext) with
          names := [2], binding := some fBinding},
         .atom {(atom .computedFetchOnce 21 bodyContext) with
          names := [2], binding := some fBinding}] .nil := by
  simp only [fName, sourceRules]
  rfl

/-- Full h App, including the original singleton-formal source clause,
whole inert argument, complete Call certificate, and computation check. -/
theorem h_call_complete_rule :
    sourceRules bodyContext hCall =
      .existsE ⟨16, .viewLogic, 0⟩
        (.rule .app 16 bodyContext
          (([AtomKind.descriptorFormation, .wholeArgumentCompatibility,
              .completeCallCertificate, .sourceCallIncidence, .callableImage,
              .roleAndInitialCallOrigin].map
            (fun kind => Premise.atom (atom kind 16 bodyContext [17, 18]))) ++
            [.checking ⟨.value, 16, bodyContext, ⟨17, .returnedValue⟩, ⟨16, .descriptor⟩⟩,
             .checking ⟨.computation, 16, bodyContext,
                ⟨16, .callableImage⟩, ⟨16, .synthesis⟩⟩])
          (.two (sourceRules bodyContext hName) (sourceRules bodyContext xName))) := by
  simp only [hCall, sourceRules]
  rfl

/-- The recursive App retains the same full Call family; it does not receive
the unrelated singleton-formal clause or a fresh polymorphic f instance. -/
theorem recursive_call_complete_rule :
    sourceRules bodyContext recursiveCall =
      .existsE ⟨20, .viewLogic, 0⟩
        (.rule .app 20 bodyContext
          (([AtomKind.descriptorFormation, .wholeArgumentCompatibility,
              .completeCallCertificate, .sourceCallIncidence, .callableImage].map
            (fun kind => Premise.atom (atom kind 20 bodyContext [21, 22]))) ++
            [.checking ⟨.value, 20, bodyContext, ⟨21, .returnedValue⟩, ⟨20, .descriptor⟩⟩,
             .checking ⟨.computation, 20, bodyContext,
                ⟨20, .callableImage⟩, ⟨20, .synthesis⟩⟩])
          (.two (sourceRules bodyContext fName) (sourceRules bodyContext argument))) := by
  simp only [recursiveCall, sourceRules]
  rfl

/-- The recursive field is a suspended suffix below the h Call's actual
Return/rebind. This is the precise source telescope consumed by AR1, not an
assumption that h returns or that both calls have already executed. -/
theorem recursive_field_retains_h_suffix :
    sourceRules bodyContext fields =
      .rule .recordField 15 bodyContext
        [.atom {(atom .visibleFieldUpdate 15 bodyContext [16]) with labels := [0]}]
        (.two (sourceRules bodyContext hCall)
          (.executionE ⟨16, .returnRebind, 0⟩
            (sourceRules bodyContext remainingFields))) := by
  simp only [fields, sourceRules]
  rfl

/-- At the original, nontrivial recursive-body context, the h Name source
derivation is constructed from its actual installed binding. No Name typing,
generated solution, whole App certificate or successful inference is assumed.
The installed tuple keeps the current descriptor/value/provider together. -/
theorem h_name_source_derivation (inputs : Inputs s)
    (readout : RuntimeReadout s View) (original : Kernel (Payload s View))
    (environment : Environment (Payload s View)) (state : Decoded s View)
    (decoded : decode readout environment = some state) (address : Nat)
    (binding : state.assignment.binding 1 = some address)
    (bound : address < inputs.installedCount state.assignment.event)
    (found : inputs.installed state.assignment.event address =
      some (.value (state.assignment.descriptor ⟨17, .finalRoot⟩)
        (state.assignment.value ⟨17, .finalRoot⟩)
        (state.assignment.root ⟨17, .finalRoot⟩))) :
    SourceJudgment (foldedNameKernel inputs readout original 17 1)
      environment bodyContext hName := by
  have lookup : lookupBinding bodyContext 1 = some hBinding := rfl
  simp only [SourceJudgment, hName, sourceRules, lookup]
  apply Judgment.rule
  · intro premise member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    all_goals
      apply Local.atom
      simp only [foldedNameKernel, OriginalSource.atom, valueFormalAtom, hBinding]
      simp only [beq_self_eq_true, Bool.and_self, reduceCtorEq, true_or, or_true,
        and_self, ite_true]
      exact ⟨state, decoded, 1, address, rfl, binding, bound, found⟩
  · exact .nil

/-- All original frame classes, including arbitrary future runtime payloads,
retain both concrete original owners. No frame is selected per type port. -/
theorem source_owners_after_all_frames (readout : RuntimeReadout s View)
    (root : Root s View) (frames : List (Frame (Payload s View))) :
    let state := frames.foldl (decodeFrame readout) (root.withSource [] program).decoded
    state.callOwner ⟨16, .invocation, 0⟩ = some hOwner ∧
    state.callOwner ⟨20, .invocation, 0⟩ = some recursiveOwner := by
  dsimp only
  unfold Decoded.callOwner
  rw [decoded_call_owners]
  change (sourceCallOwners [] program).find? _ = some hOwner ∧
    (sourceCallOwners [] program).find? _ = some recursiveOwner
  rw [program_call_owners]
  exact ⟨rfl, rfl⟩

/-- The source registry supplies returned-callee ports, not App result,
descriptor, the callee's final synthesis port, or a solver row. -/
theorem source_subjects_after_all_frames (readout : RuntimeReadout s View)
    (root : Root s View) (frames : List (Frame (Payload s View))) :
    let state := frames.foldl (decodeFrame readout) (root.withSource [] program).decoded
    state.callSubject ⟨16, .invocation, 0⟩ = ⟨17, .returnedValue⟩ ∧
    state.callSubject ⟨20, .invocation, 0⟩ = ⟨21, .returnedValue⟩ := by
  dsimp only
  obtain ⟨h, recursive⟩ := source_owners_after_all_frames readout root frames
  simp only [Decoded.callSubject, h, recursive, Option.map_some, Option.getD_some]
  exact ⟨rfl, rfl⟩

/-- A concrete original returned-object update. The value and provider root
are inputs from the actual Name Return; no fresh value/provider is chosen.
This data constructor alone does not prove admission of that Return. -/
def hReturn (value : s.Value) (provider : s.Root) (observation : s.Observation)
    (after : Current s) : Outcome s :=
  {observation := observation, result := some (.value value provider), after := after,
   endpoints := [(⟨17, .returnedValue⟩, .value value provider)], bindings := []}

/-- Given the actual Name Return data, the existing decoder constructs the
exact h receiver/value/provider in the current frame. The complete preceding
frame list is arbitrary, and the runtime readout retains its own event data.
No native copy occurrence is assigned this receiver by this theorem. -/
theorem h_return_supplies_current_receiver (readout : RuntimeReadout s View)
    (root : Root s View) (frames : List (Frame (Payload s View)))
    (returnBinder : Binder)
    (value : s.Value) (provider : s.Root) (observation : s.Observation)
    (after : Current s) :
    let before := frames.foldl (decodeFrame readout) (root.withSource [] program).decoded
    let next := before.runtime readout returnBinder
      (.returnRebind (hReturn value provider observation after))
    next.callOwner ⟨16, .invocation, 0⟩ = some hOwner ∧
    next.assignment.value (next.callSubject ⟨16, .invocation, 0⟩) = value ∧
    next.assignment.root (next.callSubject ⟨16, .invocation, 0⟩) = provider ∧
    next.assignment.event.current = after.configuration ∧
    next.assignment.event.history = after.history := by
  dsimp only
  have owners := (source_owners_after_all_frames readout root frames).1
  have nextOwner :
      ((frames.foldl (decodeFrame readout) (root.withSource [] program).decoded).runtime
        readout returnBinder
        (.returnRebind (hReturn value provider observation after))).callOwner
          ⟨16, .invocation, 0⟩ = some hOwner := by
    unfold Decoded.callOwner
    rw [runtime_preserves_call_owners]
    exact owners
  have nextSubject :
      ((frames.foldl (decodeFrame readout) (root.withSource [] program).decoded).runtime
        readout returnBinder
        (.returnRebind (hReturn value provider observation after))).callSubject
          ⟨16, .invocation, 0⟩ = ⟨17, .returnedValue⟩ := by
    simp only [Decoded.callSubject, nextOwner, Option.map_some, Option.getD_some]
    rfl
  refine ⟨nextOwner, ?_, ?_, rfl, rfl⟩
  all_goals
    rw [nextSubject]
    simp only [Decoded.runtime, Runtime.endpoints, hReturn,
      List.foldl_cons, List.foldl_nil, Decoded.object, put]
    simp

end YulangClosure.SourcePrincipalTransport
