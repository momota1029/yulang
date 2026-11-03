import YulangClosure.OriginalTickDeclaredResponseR321

/-!
R332: the full FORMAL response domain of the actual source tick declaration.
The declaration is authenticated by R321's original source identity and signature
translation. All closed typed responses are retained, including arbitrarily many
ordered view wrappers. The exact domain is then applied to the existing captured
continuation consumer; no completed EI clause or child contribution is assumed.

This does not identify the separate TypedCall syntax with the opaque original
Inputs. Native/current-world response extraction, original primitive resolution,
whole-tuple actions, all EI phases and independent Union arms remain open.
-/
namespace YulangClosure.OriginalSourceAuthenticatedEIR332

open OriginalTickDeclaredResponseR321

/-- The original response keeps its complete ordered view chain. This is a
normal-form presentation, not an erasure of evidence or a new response type. -/
def response (integer : Int) : List TypedCall.ViewOccurrence → TypedCall.Value
  | [] => .original (.int integer)
  | view :: rest => .view (response integer rest) view

def readResponse : TypedCall.Value → Option (Int × List TypedCall.ViewOccurrence)
  | .original (.int integer) => some (integer, [])
  | .view value view => (readResponse value).map fun pair => (pair.1, view :: pair.2)
  | _ => none

theorem read_response (integer : Int) (views : List TypedCall.ViewOccurrence) :
    readResponse (response integer views) = some (integer, views) := by
  induction views with
  | nil => rfl
  | cons view rest ih => simp only [response, readResponse, ih, Option.map_some]

theorem response_injective {first second : Int}
    {left right : List TypedCall.ViewOccurrence}
    (same : response first left = response second right) : first = second ∧ left = right := by
  have h := congrArg readResponse same
  rw [read_response, read_response] at h
  exact Prod.mk.inj (Option.some.inj h)

theorem response_typed (integer : Int) (views : List TypedCall.ViewOccurrence) :
    TypedCall.ValueTyped Original.emptyContext (response integer views) tickOperation.responseType := by
  change TypedCall.ValueTyped _ _ (.base .int)
  induction views with
  | nil => exact .original .int
  | cons view rest ih => exact .view ih

/-- Inversion of every original typing constructor, rather than a claim that
the responses emitted by a successful native example exhaust the domain. -/
theorem response_complete (value : TypedCall.Value)
    (typed : TypedCall.ValueTyped Original.emptyContext value tickOperation.responseType) :
    ∃ integer views, value = response integer views := by
  change TypedCall.ValueTyped _ _ (.base .int) at typed
  cases value with
  | var index => cases typed with | var found => cases found
  | original value =>
    cases typed with
    | original original =>
      cases original with
      | var found => cases found
      | int => exact ⟨_, [], rfl⟩
  | delay body => cases typed
  | view value view =>
    cases typed with
    | view child =>
      obtain ⟨integer, views, same⟩ := response_complete value child
      exact ⟨integer, view :: views, congrArg (fun v => TypedCall.Value.view v view) same⟩

theorem response_domain_exact (value : TypedCall.Value) :
    TypedCall.ValueTyped Original.emptyContext value tickOperation.responseType ↔
      ∃ integer views, value = response integer views := by
  constructor
  · exact response_complete value
  · rintro ⟨integer, views, rfl⟩
    exact response_typed integer views

/-- Any property on the full original typed response domain can be checked on
this exact presentation. No current-world or provider acceptance restriction
appears in the domain. View duplicates and order are preserved. -/
theorem all_responses_iff (P : TypedCall.Value → Prop) :
    (∀ value, TypedCall.ValueTyped Original.emptyContext value tickOperation.responseType → P value) ↔
      ∀ integer views, P (response integer views) := by
  constructor
  · intro all integer views
    exact all _ (response_typed integer views)
  · intro all value typed
    obtain ⟨integer, views, rfl⟩ := response_complete value typed
    exact all integer views

/-- The exact actual source declaration selects this whole domain. Source
identity, operation numbering and signature are outputs of R321, not hypotheses
that identify an arbitrary desired operation with tick. -/
theorem source_response_domain (value : TypedCall.Value) :
    PrimitiveOperation.request tickKeys (declaration tick) = some tickOperation ∧
    (TypedCall.ValueTyped Original.emptyContext value tickOperation.responseType ↔
      ∃ integer views, value = response integer views) :=
  ⟨tick_declaration_interpretation.2.2.2.1, response_domain_exact value⟩

/-- Apply ALL responses from the actual declaration to the captured continuation
at its exact completed formal request boundary. The supplied formal prefix is
still independent: no native trace, opaque original Inputs, result provider or
resumed current-world relation is manufactured from syntax typing. -/
theorem selected_request_all_responses
    {W : Type} {sig : Control.Signature} {md : Control.Metadata W}
    {term : TypedCall.CallTerm} {world : W} {suffix : List Control.Frame}
    {result : Control.Ty} {n m : Nat} {s t : Control.CallState W}
    {payload : TypedCall.Value} {k : TypedCall.Comp}
    {observed : List TypedCall.ViewOccurrence}
    (hsuffix : Control.FramesTyped sig suffix (.original term.resultType) result)
    (hp : Prefix (Control.CallControlStep md) n (Control.CallState.initial term world suffix) s)
    (hhead : s.head = .requesting tickOperation payload k observed)
    (hpost : Prefix (Control.CallControlStep md) m s t)
    (hcomplete : ∃ op' payload' k', t.head = .requested op' payload' k') :
    PrimitiveOperation.request tickKeys (declaration tick) = some tickOperation ∧
    m = s.frames.length + 1 ∧
    t = s.requestBoundary md (s.frames.length + 1) ∧
    t.head = .requested tickOperation payload (Control.CallState.captureFrames s.frames k) ∧
    Control.CallStateTyped sig t result ∧ t.literalSuffix = suffix ∧
    ∀ value, TypedCall.ValueTyped Original.emptyContext value tickOperation.responseType →
      TypedCall.CompTyped Original.emptyContext
        (Control.plugResponse (Control.CallState.captureFrames s.frames k) value) term.resultType ∧
      Control.plugResponse (Control.CallState.captureFrames s.frames k) value =
        TypedCall.plugFrames s.frames (Control.plugResponse k value) ∧
      TypedCall.CompTyped Original.emptyContext
        (TypedCall.plugFrames s.frames (Control.plugResponse k value)) term.resultType := by
  have boundary := Control.actual_call_request_completed_response hsuffix hp hhead hpost hcomplete
    (response_typed 0 [])
  refine ⟨tick_declaration_interpretation.2.2.2.1, boundary.1, boundary.2.1,
    boundary.2.2.1, boundary.2.2.2.1, boundary.2.2.2.2.1, ?_⟩
  intro value typed
  obtain ⟨integer, views, rfl⟩ := response_complete value typed
  have checked := Control.actual_call_request_completed_response hsuffix hp hhead hpost hcomplete
    (response_typed integer views)
  exact ⟨checked.2.2.2.2.2.1, Control.plugResponse_captureFrames _ _ _, checked.2.2.2.2.2.2⟩

end YulangClosure.OriginalSourceAuthenticatedEIR332
