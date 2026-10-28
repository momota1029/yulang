import YulangClosure.PaperResumeExecution

/-!
One concrete partial execution machine for ordinary let control, R35 core
redexes, tuple split, perform/request bind, empty-owner raw resume, and explicit
Fail propagation. The operational manuscript's ordinary transitions (:303–359),
raw resume (:458–466), and frame preservation (:1012–1026, :1100–1110) are the
source interfaces. The corrected V5(3,6,8) preserves the failure tag and saved
continuation rather than restoring a saved world.

The machine has no dynamic world or graph mutation. Nonempty owner continuations
remain unsupported: their corrected current-world/L-Enter behavior is a separate
obligation. `none` means no implemented transition, not proved termination,
progress, or safety. The existing raw syntax has no `Bad` constructor, so none
of these results is a Bad-exclusion theorem or whole-language safety theorem.

The existing principal control remains an explicit extension seam; in particular
administrative type-application normalization can be attached by its owning lane
without changing the trace invariants or putting preservation into the step.
-/
namespace YulangClosure.PaperTypes.PaperCombinedExecution

open PaperCoreControl

/-- Empty-owner resume and one ordinary let frame of explicit failure unwinding.
This function consults syntax and the accepted partial substitution only. -/
def extraStep (s : State) : Option State :=
  match PaperResumeExecution.resumeStep s.head with
  | some next => some ⟨next, s.stack⟩
  | none => match s.head, s.stack with
    | .fail reason, _ :: rest => some ⟨.fail reason, rest⟩
    | _, _ => none

/-- Every successful old control transition retains its exact result. -/
def controlStep (d : DeclarationTable) (binder : TermName) (s : State) : Option State :=
  match PaperPerformLetExecution.controlStep d binder s with
  | some next => some next
  | none => extraStep s

inductive ControlStepEvidence (d : DeclarationTable) (binder : TermName) :
    State → State → Prop where
  | existing {s next} : PaperPerformLetExecution.ControlStepEvidence d binder s next →
      ControlStepEvidence d binder s next
  | resume {head next stack} : PaperResumeExecution.resumeStep head = some next →
      ControlStepEvidence d binder ⟨head, stack⟩ ⟨next, stack⟩
  | fail {reason body rest} :
      ControlStepEvidence d binder ⟨.fail reason, body :: rest⟩ ⟨.fail reason, rest⟩

theorem controlStep_extends {d binder s next}
    (hs : PaperPerformLetExecution.controlStep d binder s = some next) :
    controlStep d binder s = some next := by
  simp only [controlStep, hs]

/-- Success supplies an actual existing, raw-resume, or failure transition. -/
theorem controlStep_evidence {d binder s next}
    (hs : controlStep d binder s = some next) : ControlStepEvidence d binder s next := by
  cases ho : PaperPerformLetExecution.controlStep d binder s with
  | some old =>
      have he : old = next := Option.some.inj (by simpa only [controlStep, ho] using hs)
      cases he
      exact .existing (PaperPerformLetExecution.controlStep_evidence ho)
  | none =>
      have hx : extraStep s = some next := by simpa only [controlStep, ho] using hs
      rcases s with ⟨head, stack⟩
      cases hr : PaperResumeExecution.resumeStep head with
      | some c =>
          have he : (⟨c, stack⟩ : State) = next := Option.some.inj (by
            simpa only [extraStep, hr] using hx)
          cases he
          exact .resume hr
      | none =>
          cases head with
          | fail reason =>
              cases stack with
              | nil => simp [extraStep, hr] at hx
              | cons body rest =>
                  have he : (⟨.fail reason, rest⟩ : State) = next := Option.some.inj (by
                    simpa only [extraStep, hr] using hx)
                  cases he
                  exact .fail
          | _ => simp [extraStep, hr] at hx

/-- The partial raw resume function retains exactly its original typing rule. -/
theorem resume_preservation {d g e head next result}
    (ht : PaperComputationTyped d g e head result)
    (hs : PaperResumeExecution.resumeStep head = some next) :
    PaperComputationTyped d g e next result := by
  cases head with
  | resume continuation response =>
      cases continuation with
      | continuation owners binder body =>
          cases owners with
          | nil => exact PaperResumeExecution.typed_resume_preservation ht hs
          | cons owner rest => simp [PaperResumeExecution.resumeStep] at hs
      | _ => simp [PaperResumeExecution.resumeStep] at hs
  | _ => simp [PaperResumeExecution.resumeStep] at hs

/-- The literal same D, graph environment, lexical environment, and final result. -/
theorem evidence_preservation {d g e s next result binder}
    (ht : StateTyped d g e s result) (hs : ControlStepEvidence d binder s next) :
    StateTyped d g e next result := by
  cases hs with
  | existing ho => exact PaperPerformLetExecution.evidence_preservation ht ho
  | resume hr =>
      obtain ⟨a, hh, hf⟩ := ht
      exact ⟨a, resume_preservation hh hr, hf⟩
  | fail =>
      obtain ⟨a, hh, hf⟩ := ht
      cases hf with
      | cons hb rest => exact ⟨_, .fail, rest⟩

theorem preservation {d g e s next result binder}
    (ht : StateTyped d g e s result) (hs : controlStep d binder s = some next) :
    StateTyped d g e next result := evidence_preservation ht (controlStep_evidence hs)

/-- Successful raw resume reduces at the active hole under any ordinary let stack. -/
theorem controlStep_resume (d binder continuation response stack) :
    controlStep d binder ⟨.resume continuation response, stack⟩ =
      (PaperResumeExecution.resumeStep (.resume continuation response)).map
        (fun next => ⟨next, stack⟩) := by
  simp [controlStep, PaperPerformLetExecution.controlStep,
    PaperTupleSplitExecution.controlStep, PaperCoreControl.controlStep,
    PaperCoreStep.step, PaperTupleSplitExecution.splitStep,
    PaperPerformLetExecution.extraStep, PaperPerformLetExecution.performStep,
    PaperPerformLetExecution.requestBind, extraStep]
  cases stack <;> cases PaperResumeExecution.resumeStep (.resume continuation response) <;> rfl

theorem controlStep_fail_cons (d binder reason body rest) :
    controlStep d binder ⟨.fail reason, body :: rest⟩ = some ⟨.fail reason, rest⟩ := by
  simp [controlStep, PaperPerformLetExecution.controlStep,
    PaperTupleSplitExecution.controlStep, PaperCoreControl.controlStep,
    PaperCoreStep.step, PaperTupleSplitExecution.splitStep,
    PaperPerformLetExecution.extraStep, PaperPerformLetExecution.performStep,
    PaperPerformLetExecution.requestBind, extraStep, PaperResumeExecution.resumeStep]

/-- Explicit failure has no internal successor after all ordinary frames unwind. -/
theorem controlStep_fail_nil (d binder reason) :
    controlStep d binder ⟨.fail reason, []⟩ = none := by
  simp [controlStep, PaperPerformLetExecution.controlStep,
    PaperTupleSplitExecution.controlStep, PaperCoreControl.controlStep,
    PaperCoreStep.step, PaperTupleSplitExecution.splitStep,
    PaperPerformLetExecution.extraStep, PaperPerformLetExecution.performStep,
    extraStep, PaperResumeExecution.resumeStep]

/-- Source-shaped reductions; only the ordinary let context is closed here. -/
inductive ComputationStep (d : DeclarationTable) (binder : TermName) :
    Computation → Computation → Prop where
  | existing {head next} : PaperPerformLetExecution.PaperLetContextStep d binder head next →
      ComputationStep d binder head next
  | resume {head next} : PaperResumeExecution.resumeStep head = some next →
      ComputationStep d binder head next
  | fail {reason body} : ComputationStep d binder (.letE (.fail reason) body) (.fail reason)
  | underLet {head next body} : ComputationStep d binder head next →
      ComputationStep d binder (.letE head body) (.letE next body)

theorem plug_step {d binder head next} (hs : ComputationStep d binder head next)
    (stack : List Computation) :
    ComputationStep d binder (plug stack head) (plug stack next) := by
  induction stack generalizing head next with
  | nil => exact hs
  | cons body rest ih => exact ih (.underLet hs)

theorem evidence_erasure {d binder s next} (hs : ControlStepEvidence d binder s next) :
    erase s = erase next ∨ ComputationStep d binder (erase s) (erase next) := by
  cases hs with
  | existing ho =>
      cases PaperPerformLetExecution.evidence_erasure ho with
      | inl he => exact .inl he
      | inr hp => exact .inr (.existing hp)
  | @resume head next stack hr => exact .inr (plug_step (.resume hr) stack)
  | @fail reason body rest => exact .inr (plug_step (.fail (reason := reason) (body := body)) rest)

theorem erasure {d binder s next} (hs : controlStep d binder s = some next) :
    erase s = erase next ∨ ComputationStep d binder (erase s) (erase next) :=
  evidence_erasure (controlStep_evidence hs)

/-- Arbitrary finite prefixes of this actual executable step. There is no phase
restriction on split, perform, resume, or any existing core step. -/
inductive Trace (d : DeclarationTable) (binder : TermName) : State → State → Prop where
  | refl (s) : Trace d binder s s
  | tail {s middle last} : Trace d binder s middle →
      controlStep d binder middle = some last → Trace d binder s last

theorem trace_trans {d binder first middle last}
    (hf : Trace d binder first middle) (hl : Trace d binder middle last) :
    Trace d binder first last := by
  induction hl with
  | refl => exact hf
  | tail path hs ih => exact .tail ih hs

theorem existing_trace {d binder first last}
    (path : PaperPerformLetExecution.Trace d binder first last) : Trace d binder first last := by
  induction path with
  | refl => exact .refl _
  | tail path hs ih => exact .tail ih (controlStep_extends hs)

theorem trace_preservation {d g e first last result binder}
    (ht : StateTyped d g e first result) (path : Trace d binder first last) :
    StateTyped d g e last result := by
  induction path with
  | refl => exact ht
  | tail path hs ih => exact preservation ih hs

inductive ErasureTrace (d : DeclarationTable) (binder : TermName) :
    Computation → Computation → Prop where
  | refl (c) : ErasureTrace d binder c c
  | tail {first middle last} : ErasureTrace d binder first middle →
      (middle = last ∨ ComputationStep d binder middle last) →
      ErasureTrace d binder first last

theorem trace_erasure {d binder first last} (path : Trace d binder first last) :
    ErasureTrace d binder (erase first) (erase last) := by
  induction path with
  | refl => exact .refl _
  | tail path hs ih => exact .tail ih (erasure hs)

/-- Joint application to the original fixed-state finite-prefix preservation
interface. This states preservation and erasure, without assuming LocalLaws. -/
theorem finite_prefix {d g e first last result binder}
    (ht : StateTyped d g e first result) (path : Trace d binder first last) :
    StateTyped d g e last result ∧
      PaperComputationTyped d g e (erase last) result ∧
      ErasureTrace d binder (erase first) (erase last) := by
  have hl := trace_preservation ht path
  exact ⟨hl, erase_typed hl, trace_erasure path⟩

/-- Both arbitrary internal prefixes reuse literally the same saved continuation
and derivation. Neither branch consumes or alters the saved body. -/
theorem shared_continuation_prefixes
    {d g e responseBinder saved q a first second stack result controlBinder firstLast secondLast}
    (hk : PaperContinuationTyped d g e (.continuation [] responseBinder saved) q a)
    (hv₁ : PaperValueTyped d g e first q) (hv₂ : PaperValueTyped d g e second q)
    (hf : StackTyped d g e stack a result)
    (path₁ : Trace d controlBinder
      ⟨.resume (.continuation [] responseBinder saved) first, stack⟩ firstLast)
    (path₂ : Trace d controlBinder
      ⟨.resume (.continuation [] responseBinder saved) second, stack⟩ secondLast) :
    StateTyped d g e firstLast result ∧ StateTyped d g e secondLast result ∧
      ErasureTrace d controlBinder
        (erase ⟨.resume (.continuation [] responseBinder saved) first, stack⟩) (erase firstLast) ∧
      ErasureTrace d controlBinder
        (erase ⟨.resume (.continuation [] responseBinder saved) second, stack⟩) (erase secondLast) ∧
      PaperContinuationTyped d g e (.continuation [] responseBinder saved) q a := by
  have h₁ := finite_prefix ⟨a, PaperResumeExecution.resume_typed hk hv₁, hf⟩ path₁
  have h₂ := finite_prefix ⟨a, PaperResumeExecution.resume_typed hk hv₂, hf⟩ path₂
  exact ⟨h₁.1, h₂.1, h₁.2.2, h₂.2.2, hk⟩

/-- Failure unwinds any finite ordinary stack and retains its literal reason. -/
theorem fail_unwind (d binder reason stack) :
    Trace d binder ⟨.fail reason, stack⟩ ⟨.fail reason, []⟩ := by
  induction stack with
  | nil => exact .refl _
  | cons body rest ih =>
      exact trace_trans (.tail (.refl _) (controlStep_fail_cons d binder reason body rest)) ih

theorem nonempty_resume_rejected (d controlBinder owner owners binder body response stack) :
    controlStep d controlBinder
      ⟨.resume (.continuation (owner :: owners) binder body) response, stack⟩ = none := by
  rw [controlStep_resume]
  rfl

theorem nonempty_request_rejected (d controlBinder op payload owner owners binder saved stack) :
    controlStep d controlBinder
      ⟨.request op payload (.continuation (owner :: owners) binder saved), stack⟩ = none := by
  cases stack <;>
    simp [controlStep, PaperPerformLetExecution.controlStep,
      PaperTupleSplitExecution.controlStep, PaperCoreControl.controlStep,
      PaperCoreStep.step, PaperTupleSplitExecution.splitStep,
      PaperPerformLetExecution.extraStep, PaperPerformLetExecution.performStep,
      PaperPerformLetExecution.requestBind, extraStep, PaperResumeExecution.resumeStep]

/-- The environment supplies a response only at an exposed request. This is a
raw syntactic event; response typing is a separate protocol condition below. -/
def responseStep (response : Value) : State → Option State
  | ⟨.request _ _ (.continuation [] binder saved), []⟩ =>
      some ⟨.resume (.continuation [] binder saved) response, []⟩
  | _ => none

inductive Event (d : DeclarationTable) (binder : TermName) : State → State → Type where
  | internal {first last} : controlStep d binder first = some last → Event d binder first last
  | response (op payload responseBinder saved response) :
      Event d binder
        ⟨.request op payload (.continuation [] responseBinder saved), []⟩
        ⟨.resume (.continuation [] responseBinder saved) response, []⟩

/-- A response event is exactly the separate raw `responseStep` operation. -/
theorem response_event_eq (op payload responseBinder saved response) :
    responseStep response ⟨.request op payload (.continuation [] responseBinder saved), []⟩ =
      some ⟨.resume (.continuation [] responseBinder saved) response, []⟩ := rfl

/-- Only foreign response values carry a protocol premise. Internal events
require no typing, preservation, progress, or LocalLaws certificate. -/
def EventAdmissible {d binder first last} (g : GraphEnvironment) (e : TypeEnvironment) :
    Event d binder first last → Prop
  | .internal _ => True
  | .response op _ _ _ response => PaperValueTyped d g e response op.responseType

theorem event_preservation {d binder g e first last result}
    (ht : StateTyped d g e first result) (event : Event d binder first last)
    (protocol : EventAdmissible g e event) : StateTyped d g e last result := by
  cases event with
  | internal hs => exact preservation ht hs
  | response op payload responseBinder saved response =>
      have hh := PaperPerformLetExecution.external_request ht
      have hk := PaperResumeExecution.request_continuation_typed hh
      exact ⟨result, PaperResumeExecution.resume_typed hk protocol, .nil⟩

/-- Finite raw execution with arbitrary internal/response interleavings. The
execution relation itself does not mention a typing judgment. -/
inductive InteractionTrace (d : DeclarationTable) (binder : TermName) :
    State → State → Type where
  | refl (s) : InteractionTrace d binder s s
  | tail {first middle last} : InteractionTrace d binder first middle →
      Event d binder middle last → InteractionTrace d binder first last

/-- The explicit external contract: each supplied response has that request's
actual operation-instance response type in the same shared contexts. -/
def ProtocolTyped {d binder first last} (g : GraphEnvironment) (e : TypeEnvironment) :
    InteractionTrace d binder first last → Prop
  | .refl _ => True
  | .tail path event => ProtocolTyped g e path ∧ EventAdmissible g e event

theorem interaction_preservation {d binder g e first last result}
    (ht : StateTyped d g e first result) (path : InteractionTrace d binder first last)
    (protocol : ProtocolTyped g e path) : StateTyped d g e last result := by
  induction path with
  | refl => exact ht
  | tail path event ih => exact event_preservation (ih protocol.1) event protocol.2

inductive ErasedEvent (d : DeclarationTable) (binder : TermName) :
    Computation → Computation → Prop where
  | internal {first last} : (first = last ∨ ComputationStep d binder first last) →
      ErasedEvent d binder first last
  | response (op payload responseBinder saved response) :
      ErasedEvent d binder (.request op payload (.continuation [] responseBinder saved))
        (.resume (.continuation [] responseBinder saved) response)

inductive InteractionErasure (d : DeclarationTable) (binder : TermName) :
    Computation → Computation → Prop where
  | refl (c) : InteractionErasure d binder c c
  | tail {first middle last} : InteractionErasure d binder first middle →
      ErasedEvent d binder middle last → InteractionErasure d binder first last

theorem interaction_erasure {d binder first last}
    (path : InteractionTrace d binder first last) :
    InteractionErasure d binder (erase first) (erase last) := by
  induction path with
  | refl => exact .refl _
  | tail path event ih =>
      cases event with
      | internal hs => exact .tail ih (.internal (erasure hs))
      | response op payload responseBinder saved response =>
          exact .tail ih (.response op payload responseBinder saved response)

/-- Arbitrarily many performed requests, responses, raw resumes, tuple splits,
and other implemented internal steps share one D/graph/Γ/result throughout.
This is a finite-prefix preservation statement, not a progress theorem. -/
theorem finite_interaction {d binder g e first last result}
    (ht : StateTyped d g e first result) (path : InteractionTrace d binder first last)
    (protocol : ProtocolTyped g e path) :
    StateTyped d g e last result ∧
      PaperComputationTyped d g e (erase last) result ∧
      InteractionErasure d binder (erase first) (erase last) := by
  have hl := interaction_preservation ht path protocol
  exact ⟨hl, erase_typed hl, interaction_erasure path⟩

/-- A finite internal trace is admitted with no external-response obligation. -/
theorem trace_interaction {d binder g e first last} (path : Trace d binder first last) :
    ∃ execution : InteractionTrace d binder first last, ProtocolTyped g e execution := by
  induction path with
  | refl => exact ⟨.refl _, True.intro⟩
  | tail path hs ih =>
      obtain ⟨execution, protocol⟩ := ih
      exact ⟨.tail execution (.internal hs), protocol, True.intro⟩

/-- Nonempty saved owners are also rejected at the external response boundary. -/
theorem nonempty_response_rejected (op payload owner owners binder saved response) :
    responseStep response
      ⟨.request op payload (.continuation (owner :: owners) binder saved), []⟩ = none := rfl

def InteractionTrace.append {d binder first middle last}
    (left : InteractionTrace d binder first middle) :
    InteractionTrace d binder middle last → InteractionTrace d binder first last
  | .refl _ => left
  | .tail path event => .tail (left.append path) event

theorem protocol_append {d binder g e first middle last}
    (left : InteractionTrace d binder first middle)
    (right : InteractionTrace d binder middle last)
    (hl : ProtocolTyped g e left) (hr : ProtocolTyped g e right) :
    ProtocolTyped g e (left.append right) := by
  induction right with
  | refl => exact hl
  | tail path event ih => exact ⟨ih hr.1, hr.2⟩

def Event.resumeCount {d binder first last} : Event d binder first last → Nat
  | .internal _ => match first.head with
    | .resume _ _ => 1
    | _ => 0
  | .response _ _ _ _ _ => 0

def InteractionTrace.responseCount {d binder first last} :
    InteractionTrace d binder first last → Nat
  | .refl _ => 0
  | .tail path (.internal _) => path.responseCount
  | .tail path (.response _ _ _ _ _) => path.responseCount + 1

def InteractionTrace.resumeCount {d binder first last} :
    InteractionTrace d binder first last → Nat
  | .refl _ => 0
  | .tail path event => path.resumeCount + event.resumeCount

theorem responseCount_append {d binder first middle last}
    (left : InteractionTrace d binder first middle)
    (right : InteractionTrace d binder middle last) :
    (left.append right).responseCount = left.responseCount + right.responseCount := by
  induction right with
  | refl => simp [InteractionTrace.append, InteractionTrace.responseCount]
  | tail path event ih =>
      cases event <;>
        simp [InteractionTrace.append, InteractionTrace.responseCount, ih, Nat.add_assoc]

theorem resumeCount_append {d binder first middle last}
    (left : InteractionTrace d binder first middle)
    (right : InteractionTrace d binder middle last) :
    (left.append right).resumeCount = left.resumeCount + right.resumeCount := by
  induction right with
  | refl => simp [InteractionTrace.append, InteractionTrace.resumeCount]
  | tail path event ih =>
      simp [InteractionTrace.append, InteractionTrace.resumeCount, ih, Nat.add_assoc]

/-! A concrete unbounded family of finite discriminators. Every round performs,
captures a real pending let body, accepts an external unit response, resumes that
saved body with the combined step, and splits before the next perform. -/

def roundDeclaration : OperationDeclaration := ⟨7, 0, .base .unit, .base .unit⟩

def roundTable : DeclarationTable := ⟨[roundDeclaration], [], [], [], 0⟩

def roundProgram : Nat → Computation
  | 0 => .ret (.literal .unit)
  | n + 1 => .letE (.perform 7 [] (.literal .unit))
      (.split (.tuple []) [] (roundProgram n))

theorem round_resolved : OperationDeclarationResolved roundTable.operations 7 roundDeclaration := by
  refine ⟨by simp [roundTable], rfl, ?_⟩
  intro other hm hi
  simpa only [roundTable, List.mem_cons, List.not_mem_nil, or_false] using hm

theorem roundProgram_typed (n : Nat) (g : GraphEnvironment) (e : TypeEnvironment) :
    PaperComputationTyped roundTable g e (roundProgram n) (.base .unit) := by
  induction n generalizing e with
  | zero => exact .ret .literal
  | succ n ih =>
      exact .letE (.perform round_resolved rfl .literal)
        (.split (types := []) rfl (.tuple .nil) (ih _))

theorem roundProgram_supported (n : Nat) : supportedTermComputation (roundProgram n) = true := by
  induction n with
  | zero => simp [roundProgram, supportedTermComputation, supportedTermValue]
  | succ n ih => simp [roundProgram, supportedTermComputation, supportedTermValue, ih]

theorem roundProgram_replace (n : Nat) (rho : Nat → Value) :
    replaceTermComputation rho (roundProgram n) = roundProgram n := by
  induction n generalizing rho with
  | zero => simp [roundProgram, replaceTermComputation, replaceTermValue]
  | succ n ih => simp [roundProgram, replaceTermComputation, replaceTermValue, ih]

/-- This is a complete concrete round of the actual machine, including one
foreign event. No future internal transition is a theorem hypothesis. -/
theorem example_round (n : Nat) (g : GraphEnvironment) (e : TypeEnvironment) (binder : TermName) :
    ∃ path : InteractionTrace roundTable binder
        ⟨roundProgram (n + 1), []⟩ ⟨roundProgram n, []⟩,
      ProtocolTyped g e path ∧ path.responseCount = 1 ∧ path.resumeCount = 1 := by
  let body : Computation := .split (.tuple []) [] (roundProgram n)
  let op := roundDeclaration.instantiate []
  let initial : Computation := .perform 7 [] (.literal .unit)
  let request : Computation := .request op (.literal .unit)
    (.continuation [] binder (.ret (.variable 0)))
  let saved : Computation := .letE (.ret (.variable 0)) body
  let captured : Computation := .request op (.literal .unit) (.continuation [] binder saved)
  let resumed : Computation := .resume (.continuation [] binder saved) (.literal .unit)
  let returned : Computation := .letE (.ret (.literal .unit)) body
  have hp : controlStep roundTable binder ⟨roundProgram (n + 1), []⟩ =
      some ⟨initial, [body]⟩ := rfl
  have hperform : controlStep roundTable binder ⟨initial, [body]⟩ =
      some ⟨request, [body]⟩ := by
    apply controlStep_extends
    simp [PaperPerformLetExecution.controlStep, PaperTupleSplitExecution.controlStep,
      PaperCoreControl.controlStep, PaperCoreStep.step, PaperTupleSplitExecution.splitStep,
      PaperPerformLetExecution.extraStep, initial,
      PaperPerformLetExecution.performStep_eq round_resolved (show [].length = roundDeclaration.typeArity from rfl),
      request, op]
  have hb : controlStep roundTable binder ⟨request, [body]⟩ = some ⟨captured, []⟩ := by
    apply controlStep_extends
    rw [PaperPerformLetExecution.controlStep_request_cons]
    simp [PaperPerformLetExecution.requestBind, captured, saved, body,
      termSubstituteComputation, supportedTermComputation, supportedTermValue,
      roundProgram_supported, replaceTermComputation, replaceTermValue, roundProgram_replace]
  have hr : controlStep roundTable binder ⟨resumed, []⟩ = some ⟨returned, []⟩ := by
    rw [controlStep_resume]
    simp [PaperResumeExecution.resumeStep, saved, returned, body,
      termSubstituteComputation, supportedTermComputation, supportedTermValue,
      roundProgram_supported, replaceTermComputation, replaceTermValue,
      PaperCoreStep.singleReplacement, roundProgram_replace]
  have hp' : controlStep roundTable binder ⟨returned, []⟩ =
      some ⟨.ret (.literal .unit), [body]⟩ := rfl
  have hpop : controlStep roundTable binder ⟨.ret (.literal .unit), [body]⟩ =
      some ⟨body, []⟩ := by
    apply controlStep_extends
    apply PaperPerformLetExecution.controlStep_extends
    apply PaperTupleSplitExecution.controlStep_extends
    simp [PaperCoreControl.controlStep, body, termSubstituteComputation,
      supportedTermComputation, supportedTermValue, roundProgram_supported,
      replaceTermComputation, replaceTermValue, roundProgram_replace]
  have hsplit : controlStep roundTable binder ⟨body, []⟩ = some ⟨roundProgram n, []⟩ := by
    apply controlStep_extends
    apply PaperPerformLetExecution.controlStep_extends
    simp [PaperTupleSplitExecution.controlStep, PaperCoreControl.controlStep,
      PaperCoreStep.step, PaperTupleSplitExecution.splitStep, body,
      termSubstituteComputation, roundProgram_supported, roundProgram_replace]
  let path : InteractionTrace roundTable binder
      ⟨roundProgram (n + 1), []⟩ ⟨roundProgram n, []⟩ :=
    .tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail (.refl _)
      (.internal hp)) (.internal hperform)) (.internal hb))
      (.response op (.literal .unit) binder saved (.literal .unit)))
      (.internal hr)) (.internal hp')) (.internal hpop)) (.internal hsplit)
  refine ⟨path, ?_, ?_, ?_⟩
  · simp only [path, ProtocolTyped, EventAdmissible, and_true, true_and]
    exact .literal
  · rfl
  · rfl

/-- For every n, one concrete execution contains n complete perform/response/
resume rounds, with a tuple split after every resume and before each later perform.
The arbitrary-prefix theorem above applies to every prefix of these executions. -/
theorem example_arbitrarily_many_rounds (n : Nat) (g : GraphEnvironment)
    (e : TypeEnvironment) (binder : TermName) :
    ∃ path : InteractionTrace roundTable binder
        ⟨roundProgram n, []⟩ ⟨.ret (.literal .unit), []⟩,
      ProtocolTyped g e path ∧ path.responseCount = n ∧ path.resumeCount = n := by
  induction n with
  | zero => exact ⟨.refl _, True.intro, rfl, rfl⟩
  | succ n ih =>
      obtain ⟨first, hf, hfr, hfs⟩ := example_round n g e binder
      obtain ⟨last, hl, hlr, hls⟩ := ih
      refine ⟨first.append last, protocol_append first last hf hl, ?_, ?_⟩
      · simp only [responseCount_append, hfr, hlr, Nat.add_comm 1 n]
      · simp only [resumeCount_append, hfs, hls, Nat.add_comm 1 n]

/-- Apply combined preservation to the concrete arbitrarily repeated execution. -/
theorem example_rounds_preserved (n : Nat) (g : GraphEnvironment)
    (e : TypeEnvironment) (binder : TermName) :
    ∃ path : InteractionTrace roundTable binder
        ⟨roundProgram n, []⟩ ⟨.ret (.literal .unit), []⟩,
      ProtocolTyped g e path ∧
      StateTyped roundTable g e ⟨.ret (.literal .unit), []⟩ (.base .unit) ∧
      InteractionErasure roundTable binder (roundProgram n) (.ret (.literal .unit)) := by
  obtain ⟨path, protocol, _, _⟩ := example_arbitrarily_many_rounds n g e binder
  have result := finite_interaction ⟨.base .unit, roundProgram_typed n g e, .nil⟩ path protocol
  exact ⟨path, protocol, result.1, result.2.2⟩

end YulangClosure.PaperTypes.PaperCombinedExecution
