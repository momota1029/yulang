import YulangClosure.PaperCombinedExecution
import YulangClosure.PaperTypeApplicationPreservation
import YulangClosure.PaperTemplateExecution

/-!
Concrete execution joining the frozen combined machine with administrative
type beta and finite template expansion. Ordinary manuscript reductions
(:303–327) count type normalization as administrative execution and instantiate
the code table once, without inventing a scope, receipt, or view.

All old successful control results retain priority. New administrative beta
acts only on a direct type-abstraction/application redex in a represented active
operand; it never strips metadata or evaluates inside a suspended body. Every
new preservation proof uses the actual beta/template lemmas. `BodiesTyped` is
the independent syntax-directed finite code-table obligation, not a local-law
or reachability assumption. Full progress, corrected world state, all non-let
frames, and source/native correspondence remain outside this partial machine.
-/
namespace YulangClosure.PaperTypes.PaperExtendedExecution

open PaperCoreControl

/-- One direct value beta at an active operand of an already represented
eliminator, or at a returned value. No recursive value normalization is hidden. -/
def typeBetaStep : Computation → Option Computation
  | .ret value => (PaperTypeApplicationPreservation.typeBetaValue value).map Computation.ret
  | .force value => (PaperTypeApplicationPreservation.typeBetaValue value).map Computation.force
  | .split value binders body =>
      (PaperTypeApplicationPreservation.typeBetaValue value).map (fun next => .split next binders body)
  | .field value label =>
      (PaperTypeApplicationPreservation.typeBetaValue value).map (fun next => .field next label)
  | .lookup value label =>
      (PaperTypeApplicationPreservation.typeBetaValue value).map (fun next => .lookup next label)
  | .unroll value => (PaperTypeApplicationPreservation.typeBetaValue value).map Computation.unroll
  | .unionCase value leftBinder left rightBinder right =>
      (PaperTypeApplicationPreservation.typeBetaValue value).map
        (fun next => .unionCase next leftBinder left rightBinder right)
  | .resume continuation response =>
      (PaperTypeApplicationPreservation.typeBetaValue continuation).map
        (fun next => .resume next response)
  | _ => none

theorem typeBetaStep_preservation {d g e head next result}
    (ht : PaperComputationTyped d g e head result) (hs : typeBetaStep head = some next) :
    PaperComputationTyped d g e next result := by
  cases ht with
  | ret hv =>
      obtain ⟨value, hb, he⟩ := Option.map_eq_some_iff.mp hs
      cases he
      exact .ret (PaperTypeApplicationPreservation.typeBetaValue_preservation hv hb)
  | force hv =>
      obtain ⟨value, hb, he⟩ := Option.map_eq_some_iff.mp hs
      cases he
      exact .force (PaperTypeApplicationPreservation.typeBetaValue_preservation hv hb)
  | split arity hv hbody =>
      obtain ⟨value, hb, he⟩ := Option.map_eq_some_iff.mp hs
      cases he
      exact .split arity (PaperTypeApplicationPreservation.typeBetaValue_preservation hv hb) hbody
  | field hv hf =>
      obtain ⟨value, hb, he⟩ := Option.map_eq_some_iff.mp hs
      cases he
      exact .field (PaperTypeApplicationPreservation.typeBetaValue_preservation hv hb) hf
  | lookup hv hf =>
      obtain ⟨value, hb, he⟩ := Option.map_eq_some_iff.mp hs
      cases he
      exact .lookup (PaperTypeApplicationPreservation.typeBetaValue_preservation hv hb) hf
  | unroll hv =>
      obtain ⟨value, hb, he⟩ := Option.map_eq_some_iff.mp hs
      cases he
      exact .unroll (PaperTypeApplicationPreservation.typeBetaValue_preservation hv hb)
  | unionCase hv hl hr =>
      obtain ⟨value, hb, he⟩ := Option.map_eq_some_iff.mp hs
      cases he
      exact .unionCase (PaperTypeApplicationPreservation.typeBetaValue_preservation hv hb) hl hr
  | resume hk hv =>
      obtain ⟨value, hb, he⟩ := Option.map_eq_some_iff.mp hs
      cases he
      exact .resume (PaperTypeApplicationPreservation.typeBetaValue_preservation hk hb) hv
  | _ => simp [typeBetaStep] at hs

/-- Administrative beta precedes finite template expansion in the new fallback. -/
def principalStep (d : DeclarationTable) (head : Computation) : Option Computation :=
  match typeBetaStep head with
  | some next => some next
  | none => PaperTemplateExecution.templateStep d head

/-- A syntax/declaration-directed extension; no typing appears in its definition. -/
def controlStep (d : DeclarationTable) (binder : TermName) (s : State) : Option State :=
  match PaperCombinedExecution.controlStep d binder s with
  | some next => some next
  | none => (principalStep d s.head).map (fun next => ⟨next, s.stack⟩)

inductive ControlStepEvidence (d : DeclarationTable) (binder : TermName) :
    State → State → Prop where
  | existing {s next} : PaperCombinedExecution.ControlStepEvidence d binder s next →
      ControlStepEvidence d binder s next
  | beta {head next stack} : typeBetaStep head = some next →
      ControlStepEvidence d binder ⟨head, stack⟩ ⟨next, stack⟩
  | template {head next stack} : PaperTemplateExecution.templateStep d head = some next →
      ControlStepEvidence d binder ⟨head, stack⟩ ⟨next, stack⟩

theorem controlStep_extends {d binder s next}
    (hs : PaperCombinedExecution.controlStep d binder s = some next) :
    controlStep d binder s = some next := by simp only [controlStep, hs]

theorem controlStep_evidence {d binder s next} (hs : controlStep d binder s = some next) :
    ControlStepEvidence d binder s next := by
  cases ho : PaperCombinedExecution.controlStep d binder s with
  | some old =>
      have he : old = next := Option.some.inj (by simpa only [controlStep, ho] using hs)
      cases he
      exact .existing (PaperCombinedExecution.controlStep_evidence ho)
  | none =>
      have hx : (principalStep d s.head).map (fun c => (⟨c, s.stack⟩ : State)) = some next := by
        simpa only [controlStep, ho] using hs
      obtain ⟨c, hc, he⟩ := Option.map_eq_some_iff.mp hx
      cases he
      rcases s with ⟨head, stack⟩
      cases hb : typeBetaStep head with
      | some value =>
          have he : value = c := Option.some.inj (by simpa only [principalStep, hb] using hc)
          cases he
          exact .beta hb
      | none =>
          exact .template (by simpa only [principalStep, hb] using hc)

/-- Literal shared d/g/e/result; the only new table premise checks actual code. -/
theorem evidence_preservation {d g e s next result binder}
    (hd : PaperTemplateExecution.BodiesTyped d)
    (ht : StateTyped d g e s result) (hs : ControlStepEvidence d binder s next) :
    StateTyped d g e next result := by
  cases hs with
  | existing ho => exact PaperCombinedExecution.evidence_preservation ht ho
  | beta hb =>
      obtain ⟨a, hh, hf⟩ := ht
      exact ⟨a, typeBetaStep_preservation hh hb, hf⟩
  | template hb =>
      obtain ⟨a, hh, hf⟩ := ht
      exact ⟨a, PaperTemplateExecution.template_preservation hd hh hb, hf⟩

theorem preservation {d g e s next result binder}
    (hd : PaperTemplateExecution.BodiesTyped d)
    (ht : StateTyped d g e s result) (hs : controlStep d binder s = some next) :
    StateTyped d g e next result := evidence_preservation hd ht (controlStep_evidence hs)

inductive ComputationStep (d : DeclarationTable) (binder : TermName) :
    Computation → Computation → Prop where
  | existing {head next} : PaperCombinedExecution.ComputationStep d binder head next →
      ComputationStep d binder head next
  | beta {head next} : typeBetaStep head = some next → ComputationStep d binder head next
  | template {head next} : PaperTemplateExecution.templateStep d head = some next →
      ComputationStep d binder head next
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
      cases PaperCombinedExecution.evidence_erasure ho with
      | inl he => exact .inl he
      | inr hp => exact .inr (.existing hp)
  | @beta head next stack hb => exact .inr (plug_step (.beta hb) stack)
  | @template head next stack hb => exact .inr (plug_step (.template hb) stack)

theorem erasure {d binder s next} (hs : controlStep d binder s = some next) :
    erase s = erase next ∨ ComputationStep d binder (erase s) (erase next) :=
  evidence_erasure (controlStep_evidence hs)

inductive Trace (d : DeclarationTable) (binder : TermName) : State → State → Prop where
  | refl (s) : Trace d binder s s
  | tail {first middle last} : Trace d binder first middle →
      controlStep d binder middle = some last → Trace d binder first last

/-- Existing traces embed without any new typing or code-table hypothesis. -/
theorem combined_trace {d binder first last}
    (path : PaperCombinedExecution.Trace d binder first last) : Trace d binder first last := by
  induction path with
  | refl => exact .refl _
  | tail path hs ih => exact .tail ih (controlStep_extends hs)

theorem trace_preservation {d g e first last result binder}
    (hd : PaperTemplateExecution.BodiesTyped d)
    (ht : StateTyped d g e first result) (path : Trace d binder first last) :
    StateTyped d g e last result := by
  induction path with
  | refl => exact ht
  | tail path hs ih => exact preservation hd ih hs

inductive ErasureTrace (d : DeclarationTable) (binder : TermName) :
    Computation → Computation → Prop where
  | refl (c) : ErasureTrace d binder c c
  | tail {first middle last} : ErasureTrace d binder first middle →
      (middle = last ∨ ComputationStep d binder middle last) → ErasureTrace d binder first last

theorem trace_erasure {d binder first last} (path : Trace d binder first last) :
    ErasureTrace d binder (erase first) (erase last) := by
  induction path with
  | refl => exact .refl _
  | tail path hs ih => exact .tail ih (erasure hs)

theorem finite_prefix {d g e first last result binder}
    (hd : PaperTemplateExecution.BodiesTyped d)
    (ht : StateTyped d g e first result) (path : Trace d binder first last) :
    StateTyped d g e last result ∧
      PaperComputationTyped d g e (erase last) result ∧
      ErasureTrace d binder (erase first) (erase last) := by
  have hl := trace_preservation hd ht path
  exact ⟨hl, erase_typed hl, trace_erasure path⟩

/-- The identical raw exposed-request interface, with no world/owner extension. -/
abbrev responseStep := PaperCombinedExecution.responseStep

inductive Event (d : DeclarationTable) (binder : TermName) : State → State → Type where
  | internal {first last} : controlStep d binder first = some last → Event d binder first last
  | response (op payload responseBinder saved response) :
      Event d binder
        ⟨.request op payload (.continuation [] responseBinder saved), []⟩
        ⟨.resume (.continuation [] responseBinder saved) response, []⟩

theorem response_event_eq (op payload responseBinder saved response) :
    responseStep response ⟨.request op payload (.continuation [] responseBinder saved), []⟩ =
      some ⟨.resume (.continuation [] responseBinder saved) response, []⟩ := rfl

def EventAdmissible {d binder first last} (g : GraphEnvironment) (e : TypeEnvironment) :
    Event d binder first last → Prop
  | .internal _ => True
  | .response op _ _ _ response => PaperValueTyped d g e response op.responseType

theorem event_preservation {d binder g e first last result}
    (hd : PaperTemplateExecution.BodiesTyped d)
    (ht : StateTyped d g e first result) (event : Event d binder first last)
    (protocol : EventAdmissible g e event) : StateTyped d g e last result := by
  cases event with
  | internal hs => exact preservation hd ht hs
  | response op payload responseBinder saved response =>
      have hh := PaperPerformLetExecution.external_request ht
      have hk := PaperResumeExecution.request_continuation_typed hh
      exact ⟨result, PaperResumeExecution.resume_typed hk protocol, .nil⟩

inductive InteractionTrace (d : DeclarationTable) (binder : TermName) :
    State → State → Type where
  | refl (s) : InteractionTrace d binder s s
  | tail {first middle last} : InteractionTrace d binder first middle →
      Event d binder middle last → InteractionTrace d binder first last

def ProtocolTyped {d binder first last} (g : GraphEnvironment) (e : TypeEnvironment) :
    InteractionTrace d binder first last → Prop
  | .refl _ => True
  | .tail path event => ProtocolTyped g e path ∧ EventAdmissible g e event

theorem interaction_preservation {d binder g e first last result}
    (hd : PaperTemplateExecution.BodiesTyped d)
    (ht : StateTyped d g e first result) (path : InteractionTrace d binder first last)
    (protocol : ProtocolTyped g e path) : StateTyped d g e last result := by
  induction path with
  | refl => exact ht
  | tail path event ih => exact event_preservation hd (ih protocol.1) event protocol.2

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

theorem interaction_erasure {d binder first last} (path : InteractionTrace d binder first last) :
    InteractionErasure d binder (erase first) (erase last) := by
  induction path with
  | refl => exact .refl _
  | tail path event ih =>
      cases event with
      | internal hs => exact .tail ih (.internal (erasure hs))
      | response op payload responseBinder saved response =>
          exact .tail ih (.response op payload responseBinder saved response)

/-- Arbitrary finite mixed beta/template/core/split/perform/resume/failure and
foreign-response executions under one independently checked finite code table. -/
theorem finite_interaction {d binder g e first last result}
    (hd : PaperTemplateExecution.BodiesTyped d)
    (ht : StateTyped d g e first result) (path : InteractionTrace d binder first last)
    (protocol : ProtocolTyped g e path) :
    StateTyped d g e last result ∧
      PaperComputationTyped d g e (erase last) result ∧
      InteractionErasure d binder (erase first) (erase last) := by
  have hl := interaction_preservation hd ht path protocol
  exact ⟨hl, erase_typed hl, interaction_erasure path⟩

def Event.ofCombined {d binder first last} :
    PaperCombinedExecution.Event d binder first last → Event d binder first last
  | .internal hs => .internal (controlStep_extends hs)
  | .response op payload responseBinder saved value =>
      .response op payload responseBinder saved value

theorem event_ofCombined_admissible {d binder g e first last}
    (event : PaperCombinedExecution.Event d binder first last)
    (protocol : PaperCombinedExecution.EventAdmissible g e event) :
    EventAdmissible g e (Event.ofCombined event) := by
  cases event <;> exact protocol

/-- Embedding preserves the actual events, with no BodiesTyped hypothesis. -/
def InteractionTrace.ofCombined {d binder first last} :
    PaperCombinedExecution.InteractionTrace d binder first last → InteractionTrace d binder first last
  | .refl _ => .refl _
  | .tail path event => .tail (InteractionTrace.ofCombined path) (Event.ofCombined event)

theorem combined_protocol {d binder g e first last}
    (path : PaperCombinedExecution.InteractionTrace d binder first last)
    (protocol : PaperCombinedExecution.ProtocolTyped g e path) :
    ProtocolTyped g e (InteractionTrace.ofCombined path) := by
  induction path with
  | refl => exact True.intro
  | tail path event ih => exact ⟨ih protocol.1, event_ofCombined_admissible event protocol.2⟩

theorem trace_interaction {d binder g e first last} (path : Trace d binder first last) :
    ∃ execution : InteractionTrace d binder first last, ProtocolTyped g e execution := by
  induction path with
  | refl => exact ⟨.refl _, True.intro⟩
  | tail path hs ih =>
      obtain ⟨execution, protocol⟩ := ih
      exact ⟨.tail execution (.internal hs), protocol, True.intro⟩

theorem nonempty_resume_rejected (d controlBinder owner owners binder saved response stack) :
    controlStep d controlBinder
      ⟨.resume (.continuation (owner :: owners) binder saved) response, stack⟩ = none := by
  simp [controlStep, PaperCombinedExecution.nonempty_resume_rejected, principalStep,
    typeBetaStep, PaperTypeApplicationPreservation.typeBetaValue, PaperTemplateExecution.templateStep]

theorem nonempty_request_rejected (d controlBinder op payload owner owners binder saved stack) :
    controlStep d controlBinder
      ⟨.request op payload (.continuation (owner :: owners) binder saved), stack⟩ = none := by
  simp [controlStep, PaperCombinedExecution.nonempty_request_rejected, principalStep,
    typeBetaStep, PaperTemplateExecution.templateStep]

theorem nonempty_response_rejected (op payload owner owners binder saved response) :
    responseStep response
      ⟨.request op payload (.continuation (owner :: owners) binder saved), []⟩ = none := rfl

theorem controlStep_template (d binder identity types values stack) :
    controlStep d binder ⟨.template identity types values, stack⟩ =
      (PaperTemplateExecution.templateStep d (.template identity types values)).map
        (fun next => ⟨next, stack⟩) := by
  cases stack <;>
    simp [controlStep, PaperCombinedExecution.controlStep,
      PaperPerformLetExecution.controlStep, PaperTupleSplitExecution.controlStep,
      PaperCoreControl.controlStep, PaperCoreStep.step, PaperTupleSplitExecution.splitStep,
      PaperPerformLetExecution.extraStep, PaperPerformLetExecution.performStep,
      PaperPerformLetExecution.requestBind, PaperCombinedExecution.extraStep,
      PaperResumeExecution.resumeStep, principalStep, typeBetaStep]

theorem controlStep_force_beta (d binder body argument stack) :
    controlStep d binder
      ⟨.force (.typeApplication (.typeAbstraction body) argument), stack⟩ =
      some ⟨.force (mapPaperValue (instantiateSubstitution [argument]) body), stack⟩ := by
  cases stack <;>
    simp [controlStep, PaperCombinedExecution.controlStep,
      PaperPerformLetExecution.controlStep, PaperTupleSplitExecution.controlStep,
      PaperCoreControl.controlStep, PaperCoreStep.step, PaperTupleSplitExecution.splitStep,
      PaperPerformLetExecution.extraStep, PaperPerformLetExecution.performStep,
      PaperPerformLetExecution.requestBind, PaperCombinedExecution.extraStep,
      PaperResumeExecution.resumeStep, principalStep, typeBetaStep,
      PaperTypeApplicationPreservation.typeBetaValue]

theorem controlStep_ret_beta (d binder body argument) :
    controlStep d binder ⟨.ret (.typeApplication (.typeAbstraction body) argument), []⟩ =
      some ⟨.ret (mapPaperValue (instantiateSubstitution [argument]) body), []⟩ := by
  simp [controlStep, PaperCombinedExecution.controlStep,
    PaperPerformLetExecution.controlStep, PaperTupleSplitExecution.controlStep,
    PaperCoreControl.controlStep, PaperCoreStep.step, PaperTupleSplitExecution.splitStep,
    PaperPerformLetExecution.extraStep, PaperPerformLetExecution.performStep,
    PaperCombinedExecution.extraStep, PaperResumeExecution.resumeStep,
    principalStep, typeBetaStep, PaperTypeApplicationPreservation.typeBetaValue]

theorem controlStep_force_delay (d binder body stack) :
    controlStep d binder ⟨.force (.delay body), stack⟩ = some ⟨body, stack⟩ := by
  apply controlStep_extends
  apply PaperCombinedExecution.controlStep_extends
  apply PaperPerformLetExecution.controlStep_extends
  apply PaperTupleSplitExecution.controlStep_extends
  simp [PaperCoreControl.controlStep, PaperCoreStep.step]

/-! A template with two heterogeneous formals expands into a genuine polymorphic
thunk use. Type beta precedes Force/Delay; the last source formal is index zero.
Its type abstraction shifts the captured formal type from var 1 to var 2, and
beta must restore that ambient type, not substitute the first argument for it. -/

def mixedBody : Computation :=
  .force (.typeApplication (.typeAbstraction (.delay (.ret (.variable 0)))) (.var 0))

def mixedEntry : TemplateBody :=
  .mk 42 2 [.var 0, .var 1] (.var 1) mixedBody

def mixedTable : DeclarationTable := ⟨[], [], [], [mixedEntry], 0⟩

def mixedInvocation : Computation :=
  .template 42 [.base .int, .base .bool]
    [.literal (.integer 7), .literal (.boolean true)]

def mixedExpanded : Computation :=
  .force (.typeApplication
    (.typeAbstraction (.delay (.ret (.literal (.boolean true))))) (.base .int))

theorem mixed_bodiesTyped : PaperTemplateExecution.BodiesTyped mixedTable := by
  intro entry hm
  have he : entry = mixedEntry := List.mem_singleton.mp hm
  subst entry
  refine .mk (.force (.typeApplication (body := .thunk (.var 2)) ?_))
  exact .typeAbstraction (.delay (.ret (.variable rfl)))

theorem mixed_invocation_typed (g : GraphEnvironment) (e : TypeEnvironment) :
    PaperComputationTyped mixedTable g e mixedInvocation (.base .bool) := by
  have resolved : TemplateDeclarationResolved mixedTable.templates 42 mixedEntry := by
    refine ⟨by simp [mixedTable], rfl, ?_⟩
    intro other hm _
    exact List.mem_singleton.mp hm
  exact .template resolved rfl (.cons .literal (.cons .literal .nil))

theorem mixed_expansion :
    PaperTemplateExecution.templateStep mixedTable mixedInvocation = some mixedExpanded := by
  simp [PaperTemplateExecution.templateStep, mixedTable, mixedEntry, mixedInvocation,
    mixedBody, mixedExpanded, PaperTemplateExecution.lookupTemplate, templateIdentity,
    PaperTemplateExecution.expandTemplate, mapPaperComputation, mapPaperValue,
    PaperTupleSplitExecution.tupleReplacement, PaperTupleSplitExecution.prefixReplacement,
    termSubstituteComputation, supportedTermComputation, supportedTermValue,
    replaceTermComputation, replaceTermValue, shiftTermSubstitution,
    subst, instantiateSubstitution, lookupTypeArgument]

/-- Three actual executable transitions: template, beta, and Force/Delay. -/
theorem mixed_trace (binder : TermName) :
    Trace mixedTable binder ⟨mixedInvocation, []⟩
      ⟨.ret (.literal (.boolean true)), []⟩ := by
  have ht : controlStep mixedTable binder ⟨mixedInvocation, []⟩ =
      some ⟨mixedExpanded, []⟩ := by
    unfold mixedInvocation
    rw [controlStep_template]
    change (PaperTemplateExecution.templateStep mixedTable mixedInvocation).map
      (fun next => (⟨next, []⟩ : State)) = some ⟨mixedExpanded, []⟩
    rw [mixed_expansion]
    rfl
  have hb : controlStep mixedTable binder ⟨mixedExpanded, []⟩ =
      some ⟨.force (.delay (.ret (.literal (.boolean true)))), []⟩ := by
    unfold mixedExpanded
    rw [controlStep_force_beta]
    simp [mapPaperValue, mapPaperComputation]
  exact .tail (.tail (.tail (.refl _) ht) hb)
    (controlStep_force_delay mixedTable binder (.ret (.literal (.boolean true))) [])

/-- The finite-table premise is proved, and then applied to the actual mixed
trace in arbitrary caller graph/lexical contexts. -/
theorem mixed_preserved (g : GraphEnvironment) (e : TypeEnvironment) (binder : TermName) :
    StateTyped mixedTable g e ⟨.ret (.literal (.boolean true)), []⟩ (.base .bool) ∧
      PaperComputationTyped mixedTable g e (.ret (.literal (.boolean true))) (.base .bool) ∧
      ErasureTrace mixedTable binder mixedInvocation (.ret (.literal (.boolean true))) :=
  finite_prefix mixed_bodiesTyped ⟨.base .bool, mixed_invocation_typed g e, .nil⟩ (mixed_trace binder)

/-- The new mixed trace also enters the exact external-interaction interface. -/
theorem mixed_interaction (g : GraphEnvironment) (e : TypeEnvironment) (binder : TermName) :
    ∃ path : InteractionTrace mixedTable binder ⟨mixedInvocation, []⟩
        ⟨.ret (.literal (.boolean true)), []⟩,
      ProtocolTyped g e path ∧
      StateTyped mixedTable g e ⟨.ret (.literal (.boolean true)), []⟩ (.base .bool) ∧
      InteractionErasure mixedTable binder mixedInvocation (.ret (.literal (.boolean true))) := by
  obtain ⟨path, hp⟩ := trace_interaction (g := g) (e := e) (mixed_trace binder)
  have result := finite_interaction mixed_bodiesTyped
    ⟨.base .bool, mixed_invocation_typed g e, .nil⟩ path hp
  exact ⟨path, hp, result.1, result.2.2⟩

end YulangClosure.PaperTypes.PaperExtendedExecution
