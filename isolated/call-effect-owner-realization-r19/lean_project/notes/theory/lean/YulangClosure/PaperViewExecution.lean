import YulangClosure.PaperHeapExecution

/-!
Manuscript :485–493 exposure entry, with corrected V1/V4/V5 shared contexts.
The existing syntax and actual typing judgment retain arbitrary metadata.
Only Force of a view-wrapped literal Delay is added to the connected executor.
Return-path and request/continuation metadata transfer remain unspecified here;
no exposure completion, full View progress, guard, or native correspondence is claimed.
-/
namespace YulangClosure.PaperTypes.PaperViewExecution

open PaperCoreControl

/-- The exact body derivation is recovered without changing any shared context. -/
theorem force_view_delay_inversion {d g e metadata body result}
    (ht : PaperComputationTyped d g e (.force (.view metadata (.delay body))) result) :
    PaperComputationTyped d g e body result := by
  cases ht with
  | force hv =>
      cases hv with
      | view hv =>
          cases hv with
          | delay hb => exact hb

/-- Force/View enters exposure with the same metadata and suspended body. -/
def forceViewStep : Computation → Option Computation
  | .force (.view metadata (.delay body)) => some (.expose metadata body)
  | _ => none

theorem forceViewStep_preservation {d g e head next result}
    (ht : PaperComputationTyped d g e head result)
    (hs : forceViewStep head = some next) :
    PaperComputationTyped d g e next result := by
  cases head with
  | force operand =>
      cases operand with
      | view metadata value =>
          cases value with
          | delay body =>
              have he : Computation.expose metadata body = next := Option.some.inj hs
              cases he
              exact .expose (force_view_delay_inversion ht)
          | _ => simp [forceViewStep] at hs
      | _ => simp [forceViewStep] at hs
  | _ => simp [forceViewStep] at hs

/-- Every previous successful connected transition retains priority. -/
def controlStep (d : DeclarationTable) (binder : TermName) (s : State) : Option State :=
  match PaperExtendedExecution.controlStep d binder s with
  | some next => some next
  | none => (forceViewStep s.head).map (fun next => ⟨next, s.stack⟩)

inductive ControlStepEvidence (d : DeclarationTable) (binder : TermName) :
    State → State → Prop where
  | existing {s next} : PaperExtendedExecution.ControlStepEvidence d binder s next →
      ControlStepEvidence d binder s next
  | exposure {head next stack} : forceViewStep head = some next →
      ControlStepEvidence d binder ⟨head, stack⟩ ⟨next, stack⟩

theorem controlStep_extends {d binder s next}
    (hs : PaperExtendedExecution.controlStep d binder s = some next) :
    controlStep d binder s = some next := by
  simp only [controlStep, hs]

theorem controlStep_evidence {d binder s next}
    (hs : controlStep d binder s = some next) : ControlStepEvidence d binder s next := by
  cases ho : PaperExtendedExecution.controlStep d binder s with
  | some old =>
      have he : old = next := Option.some.inj (by simpa only [controlStep, ho] using hs)
      cases he
      exact .existing (PaperExtendedExecution.controlStep_evidence ho)
  | none =>
      have hx : (forceViewStep s.head).map (fun c => (⟨c, s.stack⟩ : State)) = some next := by
        simpa only [controlStep, ho] using hs
      obtain ⟨c, hc, he⟩ := Option.map_eq_some_iff.mp hx
      cases he
      exact .exposure hc

theorem evidence_preservation {d g e s next result binder}
    (hd : PaperTemplateExecution.BodiesTyped d)
    (ht : StateTyped d g e s result) (hs : ControlStepEvidence d binder s next) :
    StateTyped d g e next result := by
  cases hs with
  | existing ho => exact PaperExtendedExecution.evidence_preservation hd ht ho
  | exposure hb =>
      obtain ⟨a, hh, hf⟩ := ht
      exact ⟨a, forceViewStep_preservation hh hb, hf⟩

theorem preservation {d g e s next result binder}
    (hd : PaperTemplateExecution.BodiesTyped d)
    (ht : StateTyped d g e s result) (hs : controlStep d binder s = some next) :
    StateTyped d g e next result := evidence_preservation hd ht (controlStep_evidence hs)

/-- Existing principal/context evidence and the concrete new entry under lets. -/
inductive ComputationStep (d : DeclarationTable) (binder : TermName) :
    Computation → Computation → Prop where
  | existing {head next} : PaperExtendedExecution.ComputationStep d binder head next →
      ComputationStep d binder head next
  | exposure {head next} : forceViewStep head = some next → ComputationStep d binder head next
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
      cases PaperExtendedExecution.evidence_erasure ho with
      | inl he => exact .inl he
      | inr hp => exact .inr (.existing hp)
  | @exposure head next stack hb => exact .inr (plug_step (.exposure hb) stack)

theorem erasure {d binder s next} (hs : controlStep d binder s = some next) :
    erase s = erase next ∨ ComputationStep d binder (erase s) (erase next) :=
  evidence_erasure (controlStep_evidence hs)

/-- Same arbitrary existing stack and exact metadata/body, without a table law. -/
theorem controlStep_force_view_delay (d : DeclarationTable) (binder : TermName)
    (metadata : ViewMetadata) (body : Computation) (stack : List Computation) :
    controlStep d binder ⟨.force (.view metadata (.delay body)), stack⟩ =
      some ⟨.expose metadata body, stack⟩ := by
  cases stack <;> rfl

/-- The same witnesses supply the actual step, typed result and erased context step.
The new entry needs no code-table well-typedness or closedness assumption. -/
theorem force_view_delay_control {d g e metadata body stack result binder}
    (ht : StateTyped d g e ⟨.force (.view metadata (.delay body)), stack⟩ result) :
    controlStep d binder ⟨.force (.view metadata (.delay body)), stack⟩ =
      some ⟨.expose metadata body, stack⟩ ∧
    StateTyped d g e ⟨.expose metadata body, stack⟩ result ∧
    PaperComputationTyped d g e (erase ⟨.expose metadata body, stack⟩) result ∧
    ControlStepEvidence d binder
      ⟨.force (.view metadata (.delay body)), stack⟩ ⟨.expose metadata body, stack⟩ ∧
    ComputationStep d binder
      (erase ⟨.force (.view metadata (.delay body)), stack⟩)
      (erase ⟨.expose metadata body, stack⟩) := by
  obtain ⟨a, hh, hf⟩ := ht
  have last : StateTyped d g e ⟨.expose metadata body, stack⟩ result :=
    ⟨a, .expose (force_view_delay_inversion hh), hf⟩
  exact ⟨controlStep_force_view_delay d binder metadata body stack, last,
    erase_typed last, .exposure rfl, plug_step (.exposure rfl) stack⟩

/-- Application to the original represented R63 witness, retaining arbitrary metadata. -/
theorem original_obstruction_entry (d : DeclarationTable) (binder : TermName)
    (metadata : ViewMetadata) :
    controlStep d binder
      ⟨.force (.view metadata (.delay (.ret (.literal .unit)))), []⟩ =
      some ⟨.expose metadata (.ret (.literal .unit)), []⟩ ∧
    StateTyped d [] [] ⟨.expose metadata (.ret (.literal .unit)), []⟩ (.base .unit) ∧
    ComputationStep d binder
      (.force (.view metadata (.delay (.ret (.literal .unit)))))
      (.expose metadata (.ret (.literal .unit))) := by
  have initial : StateTyped d [] []
      ⟨.force (.view metadata (.delay (.ret (.literal .unit)))), []⟩ (.base .unit) :=
    ⟨_, .force (.view (.delay (.ret .literal))), .nil⟩
  obtain ⟨hs, ht, _, _, hp⟩ := force_view_delay_control (binder := binder) initial
  exact ⟨hs, ht, hp⟩

/-- This packet supplies no speculative result-path completion operation. -/
theorem expose_not_dispatched (d : DeclarationTable) (binder : TermName)
    (metadata : ViewMetadata) (body : Computation) (stack : List Computation) :
    controlStep d binder ⟨.expose metadata body, stack⟩ = none := by
  cases stack <;> rfl

end YulangClosure.PaperTypes.PaperViewExecution
