import YulangClosure.PaperTupleSplitExecution

/-!
R46 bounded perform/empty-owner request propagation under ordinary let frames.
Manuscript :318–319, :340–359 and :1012–1026; the full-state/current-port/
residual-graph parent :1860–1877 and source/native correspondence stay open.
-/
namespace YulangClosure.PaperTypes.PaperPerformLetExecution

/-- Find one declaration, then reject any conflicting same-identity entry.
Repeated identical entries are accepted. -/
def resolveOperation (operations : List OperationDeclaration) (operation : DeclarationId) :
    Option OperationDeclaration :=
  match operations.find? (fun entry => entry.identity == operation) with
  | none => none
  | some declaration =>
      if operations.all (fun other => decide (other.identity = operation → other = declaration)) = true
      then some declaration else none

private theorem find_resolved {operations operation declaration}
    (h : OperationDeclarationResolved operations operation declaration) :
    operations.find? (fun entry => entry.identity == operation) = some declaration := by
  cases hf : operations.find? (fun entry => entry.identity == operation) with
  | none =>
      have hn := List.find?_eq_none.mp hf declaration h.1
      have hp : (declaration.identity == operation) = true :=
        h.2.1 ▸ Nat.beq_refl declaration.identity
      exact False.elim (hn hp)
  | some candidate =>
      have hm := List.mem_of_find?_eq_some hf
      have hiBool : (candidate.identity == operation) = true :=
        List.find?_some
          (p := fun entry : OperationDeclaration => entry.identity == operation)
          (a := candidate) (l := operations) hf
      have hi : candidate.identity = operation := Nat.eq_of_beq_eq_true hiBool
      have he := h.2.2 candidate hm hi
      exact congrArg some he

/-- Equivalence to the accepted declaration relation, including duplicates. -/
theorem resolveOperation_iff {operations operation declaration} :
    resolveOperation operations operation = some declaration ↔
      OperationDeclarationResolved operations operation declaration := by
  constructor
  · intro hs
    cases hf : operations.find? (fun entry => entry.identity == operation) with
    | none => simp [resolveOperation, hf] at hs
    | some candidate =>
        have hm := List.mem_of_find?_eq_some hf
        have hiBool : (candidate.identity == operation) = true :=
          List.find?_some
            (p := fun entry : OperationDeclaration => entry.identity == operation)
            (a := candidate) (l := operations) hf
        have hi : candidate.identity = operation := Nat.eq_of_beq_eq_true hiBool
        cases hall : operations.all
            (fun other => decide (other.identity = operation → other = candidate)) with
        | false =>
            have impossible : (none : Option OperationDeclaration) = some declaration := by
              simpa only [resolveOperation, hf, hall, Bool.false_eq_true, ↓reduceIte] using hs
            cases impossible
        | true =>
            have he : candidate = declaration := Option.some.inj (by
              simpa only [resolveOperation, hf, hall, ↓reduceIte] using hs)
            cases he
            exact ⟨hm, hi, by simpa only [List.all_eq_true, decide_eq_true_eq] using hall⟩
  · intro h
    have hall : operations.all
        (fun other => decide (other.identity = operation → other = declaration)) = true := by
      simpa only [List.all_eq_true, decide_eq_true_eq] using h.2.2
    simp only [resolveOperation, find_resolved h, ite_eq_left hall]

/-- A single declaration instance supplies identity, arguments, payload and response. -/
def performStep (d : DeclarationTable) (responseBinder : TermName) :
    Computation → Option Computation
  | .perform operation arguments payload => do
      let declaration ← resolveOperation d.operations operation
      if arguments.length = declaration.typeArity then
        let opInstance := declaration.instantiate arguments
        some (.request opInstance payload
          (.continuation [] responseBinder (.ret (.variable 0))))
      else none
  | _ => none

theorem performStep_eq {d operation arguments payload declaration binder}
    (resolved : OperationDeclarationResolved d.operations operation declaration)
    (arity : arguments.length = declaration.typeArity) :
    performStep d binder (.perform operation arguments payload) =
      some (.request (declaration.instantiate arguments) payload
        (.continuation [] binder (.ret (.variable 0)))) := by
  simp [performStep, resolveOperation_iff.mpr resolved, arity]

theorem performStep_arity_mismatch {d operation arguments payload declaration binder}
    (resolved : OperationDeclarationResolved d.operations operation declaration)
    (arity : arguments.length ≠ declaration.typeArity) :
    performStep d binder (.perform operation arguments payload) = none := by
  simp [performStep, resolveOperation_iff.mpr resolved, arity]

theorem perform_applicable {d g e operation arguments payload result binder}
    (ht : PaperComputationTyped d g e (.perform operation arguments payload) result) :
    ∃ next, performStep d binder (.perform operation arguments payload) = some next ∧
      PaperComputationTyped d g e next result := by
  cases ht with
  | perform resolved arity hp =>
      rename_i declaration
      refine ⟨.request (declaration.instantiate arguments) payload
        (.continuation [] binder (.ret (.variable 0))), performStep_eq resolved arity, ?_⟩
      exact PaperComputationTyped.request
        (declaration := declaration) (arguments := arguments)
        (opInstance := declaration.instantiate arguments) (payload := payload)
        (continuation := .continuation [] binder (.ret (.variable 0)))
        (by simpa only [OperationDeclaration.instantiate, resolved.2.1] using resolved)
        arity rfl hp (.continuation (.ret (.variable rfl)))

theorem perform_preservation {d g e c next result binder}
    (ht : PaperComputationTyped d g e c result)
    (hs : performStep d binder c = some next) :
    PaperComputationTyped d g e next result := by
  cases c with
  | perform operation arguments payload =>
      obtain ⟨actual, ha, htyped⟩ := perform_applicable (binder := binder) ht
      have he := Option.some.inj (ha.symm.trans hs)
      exact he ▸ htyped
  | _ => simp [performStep] at hs

/-- Insert the response hole below the active let binder, simultaneously. -/
def insertResponse : Nat → Value
  | 0 => .variable 0
  | n + 1 => .variable (n + 2)

theorem insertResponse_zero : insertResponse 0 = .variable 0 := rfl

theorem insertResponse_outer (n : Nat) : insertResponse (n + 1) = .variable (n + 2) := rfl

theorem insertResponse_typed (d g e a response) :
    TermSubstitutionTyped d g (a :: e) (a :: response :: e) insertResponse := by
  intro n b hn
  cases n with
  | zero => exact .variable hn
  | succ n => exact .variable hn

/-- Only empty owner lists are accepted; preserve the actual saved body first. -/
def requestBind (head body : Computation) : Option Computation :=
  match head with
  | .request op payload (.continuation [] binder saved) =>
      (termSubstituteComputation insertResponse body).map fun inserted =>
        .request op payload (.continuation [] binder (.letE saved inserted))
  | _ => none

theorem requestBind_applicable {d g e op payload binder saved body a result}
    (hh : PaperComputationTyped d g e
      (.request op payload (.continuation [] binder saved)) a)
    (hb : PaperComputationTyped d g (a :: e) body result) :
    ∃ next, requestBind (.request op payload (.continuation [] binder saved)) body = some next ∧
      PaperComputationTyped d g e next result := by
  cases hh with
  | request resolved arity instanceEq hp hk =>
      cases hk with
      | continuation hs =>
          obtain ⟨inserted, hi, ht⟩ := hb.termSubstitute (insertResponse_typed _ _ _ _ _)
          refine ⟨.request op payload (.continuation [] binder (.letE saved inserted)), ?_,
            .request resolved arity instanceEq hp
              (.continuation (owners := []) (binder := binder) (body := .letE saved inserted)
                (.letE hs ht))⟩
          simp only [requestBind, hi, Option.map_some]

theorem requestBind_preservation {d g e head body next a result}
    (hh : PaperComputationTyped d g e head a)
    (hb : PaperComputationTyped d g (a :: e) body result)
    (hs : requestBind head body = some next) :
    PaperComputationTyped d g e next result := by
  cases head with
  | request op payload continuation =>
      cases continuation with
      | continuation owners binder saved =>
          cases owners with
          | nil =>
              obtain ⟨actual, ha, ht⟩ := requestBind_applicable hh hb
              have he := Option.some.inj (ha.symm.trans hs)
              exact he ▸ ht
          | cons owner rest => simp [requestBind] at hs
      | _ => simp [requestBind] at hs
  | _ => simp [requestBind] at hs

open PaperCoreControl

/-- Fallback after R45: perform first, then request through the innermost let. -/
def extraStep (d : DeclarationTable) (binder : TermName) (s : State) : Option State :=
  match performStep d binder s.head with
  | some next => some ⟨next, s.stack⟩
  | none => match s.stack with
    | [] => none
    | body :: rest => (requestBind s.head body).map (fun next => ⟨next, rest⟩)

/-- R36 push/pop/delegate and R45 split retain their successful results/priority. -/
def controlStep (d : DeclarationTable) (binder : TermName) (s : State) : Option State :=
  match PaperTupleSplitExecution.controlStep s with
  | some next => some next
  | none => extraStep d binder s

inductive ControlStepEvidence (d : DeclarationTable) (binder : TermName) : State → State → Prop where
  | existing {s next} : PaperTupleSplitExecution.ControlStepEvidence s next →
      ControlStepEvidence d binder s next
  | perform {head next stack} : performStep d binder head = some next →
      ControlStepEvidence d binder ⟨head, stack⟩ ⟨next, stack⟩
  | request {head body next rest} : requestBind head body = some next →
      ControlStepEvidence d binder ⟨head, body :: rest⟩ ⟨next, rest⟩

theorem controlStep_extends {d binder s next}
    (hs : PaperTupleSplitExecution.controlStep s = some next) :
    controlStep d binder s = some next := by simp only [controlStep, hs]

theorem controlStep_evidence {d binder s next}
    (hs : controlStep d binder s = some next) : ControlStepEvidence d binder s next := by
  cases ho : PaperTupleSplitExecution.controlStep s with
  | some old =>
      have he : old = next := Option.some.inj (by simpa only [controlStep, ho] using hs)
      cases he
      exact .existing (PaperTupleSplitExecution.controlStep_evidence ho)
  | none =>
      have hx : extraStep d binder s = some next := by simpa only [controlStep, ho] using hs
      rcases s with ⟨head, stack⟩
      cases hp : performStep d binder head with
      | some c =>
          have he : (⟨c, stack⟩ : State) = next := Option.some.inj (by
            simpa only [extraStep, hp] using hx)
          cases he
          exact .perform hp
      | none =>
          cases stack with
          | nil => simp [extraStep, hp] at hx
          | cons body rest =>
              have hm : (requestBind head body).map (fun c => (⟨c, rest⟩ : State)) = some next := by
                simpa only [extraStep, hp] using hx
              obtain ⟨c, hc, he⟩ := Option.map_eq_some_iff.mp hm
              cases he
              exact .request hc

theorem evidence_preservation {d g e s next result binder}
    (ht : StateTyped d g e s result) (hs : ControlStepEvidence d binder s next) :
    StateTyped d g e next result := by
  cases hs with
  | existing ho => exact PaperTupleSplitExecution.evidence_preservation ht ho
  | perform hp =>
      obtain ⟨a, hh, hf⟩ := ht
      exact ⟨a, perform_preservation hh hp, hf⟩
  | request hp =>
      obtain ⟨a, hh, hf⟩ := ht
      cases hf with
      | cons hb hr => exact ⟨_, requestBind_preservation hh hb hp, hr⟩

theorem preservation {d g e s next result binder}
    (ht : StateTyped d g e s result) (hs : controlStep d binder s = some next) :
    StateTyped d g e next result := evidence_preservation ht (controlStep_evidence hs)

/-- Source-shaped reductions closed only under finite ordinary let contexts. -/
inductive PaperLetContextStep (d : DeclarationTable) (binder : TermName) :
    Computation → Computation → Prop where
  | existing {head next} : PaperTupleSplitExecution.PaperLetContextStep head next →
      PaperLetContextStep d binder head next
  | perform {head next} : performStep d binder head = some next →
      PaperLetContextStep d binder head next
  | request {head body next} : requestBind head body = some next →
      PaperLetContextStep d binder (.letE head body) next
  | underLet {head next body} : PaperLetContextStep d binder head next →
      PaperLetContextStep d binder (.letE head body) (.letE next body)

theorem plug_step {d binder head next} (hs : PaperLetContextStep d binder head next)
    (stack : List Computation) :
    PaperLetContextStep d binder (plug stack head) (plug stack next) := by
  induction stack generalizing head next with
  | nil => exact hs
  | cons body rest ih => exact ih (.underLet hs)

theorem evidence_erasure {d binder s next} (hs : ControlStepEvidence d binder s next) :
    erase s = erase next ∨ PaperLetContextStep d binder (erase s) (erase next) := by
  cases hs with
  | existing ho =>
      cases PaperTupleSplitExecution.evidence_erasure ho with
      | inl he => exact .inl he
      | inr hp => exact .inr (.existing hp)
  | @perform head next stack hp => exact .inr (plug_step (.perform hp) stack)
  | @request head body next rest hp => exact .inr (plug_step (.request hp) rest)

theorem erasure {d binder s next} (hs : controlStep d binder s = some next) :
    erase s = erase next ∨ PaperLetContextStep d binder (erase s) (erase next) :=
  evidence_erasure (controlStep_evidence hs)

inductive Trace (d : DeclarationTable) (binder : TermName) : State → State → Prop where
  | refl (s) : Trace d binder s s
  | tail {s mid last} : Trace d binder s mid → controlStep d binder mid = some last →
      Trace d binder s last

theorem trace_preservation {d g e s last result binder}
    (ht : StateTyped d g e s result) (hs : Trace d binder s last) :
    StateTyped d g e last result := by
  induction hs with
  | refl => exact ht
  | tail path hstep ih => exact preservation ih hstep

/-- Every successful perform creates exactly the identity, empty-owner continuation. -/
theorem perform_empty_owner {d binder c next} (hs : performStep d binder c = some next) :
    ∃ op payload, next = .request op payload (.continuation [] binder (.ret (.variable 0))) := by
  cases c with
  | perform operation arguments payload =>
      cases hr : resolveOperation d.operations operation with
      | none => simp [performStep, hr] at hs
      | some declaration =>
          by_cases ha : arguments.length = declaration.typeArity
          · simp only [performStep, hr] at hs
            change (if arguments.length = declaration.typeArity then
              some (.request (declaration.instantiate arguments) payload
                (.continuation [] binder (.ret (.variable 0)))) else none) = some next at hs
            rw [ite_eq_left ha] at hs
            exact ⟨_, _, (Option.some.inj hs).symm⟩
          · simp [performStep, hr, ha] at hs
  | _ => simp [performStep] at hs

/-- The response binder and packet stay fixed through any successful request bind. -/
theorem requestBind_shape {op payload binder saved body next}
    (hs : requestBind (.request op payload (.continuation [] binder saved)) body = some next) :
    ∃ inserted, termSubstituteComputation insertResponse body = some inserted ∧
      next = .request op payload (.continuation [] binder (.letE saved inserted)) := by
  obtain ⟨inserted, hi, he⟩ := Option.map_eq_some_iff.mp hs
  exact ⟨inserted, hi, he.symm⟩

/-- A request with no stored let is exposed, without an internal transition. -/
theorem controlStep_request_nil (d binder op payload continuation) :
    controlStep d binder ⟨.request op payload continuation, []⟩ = none := by
  simp [controlStep, PaperTupleSplitExecution.controlStep, PaperCoreControl.controlStep,
    PaperCoreStep.step, PaperTupleSplitExecution.splitStep, extraStep, performStep]

/-- Request propagation consumes exactly the first stored frame. -/
theorem controlStep_request_cons (d binder op payload continuation body rest) :
    controlStep d binder ⟨.request op payload continuation, body :: rest⟩ =
      (requestBind (.request op payload continuation) body).map (fun next => ⟨next, rest⟩) := by
  simp [controlStep, PaperTupleSplitExecution.controlStep, PaperCoreControl.controlStep,
    PaperCoreStep.step, PaperTupleSplitExecution.splitStep, extraStep, performStep]

/-- Arbitrarily many request-only propagations; no owner alpha-renaming is assumed. -/
inductive RequestTrace : State → State → Prop where
  | refl (s) : RequestTrace s s
  | tail {s head body rest next} : RequestTrace s ⟨head, body :: rest⟩ →
      requestBind head body = some next → RequestTrace s ⟨next, rest⟩

private theorem requestTrace_shape {start last} (hs : RequestTrace start last) :
    ∀ op payload binder saved stack,
      start = ⟨.request op payload (.continuation [] binder saved), stack⟩ →
      ∃ saved' stack', last = ⟨.request op payload (.continuation [] binder saved'), stack'⟩ := by
  induction hs with
  | refl =>
      intro op payload binder saved stack he
      exact ⟨saved, stack, he⟩
  | tail path hstep ih =>
      intro op payload binder saved stack he
      obtain ⟨previous, frames, hp⟩ := ih op payload binder saved stack he
      cases hp
      obtain ⟨inserted, hi, hn⟩ := requestBind_shape hstep
      cases hn
      exact ⟨_, _, rfl⟩

theorem requestTrace_empty_owner {op payload binder saved stack last}
    (hs : RequestTrace ⟨.request op payload (.continuation [] binder saved), stack⟩ last) :
    ∃ saved' stack', last = ⟨.request op payload (.continuation [] binder saved'), stack'⟩ :=
  requestTrace_shape hs op payload binder saved stack rfl

theorem perform_requestTrace_empty_owner {d binder c request stack last}
    (hp : performStep d binder c = some request)
    (hs : RequestTrace ⟨request, stack⟩ last) :
    ∃ op payload saved frames,
      last = ⟨.request op payload (.continuation [] binder saved), frames⟩ := by
  obtain ⟨op, payload, he⟩ := perform_empty_owner hp
  cases he
  obtain ⟨saved, frames, hf⟩ := requestTrace_empty_owner hs
  exact ⟨op, payload, saved, frames, hf⟩

theorem requestTrace_trans {first middle last}
    (hf : RequestTrace first middle) (hl : RequestTrace middle last) : RequestTrace first last := by
  induction hl with
  | refl => exact hf
  | tail path hstep ih => exact .tail ih hstep

/-- Every typed finite ordinary stack can be absorbed, with the final result type. -/
theorem propagate_stack {d g e stack a result op payload binder saved}
    (hf : StackTyped d g e stack a result)
    (hh : PaperComputationTyped d g e (.request op payload (.continuation [] binder saved)) a) :
    ∃ finalSaved,
      RequestTrace ⟨.request op payload (.continuation [] binder saved), stack⟩
        ⟨.request op payload (.continuation [] binder finalSaved), []⟩ ∧
      PaperComputationTyped d g e (.request op payload (.continuation [] binder finalSaved)) result := by
  induction hf generalizing saved with
  | nil => exact ⟨saved, .refl _, hh⟩
  | cons hb hr ih =>
      obtain ⟨next, hn, ht⟩ := requestBind_applicable hh hb
      obtain ⟨inserted, hi, he⟩ := requestBind_shape hn
      cases he
      obtain ⟨finalSaved, path, hfinal⟩ := ih ht
      exact ⟨finalSaved, requestTrace_trans (.tail (.refl _) hn) path, hfinal⟩

/-- Apply the components to the original bounded perform/finite-let obligation.
The same declaration instance and D/Xi/Γ are retained through the whole stack. -/
theorem perform_through_stack {d g e declaration operation arguments payload binder stack final}
    (resolved : OperationDeclarationResolved d.operations operation declaration)
    (arity : arguments.length = declaration.typeArity)
    (hp : PaperValueTyped d g e payload (declaration.instantiate arguments).payloadType)
    (hf : StackTyped d g e stack (declaration.instantiate arguments).responseType final) :
    ∃ saved,
      performStep d binder (.perform operation arguments payload) =
        some (.request (declaration.instantiate arguments) payload
          (.continuation [] binder (.ret (.variable 0)))) ∧
      RequestTrace
        ⟨.request (declaration.instantiate arguments) payload
          (.continuation [] binder (.ret (.variable 0))), stack⟩
        ⟨.request (declaration.instantiate arguments) payload (.continuation [] binder saved), []⟩ ∧
      PaperComputationTyped d g e
        (.request (declaration.instantiate arguments) payload (.continuation [] binder saved)) final := by
  have hh : PaperComputationTyped d g e
      (.request (declaration.instantiate arguments) payload
        (.continuation [] binder (.ret (.variable 0))))
      (declaration.instantiate arguments).responseType := by
    exact PaperComputationTyped.request
      (declaration := declaration) (arguments := arguments)
      (opInstance := declaration.instantiate arguments) (payload := payload)
      (continuation := .continuation [] binder (.ret (.variable 0)))
      (by simpa only [OperationDeclaration.instantiate, resolved.2.1] using resolved)
      arity rfl hp (.continuation (.ret (.variable rfl)))
  obtain ⟨saved, path, ht⟩ := propagate_stack hf hh
  exact ⟨saved, performStep_eq resolved arity, path, ht⟩

private theorem trace_request_shape {d binder start last} (hs : Trace d binder start last) :
    ∀ op payload responseBinder saved stack,
      start = ⟨.request op payload (.continuation [] responseBinder saved), stack⟩ →
      ∃ saved' stack', last = ⟨.request op payload (.continuation [] responseBinder saved'), stack'⟩ := by
  induction hs with
  | refl =>
      intro op payload responseBinder saved stack he
      exact ⟨saved, stack, he⟩
  | tail path hstep ih =>
      intro op payload responseBinder saved stack he
      obtain ⟨previous, frames, hp⟩ := ih op payload responseBinder saved stack he
      cases hp
      cases frames with
      | nil => simp only [controlStep_request_nil] at hstep; contradiction
      | cons body rest =>
          rw [controlStep_request_cons] at hstep
          obtain ⟨next, hn, heq⟩ := Option.map_eq_some_iff.mp hstep
          cases heq
          obtain ⟨inserted, hi, hnxt⟩ := requestBind_shape hn
          cases hnxt
          exact ⟨_, _, rfl⟩

/-- The actual executable control preserves the empty owner list at every prefix. -/
theorem perform_controlTrace_empty_owner {d binder c request stack last}
    (hp : performStep d binder c = some request)
    (hs : Trace d binder ⟨request, stack⟩ last) :
    ∃ op payload saved frames,
      last = ⟨.request op payload (.continuation [] binder saved), frames⟩ := by
  obtain ⟨op, payload, he⟩ := perform_empty_owner hp
  cases he
  obtain ⟨saved, frames, hf⟩ := trace_request_shape hs op payload binder (.ret (.variable 0)) stack rfl
  exact ⟨op, payload, saved, frames, hf⟩

theorem nonempty_owner_rejected (op payload owner owners binder saved body) :
    requestBind (.request op payload (.continuation (owner :: owners) binder saved)) body = none := rfl

/-- With no pending let, a typed request is an external result of the final type. -/
theorem external_request {d g e op payload continuation result}
    (ht : StateTyped d g e ⟨.request op payload continuation, []⟩ result) :
    PaperComputationTyped d g e (.request op payload continuation) result := by
  obtain ⟨a, hh, hf⟩ := ht
  cases hf
  exact hh

/-- Two arbitrary stored let bodies are appended in innermost-first order. -/
theorem two_frames_order {op payload binder saved inner outer inner' outer'}
    (hi : termSubstituteComputation insertResponse inner = some inner')
    (ho : termSubstituteComputation insertResponse outer = some outer') :
    RequestTrace ⟨.request op payload (.continuation [] binder saved), [inner, outer]⟩
      ⟨.request op payload (.continuation [] binder (.letE (.letE saved inner') outer')), []⟩ := by
  have first : RequestTrace
      ⟨.request op payload (.continuation [] binder saved), [inner, outer]⟩
      ⟨.request op payload (.continuation [] binder (.letE saved inner')), [outer]⟩ :=
    .tail (.refl _) (by simp only [requestBind, hi, Option.map_some])
  exact .tail first (by simp only [requestBind, ho, Option.map_some])

theorem repeated_declarations_resolve (declaration : OperationDeclaration) :
    resolveOperation [declaration, declaration] declaration.identity = some declaration := by
  apply resolveOperation_iff.mpr
  refine ⟨by simp, rfl, ?_⟩
  intro other hm hi
  simpa only [List.mem_cons, List.not_mem_nil, or_false, or_self] using hm

theorem conflicting_declarations_rejected {first second : OperationDeclaration}
    (same : first.identity = second.identity) (different : first ≠ second) :
    resolveOperation [first, second] first.identity = none := by
  cases hr : resolveOperation [first, second] first.identity with
  | none => rfl
  | some declaration =>
      have h := resolveOperation_iff.mp hr
      have hfirst := h.2.2 first (by simp) rfl
      have hsecond := h.2.2 second (by simp) same.symm
      exact False.elim (different (hfirst.trans hsecond.symm))

theorem one_instance_fields (declaration : OperationDeclaration) (arguments : List Ty) :
    (declaration.instantiate arguments).identity = declaration.identity ∧
    (declaration.instantiate arguments).typeArguments = argsSyntax arguments ∧
    (declaration.instantiate arguments).payloadType =
      subst (instantiateSubstitution arguments) declaration.payloadTemplate ∧
    (declaration.instantiate arguments).responseType =
      subst (instantiateSubstitution arguments) declaration.responseTemplate := ⟨rfl, rfl, rfl, rfl⟩

/-- Response int, saved continuation result bool, and outer final unit differ. -/
theorem distinct_result_types (d : DeclarationTable) (g : GraphEnvironment) (e : TypeEnvironment) :
    PaperContinuationTyped d g e
      (.continuation [] 9 (.ret (.literal (.boolean true)))) (.base .int) (.base .bool) ∧
    StackTyped d g e [.ret (.literal .unit)] (.base .bool) (.base .unit) :=
  ⟨.continuation (.ret .literal), .cons (.ret .literal) .nil⟩

theorem insertion_discriminator (n : Nat) :
    termSubstituteComputation insertResponse (.ret (.variable 0)) = some (.ret (.variable 0)) ∧
    termSubstituteComputation insertResponse (.ret (.variable (n + 1))) =
      some (.ret (.variable (n + 2))) := by
  simp [termSubstituteComputation, supportedTermComputation, supportedTermValue,
    replaceTermComputation, replaceTermValue, insertResponse]

/-- Unsupported raw bodies are rejected by the actual accepted partial operation. -/
theorem unsupported_body_rejected (op payload binder saved handler body) :
    requestBind (.request op payload (.continuation [] binder saved)) (.handle body handler) = none := by
  simp [requestBind, termSubstituteComputation, supportedTermComputation]

end YulangClosure.PaperTypes.PaperPerformLetExecution
