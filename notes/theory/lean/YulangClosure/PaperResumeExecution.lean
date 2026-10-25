import YulangClosure.PaperPerformLetExecution

/-!
R50: manuscript :458–466 and :1069–1085, empty-owner response substitution.
The saved body is an immutable input. Owner freshening, corrected lifetime
state, handlers, and source/native simulation remain separate obligations.
-/
namespace YulangClosure.PaperTypes.PaperResumeExecution

open PaperCoreControl

/-- Only the empty-owner continuation case; freshening is vacuous here. -/
def resumeStep : Computation → Option Computation
  | .resume (.continuation [] _ body) response =>
      termSubstituteComputation (PaperCoreStep.singleReplacement response) body
  | _ => none

theorem resumeStep_eq (binder body response) :
    resumeStep (.resume (.continuation [] binder body) response) =
      termSubstituteComputation (PaperCoreStep.singleReplacement response) body := rfl

/-- Arbitrary shared declarations, graph and lexical environment; Q and A differ. -/
theorem resume_applicable {d g e binder body response q a}
    (hk : PaperContinuationTyped d g e (.continuation [] binder body) q a)
    (hv : PaperValueTyped d g e response q) :
    ∃ next, resumeStep (.resume (.continuation [] binder body) response) = some next ∧
      PaperComputationTyped d g e next a := by
  cases hk with
  | continuation hb => exact hb.termSubstitute (PaperCoreStep.singleReplacement_typed hv)

theorem resume_preservation {d g e binder body response next q a}
    (hk : PaperContinuationTyped d g e (.continuation [] binder body) q a)
    (hv : PaperValueTyped d g e response q)
    (hs : resumeStep (.resume (.continuation [] binder body) response) = some next) :
    PaperComputationTyped d g e next a := by
  obtain ⟨actual, ha, ht⟩ := resume_applicable hk hv
  exact Option.some.inj (ha.symm.trans hs) ▸ ht

theorem resume_typed {d g e binder body response q a}
    (hk : PaperContinuationTyped d g e (.continuation [] binder body) q a)
    (hv : PaperValueTyped d g e response q) :
    PaperComputationTyped d g e (.resume (.continuation [] binder body) response) a :=
  .resume (.continuation hk) hv

/-- Invert the existing computation rule, without changing its premises. -/
theorem typed_resume_preservation {d g e binder body response next a}
    (ht : PaperComputationTyped d g e (.resume (.continuation [] binder body) response) a)
    (hs : resumeStep (.resume (.continuation [] binder body) response) = some next) :
    PaperComputationTyped d g e next a := by
  cases ht with
  | resume hk hv =>
      cases hk with
      | continuation hc => exact resume_preservation hc hv hs

/-- Both branches read exactly the same saved body and its original derivation. -/
theorem two_resumes {d g e binder body first second q a}
    (hk : PaperContinuationTyped d g e (.continuation [] binder body) q a)
    (hfirst : PaperValueTyped d g e first q)
    (hsecond : PaperValueTyped d g e second q) :
    ∃ nextFirst nextSecond,
      resumeStep (.resume (.continuation [] binder body) first) = some nextFirst ∧
      PaperComputationTyped d g e nextFirst a ∧
      resumeStep (.resume (.continuation [] binder body) second) = some nextSecond ∧
      PaperComputationTyped d g e nextSecond a ∧
      PaperContinuationTyped d g e (.continuation [] binder body) q a := by
  obtain ⟨nextFirst, hf, htf⟩ := resume_applicable hk hfirst
  obtain ⟨nextSecond, hs, hts⟩ := resume_applicable hk hsecond
  exact ⟨nextFirst, nextSecond, hf, htf, hs, hts, hk⟩

/-- Invert a request using the actual instance's response field. -/
theorem request_continuation_typed {d g e op payload binder body a}
    (ht : PaperComputationTyped d g e
      (.request op payload (.continuation [] binder body)) a) :
    PaperContinuationTyped d g e (.continuation [] binder body) op.responseType a := by
  cases ht with
  | request resolved arity instanceEq hp hk =>
      cases instanceEq
      exact hk

/-- Apply directly to R49: retain its one saved witness and complete packet. -/
theorem perform_through_stack_resumable
    {d g e declaration operation arguments payload binder stack a}
    (resolved : OperationDeclarationResolved d.operations operation declaration)
    (arity : arguments.length = declaration.typeArity)
    (hp : PaperValueTyped d g e payload (declaration.instantiate arguments).payloadType)
    (hf : StackTyped d g e stack (declaration.instantiate arguments).responseType a) :
    ∃ saved,
      PaperPerformLetExecution.performStep d binder (.perform operation arguments payload) =
        some (.request (declaration.instantiate arguments) payload
          (.continuation [] binder (.ret (.variable 0)))) ∧
      PaperPerformLetExecution.RequestTrace
        ⟨.request (declaration.instantiate arguments) payload
          (.continuation [] binder (.ret (.variable 0))), stack⟩
        ⟨.request (declaration.instantiate arguments) payload (.continuation [] binder saved), []⟩ ∧
      PaperComputationTyped d g e
        (.request (declaration.instantiate arguments) payload (.continuation [] binder saved)) a ∧
      PaperContinuationTyped d g e (.continuation [] binder saved)
        (declaration.instantiate arguments).responseType a ∧
      ∀ response, PaperValueTyped d g e response (declaration.instantiate arguments).responseType →
        ∃ next, resumeStep (.resume (.continuation [] binder saved) response) = some next ∧
          PaperComputationTyped d g e next a := by
  obtain ⟨saved, hs, path, ht⟩ :=
    PaperPerformLetExecution.perform_through_stack resolved arity hp hf
  have hk := request_continuation_typed ht
  exact ⟨saved, hs, path, ht, hk, fun _ hv => resume_applicable hk hv⟩

/-- The two response branches share R49's same saved continuation and instance. -/
theorem perform_through_stack_two_resumes
    {d g e declaration operation arguments payload binder stack first second a}
    (resolved : OperationDeclarationResolved d.operations operation declaration)
    (arity : arguments.length = declaration.typeArity)
    (hp : PaperValueTyped d g e payload (declaration.instantiate arguments).payloadType)
    (hf : StackTyped d g e stack (declaration.instantiate arguments).responseType a)
    (hfirst : PaperValueTyped d g e first (declaration.instantiate arguments).responseType)
    (hsecond : PaperValueTyped d g e second (declaration.instantiate arguments).responseType) :
    ∃ saved nextFirst nextSecond,
      PaperPerformLetExecution.RequestTrace
        ⟨.request (declaration.instantiate arguments) payload
          (.continuation [] binder (.ret (.variable 0))), stack⟩
        ⟨.request (declaration.instantiate arguments) payload (.continuation [] binder saved), []⟩ ∧
      resumeStep (.resume (.continuation [] binder saved) first) = some nextFirst ∧
      PaperComputationTyped d g e nextFirst a ∧
      resumeStep (.resume (.continuation [] binder saved) second) = some nextSecond ∧
      PaperComputationTyped d g e nextSecond a ∧
      PaperContinuationTyped d g e (.continuation [] binder saved)
        (declaration.instantiate arguments).responseType a := by
  obtain ⟨saved, _, path, ht⟩ :=
    PaperPerformLetExecution.perform_through_stack resolved arity hp hf
  obtain ⟨nextFirst, nextSecond, hs⟩ :=
    two_resumes (request_continuation_typed ht) hfirst hsecond
  exact ⟨saved, nextFirst, nextSecond, path, hs⟩

/-- Existing computation reductions plus only the external empty-owner resume. -/
inductive ComputationStep (d : DeclarationTable) (controlBinder : TermName) :
    Computation → Computation → Prop where
  | existing {head next} : PaperPerformLetExecution.PaperLetContextStep d controlBinder head next →
      ComputationStep d controlBinder head next
  | resume {binder body response next} :
      resumeStep (.resume (.continuation [] binder body) response) = some next →
      ComputationStep d controlBinder (.resume (.continuation [] binder body) response) next
  | underLet {head next body} : ComputationStep d controlBinder head next →
      ComputationStep d controlBinder (.letE head body) (.letE next body)

theorem plug_step {d controlBinder head next}
    (hs : ComputationStep d controlBinder head next) (stack : List Computation) :
    ComputationStep d controlBinder (plug stack head) (plug stack next) := by
  induction stack generalizing head next with
  | nil => exact hs
  | cons body rest ih => exact ih (.underLet hs)

theorem resume_erasure {d controlBinder binder body response next stack}
    (hs : resumeStep (.resume (.continuation [] binder body) response) = some next) :
    ComputationStep d controlBinder
      (erase ⟨.resume (.continuation [] binder body) response, stack⟩)
      (erase ⟨next, stack⟩) := plug_step (.resume hs) stack

/-- Finite evidence includes administrative equalities without inventing steps. -/
inductive ErasureTrace (d : DeclarationTable) (controlBinder : TermName) :
    Computation → Computation → Prop where
  | refl (c) : ErasureTrace d controlBinder c c
  | tail {first middle last} : ErasureTrace d controlBinder first middle →
      (middle = last ∨ ComputationStep d controlBinder middle last) →
      ErasureTrace d controlBinder first last

theorem erasureTrace_trans {d controlBinder first middle last}
    (hf : ErasureTrace d controlBinder first middle)
    (hl : ErasureTrace d controlBinder middle last) :
    ErasureTrace d controlBinder first last := by
  induction hl with
  | refl => exact hf
  | tail path hs ih => exact .tail ih hs

/-- Use R49's literal Trace and its actual erasure theorem. -/
theorem trace_erasure {d controlBinder first last}
    (path : PaperPerformLetExecution.Trace d controlBinder first last) :
    ErasureTrace d controlBinder (erase first) (erase last) := by
  induction path with
  | refl => exact .refl _
  | tail path hs ih =>
      cases PaperPerformLetExecution.erasure hs with
      | inl he => exact .tail ih (.inl he)
      | inr he => exact .tail ih (.inr (.existing he))

/-- Preservation and computation erasure for every supplied finite R49 prefix. -/
theorem resume_prefix {d g e binder body response next q a stack result controlBinder last}
    (hk : PaperContinuationTyped d g e (.continuation [] binder body) q a)
    (hv : PaperValueTyped d g e response q)
    (hf : StackTyped d g e stack a result)
    (hs : resumeStep (.resume (.continuation [] binder body) response) = some next)
    (path : PaperPerformLetExecution.Trace d controlBinder ⟨next, stack⟩ last) :
    StateTyped d g e last result ∧
      PaperComputationTyped d g e (erase last) result ∧
      ErasureTrace d controlBinder
        (erase ⟨.resume (.continuation [] binder body) response, stack⟩) (erase last) := by
  have ht : StateTyped d g e ⟨next, stack⟩ result :=
    ⟨a, resume_preservation hk hv hs, hf⟩
  have hl := PaperPerformLetExecution.trace_preservation ht path
  exact ⟨hl, erase_typed hl,
    erasureTrace_trans (.tail (.refl _) (.inr (resume_erasure hs))) (trace_erasure path)⟩

theorem nonempty_owner_rejected (owner owners binder body response) :
    resumeStep (.resume (.continuation (owner :: owners) binder body) response) = none := rfl

/-- Index zero is the response; outer lexical variables decrease by one. -/
theorem response_outer_discriminator (binder response n) :
    resumeStep (.resume (.continuation [] binder (.ret (.variable 0))) response) =
      some (.ret response) ∧
    resumeStep (.resume (.continuation [] binder (.ret (.variable (n + 1)))) response) =
      some (.ret (.variable n)) := by
  simp [resumeStep, termSubstituteComputation, supportedTermComputation, supportedTermValue,
    replaceTermComputation, replaceTermValue, PaperCoreStep.singleReplacement]

/-- A response free variable crosses a let binder without capture. -/
theorem binder_capture_discriminator (binder) :
    resumeStep (.resume (.continuation [] binder
      (.letE (.ret (.variable 0)) (.ret (.variable 1)))) (.variable 0)) =
      some (.letE (.ret (.variable 0)) (.ret (.variable 1))) := by
  simp [resumeStep, termSubstituteComputation, supportedTermComputation, supportedTermValue,
    replaceTermComputation, replaceTermValue, PaperCoreStep.singleReplacement,
    liftTermSubstitution, renameTermValue]

/-- A Q=int response resumes a saved A=bool body, in arbitrary shared contexts. -/
theorem distinct_response_result (d : DeclarationTable) (g : GraphEnvironment)
    (e : TypeEnvironment) (binder : TermName) :
    PaperContinuationTyped d g e (.continuation [] binder (.ret (.literal (.boolean true))))
      (.base .int) (.base .bool) ∧
    PaperValueTyped d g e (.literal (.integer 7)) (.base .int) ∧
    resumeStep (.resume (.continuation [] binder (.ret (.literal (.boolean true))))
      (.literal (.integer 7))) = some (.ret (.literal (.boolean true))) ∧
    PaperComputationTyped d g e (.ret (.literal (.boolean true))) (.base .bool) := by
  refine ⟨.continuation (.ret .literal), .literal, ?_, .ret .literal⟩
  simp [resumeStep, termSubstituteComputation, supportedTermComputation, supportedTermValue,
    replaceTermComputation, replaceTermValue]

end YulangClosure.PaperTypes.PaperResumeExecution
