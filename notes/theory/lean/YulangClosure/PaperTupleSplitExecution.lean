import YulangClosure.PaperCoreControl

/-!
R44: ordinary tuple split, using R28 simultaneous substitution and the accepted
reversed tuple environment. This is a local computation/finite-let result for
manuscript typing :229, reduction :308 and context :1012–1026. It does not prove
the full state/current-port/residual-graph parent at :1860–1877, source/native
correspondence, inference A/B, or production authority.
-/
namespace YulangClosure.PaperTypes.PaperTupleSplitExecution

/-- A vector in de Bruijn index order, followed by the decremented outer map. -/
def prefixReplacement : List Value → (Nat → Value) → Nat → Value
  | [], rho, n => rho n
  | v :: _, _, 0 => v
  | _ :: rest, rho, n + 1 => prefixReplacement rest rho n

/-- Source tuple order is reversed exactly once; inserted values are simultaneous. -/
def tupleReplacement (values : List Value) (rho : Nat → Value) : Nat → Value :=
  prefixReplacement values.reverse rho

theorem prefixReplacement_tail (values : List Value) (rho : Nat → Value) (n : Nat) :
    prefixReplacement values rho (values.length + n) = rho n := by
  induction values with
  | nil => simp only [List.length_nil, Nat.zero_add, prefixReplacement]
  | cons v rest ih =>
      simpa only [List.length_cons, Nat.succ_add, prefixReplacement] using ih

theorem tupleReplacement_tail (values : List Value) (rho : Nat → Value) (n : Nat) :
    tupleReplacement values rho (values.length + n) = rho n := by
  simpa only [tupleReplacement, List.length_reverse] using
    prefixReplacement_tail values.reverse rho n

private theorem values_append {d g e vs ts ws us}
    (hv : ValuesTyped d g e vs ts) (hw : ValuesTyped d g e ws us) :
    ValuesTyped d g e (vs ++ ws) (ts ++ us) := by
  induction vs generalizing ts with
  | nil => cases hv; exact hw
  | cons v vs ih =>
      cases hv with
      | cons head tail => exact .cons head (ih tail)

private theorem values_reverse {d g e vs ts} (hv : ValuesTyped d g e vs ts) :
    ValuesTyped d g e vs.reverse ts.reverse := by
  induction vs generalizing ts with
  | nil => cases hv; exact .nil
  | cons v vs ih =>
      cases hv with
      | cons head tail =>
          simpa only [List.reverse_cons] using
            values_append (ih tail) (ValuesTyped.cons head ValuesTyped.nil)

theorem values_length {d g e vs ts} (hv : ValuesTyped d g e vs ts) :
    vs.length = ts.length := by
  induction vs generalizing ts with
  | nil => cases hv; rfl
  | cons v vs ih =>
      cases hv with
      | cons head tail => exact congrArg Nat.succ (ih tail)

private theorem prefixReplacement_typed {d g source target vs ts rho}
    (hv : ValuesTyped d g target vs ts)
    (hr : TermSubstitutionTyped d g source target rho) :
    TermSubstitutionTyped d g (ts ++ source) target (prefixReplacement vs rho) := by
  induction vs generalizing ts with
  | nil => cases hv; exact hr
  | cons v vs ih =>
      cases hv with
      | cons head tail =>
          intro n a hn
          cases n with
          | zero =>
              have he : _ = a := Option.some.inj hn
              cases he
              exact head
          | succ n => exact ih tail n a hn

/-- Arbitrary shared D/Xi and outer map; no closed-value premise is required. -/
theorem tupleReplacement_typed {d g source target vs ts rho}
    (hv : ValuesTyped d g target vs ts)
    (hr : TermSubstitutionTyped d g source target rho) :
    TermSubstitutionTyped d g (extendTupleEnvironment ts source) target
      (tupleReplacement vs rho) := by
  exact prefixReplacement_typed (values_reverse hv) hr

/-- The tail keeps the same outer environment with the tuple arity removed. -/
theorem tupleReplacement_identity_typed {d g e vs ts}
    (hv : ValuesTyped d g e vs ts) :
    TermSubstitutionTyped d g (extendTupleEnvironment ts e) e
      (tupleReplacement vs Value.variable) :=
  tupleReplacement_typed hv (fun _ _ hn => .variable hn)

private theorem args_injective {ts us : List Ty} (h : argsSyntax ts = argsSyntax us) :
    ts = us := by
  induction ts generalizing us with
  | nil => cases us <;> simp_all [argsSyntax]
  | cons t ts ih =>
      cases us with
      | nil => simp [argsSyntax] at h
      | cons u us =>
          have he : t = u ∧ argsSyntax ts = argsSyntax us := by
            simpa only [argsSyntax, Ty.tupleCons.injEq] using h
          cases he.1
          exact congrArg (List.cons t) (ih he.2)

private theorem tuple_components {d g e vs a}
    (hv : PaperValueTyped d g e (.tuple vs) a) :
    ∃ ts, a = argsSyntax ts ∧ ValuesTyped d g e vs ts := by
  cases hv with
  | tuple ht => exact ⟨_, rfl, ht⟩

/-- Runtime arity is checked even for untyped raw terms. -/
def splitStep : Computation → Option Computation
  | .split (.tuple values) binders body =>
      if binders.length = values.length then
        termSubstituteComputation (tupleReplacement values Value.variable) body
      else none
  | _ => none

/-- Exact successful split equation: the accepted simultaneous R28 operation. -/
theorem splitStep_eq (values : List Value) (binders : List TermName)
    (body : Computation) (arity : binders.length = values.length) :
    splitStep (.split (.tuple values) binders body) =
      termSubstituteComputation (tupleReplacement values Value.variable) body := by
  simp only [splitStep, ite_eq_left arity]

theorem splitStep_arity_mismatch (values : List Value) (binders : List TermName)
    (body : Computation) (arity : binders.length ≠ values.length) :
    splitStep (.split (.tuple values) binders body) = none := by
  simp only [splitStep, ite_eq_right arity]

/-- Explicit component and binder arities remain the original typing premises. -/
theorem split_applicable_of_components {d g e values types binders body result}
    (hv : ValuesTyped d g e values types)
    (arity : binders.length = types.length)
    (hb : PaperComputationTyped d g (extendTupleEnvironment types e) body result) :
    ∃ next, splitStep (.split (.tuple values) binders body) = some next ∧
      PaperComputationTyped d g e next result := by
  rw [splitStep_eq values binders body (arity.trans (values_length hv).symm)]
  exact hb.termSubstitute (tupleReplacement_identity_typed hv)

/-- Applicability from the actual accepted raw split typing judgment. -/
theorem split_applicable {d g e values binders body result}
    (hc : PaperComputationTyped d g e (.split (.tuple values) binders body) result) :
    ∃ next, splitStep (.split (.tuple values) binders body) = some next ∧
      PaperComputationTyped d g e next result := by
  obtain ⟨types, arity, hv, hb⟩ := hc.splitInversion
  obtain ⟨actual, he, hvalues⟩ := tuple_components hv
  have ht : types = actual := args_injective he
  cases ht
  exact split_applicable_of_components hvalues arity hb

theorem split_preservation {d g e c next result}
    (hc : PaperComputationTyped d g e c result) (hs : splitStep c = some next) :
    PaperComputationTyped d g e next result := by
  cases c with
  | split value binders body =>
      cases value with
      | tuple values =>
          obtain ⟨actual, ha, ht⟩ := split_applicable hc
          have he := Option.some.inj (ha.symm.trans hs)
          exact he ▸ ht
      | _ => simp [splitStep] at hs
  | _ => simp [splitStep] at hs

/-- R35 retains priority and every existing successful result. -/
def step (c : Computation) : Option Computation :=
  match PaperCoreStep.step c with
  | some next => some next
  | none => splitStep c

theorem step_extends {c next} (hs : PaperCoreStep.step c = some next) :
    step c = some next := by simp only [step, hs]

theorem splitStep_to_step {c next} (hs : splitStep c = some next) :
    step c = some next := by
  cases c with
  | split value binders body => simpa only [step, PaperCoreStep.step] using hs
  | _ => simp [splitStep] at hs

theorem preservation {d g e c next result}
    (hc : PaperComputationTyped d g e c result) (hs : step c = some next) :
    PaperComputationTyped d g e next result := by
  cases ho : PaperCoreStep.step c with
  | some old =>
      have he : old = next := Option.some.inj (by simpa only [step, ho] using hs)
      cases he
      exact PaperCoreStep.preservation hc ho
  | none =>
      have hn : splitStep c = some next := by simpa only [step, ho] using hs
      exact split_preservation hc hn

open PaperCoreControl in
/-- Retain R36 push/pop/delegate priority, then offer tuple split. -/
def controlStep (s : State) : Option State :=
  match PaperCoreControl.controlStep s with
  | some next => some next
  | none => (splitStep s.head).map (fun next => ⟨next, s.stack⟩)

open PaperCoreControl in
inductive ControlStepEvidence : State → State → Prop where
  | existing {s next} : PaperCoreControl.ControlStepEvidence s next →
      ControlStepEvidence s next
  | split {head next stack} : splitStep head = some next →
      ControlStepEvidence ⟨head, stack⟩ ⟨next, stack⟩

open PaperCoreControl

theorem controlStep_extends {s next} (hs : PaperCoreControl.controlStep s = some next) :
    controlStep s = some next := by simp only [controlStep, hs]

theorem controlStep_evidence {s next} (hs : controlStep s = some next) :
    ControlStepEvidence s next := by
  cases ho : PaperCoreControl.controlStep s with
  | some old =>
      have he : old = next := Option.some.inj (by simpa only [controlStep, ho] using hs)
      cases he
      exact .existing (PaperCoreControl.controlStep_evidence ho)
  | none =>
      have hm : (splitStep s.head).map (fun c => (⟨c, s.stack⟩ : State)) = some next := by
        simpa only [controlStep, ho] using hs
      obtain ⟨c, hc, he⟩ := Option.map_eq_some_iff.mp hm
      cases he
      rcases s with ⟨head, stack⟩
      exact .split hc

theorem evidence_preservation {d g e s next result}
    (ht : StateTyped d g e s result) (hs : ControlStepEvidence s next) :
    StateTyped d g e next result := by
  cases hs with
  | existing ho => exact PaperCoreControl.evidence_preservation ht ho
  | split hp =>
      obtain ⟨a, hh, hf⟩ := ht
      exact ⟨a, split_preservation hh hp, hf⟩

theorem control_preservation {d g e s next result}
    (ht : StateTyped d g e s result) (hs : controlStep s = some next) :
    StateTyped d g e next result :=
  evidence_preservation ht (controlStep_evidence hs)

/-- The extended principal relation is closed under every ordinary let frame. -/
inductive PaperLetContextStep : Computation → Computation → Prop where
  | principal {head next} : step head = some next → PaperLetContextStep head next
  | underLet {head next body} : PaperLetContextStep head next →
      PaperLetContextStep (.letE head body) (.letE next body)

theorem old_context_step {head next} (hs : PaperCoreControl.PaperLetContextStep head next) :
    PaperLetContextStep head next := by
  induction hs with
  | principal hp => exact .principal (step_extends hp)
  | underLet hp ih => exact .underLet ih

theorem plug_step {head next} (hs : PaperLetContextStep head next)
    (stack : List Computation) :
    PaperLetContextStep (plug stack head) (plug stack next) := by
  induction stack generalizing head next with
  | nil => exact hs
  | cons body rest ih => exact ih (.underLet hs)

theorem evidence_erasure {s next} (hs : ControlStepEvidence s next) :
    erase s = erase next ∨ PaperLetContextStep (erase s) (erase next) := by
  cases hs with
  | existing ho =>
      cases PaperCoreControl.evidence_erasure ho with
      | inl he => exact .inl he
      | inr hp => exact .inr (old_context_step hp)
  | @split head next stack hp =>
      exact .inr (plug_step (.principal (splitStep_to_step hp)) stack)

theorem erasure {s next} (hs : controlStep s = some next) :
    erase s = erase next ∨ PaperLetContextStep (erase s) (erase next) :=
  evidence_erasure (controlStep_evidence hs)

/-- Finite internal transitions keep the same D/Xi/Γ and one final result. -/
inductive Trace : State → State → Prop where
  | refl (s) : Trace s s
  | tail {s mid last} : Trace s mid → controlStep mid = some last → Trace s last

theorem trace_preservation {d g e s last result}
    (ht : StateTyped d g e s result) (hs : Trace s last) :
    StateTyped d g e last result := by
  induction hs with
  | refl => exact ht
  | tail path hstep ih => exact control_preservation ih hstep

/-- Heterogeneous components expose the required reverse order. -/
theorem example_order :
    splitStep (.split (.tuple [.literal (.integer 7), .literal (.boolean true)]) [10,20]
      (.ret (.tuple [.variable 1, .variable 0]))) =
      some (.ret (.tuple [.literal (.integer 7), .literal (.boolean true)])) := by
  simp [splitStep, tupleReplacement, prefixReplacement, termSubstituteComputation,
    supportedTermComputation, supportedTermValue, replaceTermComputation, replaceTermValue]

theorem example_empty :
    splitStep (.split (.tuple []) [] (.ret (.variable 0))) =
      some (.ret (.variable 0)) := by
  simp [splitStep, tupleReplacement, prefixReplacement, termSubstituteComputation,
    supportedTermComputation, supportedTermValue, replaceTermComputation, replaceTermValue]

/-- The replacement is an external variable, transported beneath a let binder. -/
theorem example_external_under_binder :
    splitStep (.split (.tuple [.variable 0]) [10]
      (.letE (.ret (.literal .unit)) (.ret (.tuple [.variable 0, .variable 1, .variable 2])))) =
      some (.letE (.ret (.literal .unit))
        (.ret (.tuple [.variable 0, .variable 1, .variable 1]))) := by
  simp [splitStep, tupleReplacement, prefixReplacement, termSubstituteComputation,
    supportedTermComputation, supportedTermValue, replaceTermComputation, replaceTermValue,
    liftTermSubstitution, renameTermValue]

theorem example_arity_mismatch :
    splitStep (.split (.tuple [.literal .unit]) [] (.ret (.variable 0))) = none := by
  simp [splitStep]

/-- A later substitution must never rewrite an earlier inserted external variable. -/
theorem example_not_sequential :
    let body : Computation := .ret (.variable 0)
    let first : Value := .literal (.integer 7)
    let last : Value := .variable 0
    termSubstituteComputation (tupleReplacement [first,last] Value.variable) body =
      some (.ret (.variable 0)) ∧
    (termSubstituteComputation (PaperCoreStep.singleReplacement last) body).bind
      (termSubstituteComputation (PaperCoreStep.singleReplacement first)) =
      some (.ret (.literal (.integer 7))) := by
  simp [tupleReplacement, prefixReplacement, termSubstituteComputation, supportedTermComputation,
    supportedTermValue, replaceTermComputation, replaceTermValue, PaperCoreStep.singleReplacement]

end YulangClosure.PaperTypes.PaperTupleSplitExecution
