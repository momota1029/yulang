import YulangClosure.PaperCoreStep

/-!
Finite ordinary let control for the actual paper execution syntax. This models
only let active-child descent, R28 return substitution, and the partial R35
principal operator. It is a component of manuscript lines 1014–1026 and
1860–1875, not the full state, current-port, or residual-graph simulation.
-/
namespace YulangClosure.PaperTypes.PaperCoreControl

structure State where
  head : Computation
  stack : List Computation

/-- The head may have an intermediate type different from the final result. -/
inductive StackTyped (d : DeclarationTable) (g : GraphEnvironment)
    (e : TypeEnvironment) : List Computation → Ty → Ty → Prop where
  | nil {a} : StackTyped d g e [] a a
  | cons {body rest a b result} :
      PaperComputationTyped d g (a :: e) body b →
      StackTyped d g e rest b result →
      StackTyped d g e (body :: rest) a result

def StateTyped (d : DeclarationTable) (g : GraphEnvironment)
    (e : TypeEnvironment) (s : State) (result : Ty) : Prop :=
  ∃ intermediate, PaperComputationTyped d g e s.head intermediate ∧
    StackTyped d g e s.stack intermediate result

/-- The first stored body is the innermost pending let body. -/
def plug : List Computation → Computation → Computation
  | [], head => head
  | body :: rest, head => plug rest (.letE head body)

def erase (s : State) : Computation := plug s.stack s.head

/-- Descend before contracting; substitute before delegating to R35. -/
def controlStep (s : State) : Option State :=
  match s.head, s.stack with
  | .letE first body, stack => some ⟨first, body :: stack⟩
  | .ret value, body :: rest =>
      (termSubstituteComputation (PaperCoreStep.singleReplacement value) body).map
        (fun next => ⟨next, rest⟩)
  | head, stack => (PaperCoreStep.step head).map (fun next => ⟨next, stack⟩)

/-- Sound evidence for the three operations. Only `controlStep` selects their
priority; no converse completeness claim about this auxiliary relation is used. -/
inductive ControlStepEvidence : State → State → Prop where
  | push {first body stack} :
      ControlStepEvidence ⟨.letE first body, stack⟩ ⟨first, body :: stack⟩
  | pop {value body rest next} :
      termSubstituteComputation (PaperCoreStep.singleReplacement value) body = some next →
      ControlStepEvidence ⟨.ret value, body :: rest⟩ ⟨next, rest⟩
  | delegate {head next stack} :
      PaperCoreStep.step head = some next →
      ControlStepEvidence ⟨head, stack⟩ ⟨next, stack⟩

/-- Every successful function transition has actual push, pop, or R35 evidence. -/
theorem controlStep_evidence {s s' : State} (hs : controlStep s = some s') :
    ControlStepEvidence s s' := by
  rcases s with ⟨head, stack⟩
  cases head with
  | letE first body =>
      have he : (⟨first, body :: stack⟩ : State) = s' := Option.some.inj hs
      cases he
      exact .push
  | ret value =>
      cases stack with
      | nil => simp [controlStep, PaperCoreStep.step] at hs
      | cons body rest =>
          change (termSubstituteComputation (PaperCoreStep.singleReplacement value) body).map
            (fun next => (⟨next, rest⟩ : State)) = some s' at hs
          obtain ⟨next, hnext, he⟩ := Option.map_eq_some_iff.mp hs
          cases he
          exact .pop hnext
  | force thunk =>
      change (PaperCoreStep.step (.force thunk)).map
        (fun next => (⟨next, stack⟩ : State)) = some s' at hs
      obtain ⟨next, hnext, he⟩ := Option.map_eq_some_iff.mp hs
      cases he
      exact .delegate hnext
  | unionCase value leftBinder left rightBinder right =>
      change (PaperCoreStep.step (.unionCase value leftBinder left rightBinder right)).map
        (fun next => (⟨next, stack⟩ : State)) = some s' at hs
      obtain ⟨next, hnext, he⟩ := Option.map_eq_some_iff.mp hs
      cases he
      exact .delegate hnext
  | unroll value =>
      change (PaperCoreStep.step (.unroll value)).map
        (fun next => (⟨next, stack⟩ : State)) = some s' at hs
      obtain ⟨next, hnext, he⟩ := Option.map_eq_some_iff.mp hs
      cases he
      exact .delegate hnext
  | field value label =>
      change (PaperCoreStep.step (.field value label)).map
        (fun next => (⟨next, stack⟩ : State)) = some s' at hs
      obtain ⟨next, hnext, he⟩ := Option.map_eq_some_iff.mp hs
      cases he
      exact .delegate hnext
  | lookup value label =>
      change (PaperCoreStep.step (.lookup value label)).map
        (fun next => (⟨next, stack⟩ : State)) = some s' at hs
      obtain ⟨next, hnext, he⟩ := Option.map_eq_some_iff.mp hs
      cases he
      exact .delegate hnext
  | _ => simp [controlStep, PaperCoreStep.step] at hs

/-- Stack typing reconstructs the ordinary paper computation typing judgment. -/
theorem plug_typed {d g e stack a result head}
    (hf : StackTyped d g e stack a result)
    (hh : PaperComputationTyped d g e head a) :
    PaperComputationTyped d g e (plug stack head) result := by
  induction hf generalizing head with
  | nil => exact hh
  | cons hb hf ih => exact ih (.letE hh hb)

theorem erase_typed {d g e s result} (ht : StateTyped d g e s result) :
    PaperComputationTyped d g e (erase s) result := by
  obtain ⟨a, hh, hf⟩ := ht
  exact plug_typed hf hh

/-- The auxiliary evidence preserves the literal shared contexts and final type. -/
theorem evidence_preservation {d g e s s' result}
    (ht : StateTyped d g e s result) (hs : ControlStepEvidence s s') :
    StateTyped d g e s' result := by
  obtain ⟨a, hh, hf⟩ := ht
  cases hs with
  | push =>
      cases hh with
      | letE hfirst hbody => exact ⟨_, hfirst, .cons hbody hf⟩
  | pop hpop =>
      cases hh with
      | ret hv =>
          cases hf with
          | cons hbody hrest =>
              obtain ⟨next, hnext, htyped⟩ :=
                hbody.termSubstitute (PaperCoreStep.singleReplacement_typed hv)
              have he := Option.some.inj (hnext.symm.trans hpop)
              cases he
              exact ⟨_, htyped, hrest⟩
  | delegate hstep => exact ⟨a, PaperCoreStep.preservation hh hstep, hf⟩

/-- Every supplied transition preserves one fixed final result under arbitrary D/Xi/Γ. -/
theorem preservation {d g e s s' result}
    (ht : StateTyped d g e s result) (hs : controlStep s = some s') :
    StateTyped d g e s' result :=
  evidence_preservation ht (controlStep_evidence hs)

/-- R35 principal steps closed only under ordinary let active-child contexts. -/
inductive PaperLetContextStep : Computation → Computation → Prop where
  | principal {head next} :
      PaperCoreStep.step head = some next → PaperLetContextStep head next
  | underLet {head next body} :
      PaperLetContextStep head next →
      PaperLetContextStep (.letE head body) (.letE next body)

/-- Lift through every stored frame, retaining their order and actual bodies. -/
theorem plug_step {head next} (hs : PaperLetContextStep head next)
    (stack : List Computation) :
    PaperLetContextStep (plug stack head) (plug stack next) := by
  induction stack generalizing head next with
  | nil => exact hs
  | cons body rest ih => exact ih (.underLet hs)

theorem evidence_erasure {s s' : State} (hs : ControlStepEvidence s s') :
    erase s = erase s' ∨ PaperLetContextStep (erase s) (erase s') := by
  cases hs with
  | push => exact .inl rfl
  | @pop value body rest next hpop =>
      exact .inr (plug_step (head := .letE (.ret value) body) (next := next)
        (.principal hpop) rest)
  | @delegate head next stack hstep =>
      exact .inr (plug_step (.principal hstep) stack)

/-- Push stutters; pop and delegated principal steps reduce under all let frames. -/
theorem erasure {s s' : State} (hs : controlStep s = some s') :
    erase s = erase s' ∨ PaperLetContextStep (erase s) (erase s') :=
  evidence_erasure (controlStep_evidence hs)

end YulangClosure.PaperTypes.PaperCoreControl
