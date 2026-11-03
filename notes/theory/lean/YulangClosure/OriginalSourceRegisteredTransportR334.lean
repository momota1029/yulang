import YulangClosure.OriginalSourceGoalKernelTransportR333

/-!
R334 partial registered-kernel construction. The subject port below is read
from the original source-generated call registry at its site AND context.
It is not selected from a successful Checking or a desired result value.

SG §§3.1–3.3 and SRC §6 require independently fixed primitive/equality
meanings. This file does not supply those missing meanings, a registry of
finite checking declarations, or registered-kernel transport. It constructs
the actual selected source's subject-port component, applies it at R333's
same candidate extension, and exposes the remaining registered obligations.
-/
namespace YulangClosure.OriginalSourceRegisteredTransportR334

open OriginalSource OriginalScopedClosure OriginalSourceInterpretation
open OriginalSourceEnvironment OriginalSourceChecking OriginalCheckingAdmission
open OriginalInterfacePreservationR328 OriginalSourceViewRegistrationR330
open OriginalSourceEnvironmentTransportR331 OriginalSourcePrefixBridgeR332

variable {s : Sorts} {View G : Type}

/-- Both source occurrence and lexical context participate in lookup. -/
def subjectOf (owners : List CallOwner) (site : Site) (context : Context) : Endpoint :=
  (((owners.find? (fun owner => owner.site == site && owner.context == context)).map
    CallOwner.subject).getD ⟨site,.finalRoot⟩)

/-- This constructs only the source-owned subject field. Equality operands
still require their independently fixed original typed declaration readout. -/
def sourcePorts (equality : Decoded s View → Endpoint → Operand s) : PortReadout s View where
  subject state site context := subjectOf state.callOwners site context
  equality := equality

theorem subject_independent_of_equality
    (first second : Decoded s View → Endpoint → Operand s)
    (state : Decoded s View) (site : Site) (context : Context) :
    (sourcePorts first).subject state site context =
      (sourcePorts second).subject state site context := rfl

/-- Actual source syntax, including R315's module binding and formal scope,
computes this registry. Neither source typing nor successful inference is used. -/
theorem selected_source_registry :
    sourceCallOwners OriginalModuleContextBindingR315.externalContext
      OriginalScopedSourceEventMapR314.Fixture.root =
      [.closure 0 OriginalModuleContextBindingR315.externalContext 98 98 1,
       .application 1 selectedContext 2 3, .application 2 selectedContext 4 5] := by
  run_tac Lean.Meta.withTransparency .all <| Lean.Elab.Tactic.evalTactic (← `(tactic| rfl))

theorem selected_source_subject :
    subjectOf (sourceCallOwners OriginalModuleContextBindingR315.externalContext
      OriginalScopedSourceEventMapR314.Fixture.root) 1 selectedContext =
      ⟨OriginalScopedSourceEventMapR314.Fixture.callee.site,.returnedValue⟩ := by
  rw [selected_source_registry]
  run_tac Lean.Meta.withTransparency .all <| Lean.Elab.Tactic.evalTactic (← `(tactic| rfl))

/-- Concrete scope discriminator on the same authentic source registry.
The enclosing module context is not the formal's App context. -/
theorem selected_wrong_context_falls_back :
    subjectOf (sourceCallOwners OriginalModuleContextBindingR315.externalContext
      OriginalScopedSourceEventMapR314.Fixture.root) 1
      OriginalModuleContextBindingR315.externalContext = ⟨1,.finalRoot⟩ := by
  rw [selected_source_registry]
  run_tac Lean.Meta.withTransparency .all <| Lean.Elab.Tactic.evalTactic (← `(tactic| rfl))

theorem selected_subject_differs_from_result :
    subjectOf (sourceCallOwners OriginalModuleContextBindingR315.externalContext
      OriginalScopedSourceEventMapR314.Fixture.root) 1 selectedContext ≠
      (⟨1,.finalRoot⟩ : Endpoint) := by
  rw [selected_source_subject]
  decide

theorem source_ports_after_frames
    (equality : Decoded s View → Endpoint → Operand s)
    (ro : RuntimeReadout s View) (root : Root s View)
    (frames : List (Frame (Payload s View))) :
    (sourcePorts equality).subject
      (frames.foldl (decodeFrame ro)
        (root.withSource OriginalModuleContextBindingR315.externalContext
          OriginalScopedSourceEventMapR314.Fixture.root).decoded) 1 selectedContext =
      ⟨OriginalScopedSourceEventMapR314.Fixture.callee.site,.returnedValue⟩ := by
  change subjectOf _ _ _ = _
  rw [decoded_call_owners]
  exact selected_source_subject

/-- A root equality here is static provenance, not an original source
judgment. The theorem derives the port for arbitrary ordered frames. -/
theorem decoded_source_subject
    (equality : Decoded s View → Endpoint → Operand s)
    (ro : RuntimeReadout s View) (env : Environment (Payload s View))
    (root : Root s View)
    (sourceRoot : env.root = .root (root.withSource
      OriginalModuleContextBindingR315.externalContext OriginalScopedSourceEventMapR314.Fixture.root))
    (state : Decoded s View) (found : decode ro env = some state) :
    (sourcePorts equality).subject state 1 selectedContext =
      ⟨OriginalScopedSourceEventMapR314.Fixture.callee.site,.returnedValue⟩ := by
  simp only [decode,sourceRoot] at found
  cases Option.some.inj found
  exact source_ports_after_frames equality ro root env.frames

/-- Every runtime/logical/Shared frame retains source-owned incidence.
This includes frames with provisional or semantically unadmitted payloads. -/
theorem decode_frame_subject
    (equality : Decoded s View → Endpoint → Operand s)
    (ro : RuntimeReadout s View) (state : Decoded s View)
    (frame : Frame (Payload s View)) (site : Site) (context : Context) :
    (sourcePorts equality).subject (decodeFrame ro state frame) site context =
      (sourcePorts equality).subject state site context := by
  change subjectOf _ site context = subjectOf _ site context
  have preserved := decoded_call_owners ro state [frame]
  simpa only [List.foldl_cons,List.foldl_nil] using
    congrArg (fun owners => subjectOf owners site context) preserved

/-- The conservative interface extension preserves the ACTUAL source
registry. Target equality readout is still independent and not authenticated. -/
theorem embedded_subject (g : G)
    (oldEquality : Decoded s View → Endpoint → Operand s)
    (newEquality : Decoded (extended s G) (Sum View Unit) → Endpoint → Operand (extended s G))
    (state : Decoded s View) (site : Site) (context : Context) :
    (sourcePorts newEquality).subject (decoded g state) site context =
      (sourcePorts oldEquality).subject state site context := rfl

/-- Same old candidate and same generated candidate as R332/R333. This
constructs their exact callable port without a target checking assumption. -/
theorem selected_candidate_subject
    (oldEquality : Decoded s View → Endpoint → Operand s)
    (newEquality : Decoded (extended s Code) (Sum View Unit) → Endpoint → Operand (extended s Code))
    (ro : RuntimeReadout s View) (reached : Environment (Payload s View))
    (root : Root s View)
    (sourceRoot : reached.root = .root (root.withSource
      OriginalModuleContextBindingR315.externalContext OriginalScopedSourceEventMapR314.Fixture.root))
    (state : Decoded s View) (found : decode ro reached = some state)
    (data : Logical s View) (occurrence : Nat)
    {origin : Declaration} {declared : ComputedCallTypedFormationR310.Key → Prop}
    (definition : Definition origin declared) :
    let candidate := scopeCandidate (environment definition.code reached) occurrence (definedPayload data definition)
    let after := (environment definition.code reached).extend ⟨1,.viewLogic,0⟩ candidate
    ∃ next, decode (readout definition.code ro) after = some next ∧
      (sourcePorts newEquality).subject next 1 selectedContext =
        ⟨OriginalScopedSourceEventMapR314.Fixture.callee.site,.returnedValue⟩ := by
  dsimp only
  have extension := actual_parent_extension_image definition reached data occurrence
  change environment definition.code
      (reached.extend ⟨1,.viewLogic,0⟩ (scopeCandidate reached occurrence (.logical .viewLogic data))) =
    (environment definition.code reached).extend ⟨1,.viewLogic,0⟩
      (scopeCandidate (environment definition.code reached) occurrence (definedPayload data definition)) at extension
  rw [← extension]
  rw [decode_commutes]
  let candidate := scopeCandidate reached occurrence (.logical .viewLogic data)
  let next := decodeFrame ro state ⟨⟨1,.viewLogic,0⟩,candidate,reached.eventPath⟩
  have nextFound := decode_extend ro reached ⟨1,.viewLogic,0⟩ candidate state found
  rw [nextFound]
  refine ⟨decoded definition.code next,rfl,?_⟩
  rw [embedded_subject definition.code oldEquality newEquality]
  rw [decode_frame_subject]
  exact decoded_source_subject oldEquality ro reached root sourceRoot state found

/-- Prefix execution extends environments, never their actual source root. -/
theorem prefix_root (env : Environment V) (steps : List (Binder × ScopedValue V)) :
    (runPrefix env steps).root = env.root := by
  induction steps generalizing env with
  | nil => rfl
  | cons step rest ih =>
      change (runPrefix (env.extend step.1 step.2) rest).root = env.root
      rw [ih]
      rfl

theorem registered_root
    {origin : Declaration} {declared : ComputedCallTypedFormationR310.Key → Prop}
    (definition : Definition origin declared) (base : Inputs s) (gen : Generated s Code)
    (ro : RuntimeReadout s View) (adm : LocalAdmissions s View)
    (initial reached : Environment (Payload s View)) (data : Logical s View) (occurrence : Nat)
    (registered : RegisteredAt definition base gen ro adm initial reached data occurrence) :
    reached.root = initial.root := by
  obtain ⟨steps,_,_,reachedEq,_⟩ := registered
  rw [reachedEq]
  exact prefix_root initial steps

/-- Applied to the unchanged R333 parent, retaining its entire conclusion.
The independently constructed subject law holds for EVERY candidate, hence
for precisely its original occurrence/data witness and both source children.
Static root provenance is explicit; it is not inferred from source typing.
No target registered Checking or registry/equality authentication is asserted. -/
theorem parent_with_constructed_subject
    {origin : Declaration} {declared : ComputedCallTypedFormationR310.Key → Prop}
    (definition : Definition origin declared) (base : Inputs s) (gen : Generated s Code)
    (ro : RuntimeReadout s View) (adm : LocalAdmissions s View)
    (original : Kernel (Payload s View)) (initial reached : Environment (Payload s View))
    (root : Root s View)
    (sourceRoot : initial.root = .root (root.withSource
      OriginalModuleContextBindingR315.externalContext OriginalScopedSourceEventMapR314.Fixture.root))
    (oldEquality : Decoded s View → Endpoint → Operand s)
    (newEquality : Decoded (extended s Code) (Sum View Unit) → Endpoint → Operand (extended s Code))
    (parent : OriginalSourceGoalKernelTransportR333.ParentRegisteredAt
      definition base gen ro adm original initial reached) :
    OriginalSourceGoalKernelTransportR333.ParentTransportedAt
      definition base gen ro adm original initial reached ∧
    ∀ (data : Logical s View) (occurrence : Nat),
      let candidate := scopeCandidate (environment definition.code reached) occurrence (definedPayload data definition)
      let after := (environment definition.code reached).extend ⟨1,.viewLogic,0⟩ candidate
      ∃ next, decode (readout definition.code ro) after = some next ∧
        (sourcePorts newEquality).subject next 1 selectedContext =
          ⟨OriginalScopedSourceEventMapR314.Fixture.callee.site,.returnedValue⟩ := by
  refine ⟨OriginalSourceGoalKernelTransportR333.registered_parent_transport
    definition base gen ro adm original initial reached parent,?_⟩
  obtain ⟨_,occurrence,data,state,found,_,_,_,_,_,registration,_⟩ := parent
  have reachedRoot := (registered_root definition base gen ro adm initial reached data occurrence registration).trans sourceRoot
  intro data occurrence
  exact selected_candidate_subject oldEquality newEquality ro reached root reachedRoot state found data occurrence definition

end YulangClosure.OriginalSourceRegisteredTransportR334
