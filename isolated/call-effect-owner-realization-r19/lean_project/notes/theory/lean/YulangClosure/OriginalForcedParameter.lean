import YulangClosure.OriginalParameterSemantics

/-!
Actual Force/Return supplies the native Value-entry world premises.
The same independent whole-carrier certificate supplies both the world at
the real observation and its actual returned value. The native bind then
computes the complete extended world. Original demand/force incidence,
traceForm readout, compatibility and independent world guards remain explicit.
No completed Checking proof is reinterpreted as hole-relative membership.
-/
namespace YulangClosure.OriginalForcedParameter

open OriginalSource OriginalSourceInterpretation OriginalSourceEnvironment
open OriginalRecursivePair OriginalParameterSemantics OriginalWorldReadout
open NativeClosureEnvironment SourceIdentityWorld

variable {s b : Sorts} {D V ViewData SiteData Rest Body View : Type}

/-- Every genuine forced Return is read from the same whole carrier.
Neither its pre-bind world nor its returned-field membership is a premise. -/
theorem meaning_force_return_fields (operator : Inputs s)
    (carrier : CarrierRow s) (whole : Meaning operator (.carrier carrier))
    (demandEvent : Event s) (demanded : operator.demand carrier demandEvent)
    (observation : RawObservation s)
    (executed : operator.force carrier.input demandEvent observation)
    (returned : ValueRow s)
    (actualReturn : operator.traceForm (observation.atInterface carrier.interface) =
      .pureReturn returned) :
    operator.forceIncidence carrier demandEvent observation ∧
    Meaning operator (.world observation.event) ∧
    returned.event = observation.event ∧ Meaning operator (.value returned) := by
  have opened := (meaning_iff operator (.carrier carrier)).mp whole
  have forced := (opened.2.2.2.2.1 demandEvent demanded).2 observation executed
  have trace := (meaning_iff operator
    (.trace (observation.atInterface carrier.interface))).mp forced.2
  have fields := trace.2.2.2.1
  change (match operator.traceForm (observation.atInterface carrier.interface) with
    | .pureReturn value => value.event = observation.event ∧ Meaning operator (.value value)
    | .unfinished => True) at fields
  rw [actualReturn] at fields
  exact ⟨forced.1, trace.2.2.1, fields.1, fields.2⟩

/-- Value holes cannot be used as world/trace/carrier holes. This proof
unfolds the original Background operator at the real carrier and observation. -/
theorem background_force_return_fields (operator : Inputs s)
    (holes : ValueRow s → Prop) (carrier : CarrierRow s)
    (whole : Background operator holes (.carrier carrier))
    (demandEvent : Event s) (demanded : operator.demand carrier demandEvent)
    (observation : RawObservation s)
    (executed : operator.force carrier.input demandEvent observation)
    (returned : ValueRow s)
    (actualReturn : operator.traceForm (observation.atInterface carrier.interface) =
      .pureReturn returned) :
    operator.forceIncidence carrier demandEvent observation ∧
    Background operator holes (.world observation.event) ∧
    returned.event = observation.event ∧ Background operator holes (.value returned) := by
  have forced := OriginalRecursivePair.background_force_prefix operator holes carrier whole
    demandEvent demanded observation executed
  have opened := greatest_unfold (RelativePhi operator holes) (relative_monotone operator holes)
    (.trace (observation.atInterface carrier.interface)) forced.2.1
  rcases opened with trace | impossible
  · have fields := trace.2.2.2.1
    change (match operator.traceForm (observation.atInterface carrier.interface) with
      | .pureReturn value => value.event = observation.event ∧ Background operator holes (.value value)
      | .unfinished => True) at fields
    rw [actualReturn] at fields
    exact ⟨forced.1, forced.2.2, fields.1, fields.2⟩
  · cases impossible

/-- The accepted native bind is applied to the actual force observation.
The traceForm equation is the original semantic Return readout at the selected
A, not a supplied V(A) proof or a desired post-bind registry equation. -/
theorem bind_after_force_return_meaning
    (base : Inputs (NS b D V ViewData SiteData Rest Body View))
    (references : Body → Nat → Option Name)
    (carrier : CarrierRow (NS b D V ViewData SiteData Rest Body View))
    (whole : Meaning (inputs base references) (.carrier carrier))
    (demandEvent : Event (NS b D V ViewData SiteData Rest Body View))
    (demanded : (inputs base references).demand carrier demandEvent)
    (observation : RawObservation (NS b D V ViewData SiteData Rest Body View))
    (executed : (inputs base references).force carrier.input demandEvent observation)
    (cells : List (Option (Received V)))
    (vector : observation.event.current.world.cells = vectorStore cells)
    (savedProviders : ∀ provider closure, observation.event.current.providers provider = some closure →
      closure.savedEnvironment < observation.event.current.world.environments.size)
    (savedAliases : ∀ reference ∈ observation.event.current.aliases,
      reference.environment < observation.event.current.world.environments.size)
    (parent : Nat) (formal : Name) (raw : Received V) (node : Node Name D)
    (found : nodeAt observation.event.current.world.environments parent = some node)
    (descriptor : b.Descriptor) (fields : EventFields b)
    (actualReturn : (inputs base references).traceForm (observation.atInterface carrier.interface) =
      .pureReturn ⟨descriptor, observation.event.eta.views.value raw.value,
        observation.event.eta.views.root raw.value, observation.event⟩)
    (later : base.compatible observation.event
      (bindEvent observation.event parent formal raw node found descriptor fields))
    (coherent : base.eventCoherent
      (bindEvent observation.event parent formal raw node found descriptor fields))
    (guards : (base.worldGuards
      (bindEvent observation.event parent formal raw node found descriptor fields)).Valid) :
    Meaning (inputs base references)
      (.world (bindEvent observation.event parent formal raw node found descriptor fields)) := by
  have supplied := meaning_force_return_fields (inputs base references) carrier whole
    demandEvent demanded observation executed _ actualReturn
  exact bind_meaning_world base references observation.event supplied.2.1 cells vector
    savedProviders savedAliases parent formal raw node found descriptor fields later coherent guards
    supplied.2.2.2

/-- The hole-relative native Value entry uses Background's own whole-carrier,
Return and hereditary clauses. Both former recursive bind premises are derived;
the fixed observation domain and source-selected Return readout are unchanged. -/
theorem bind_after_force_return_background
    (base : Inputs (NS b D V ViewData SiteData Rest Body View))
    (references : Body → Nat → Option Name)
    (holes : ValueRow (NS b D V ViewData SiteData Rest Body View) → Prop)
    (holeFuture : ∀ row later, holes row → base.compatible row.event later → holes (row.atEvent later))
    (carrier : CarrierRow (NS b D V ViewData SiteData Rest Body View))
    (whole : Background (inputs base references) holes (.carrier carrier))
    (demandEvent : Event (NS b D V ViewData SiteData Rest Body View))
    (demanded : (inputs base references).demand carrier demandEvent)
    (observation : RawObservation (NS b D V ViewData SiteData Rest Body View))
    (executed : (inputs base references).force carrier.input demandEvent observation)
    (cells : List (Option (Received V)))
    (vector : observation.event.current.world.cells = vectorStore cells)
    (savedProviders : ∀ provider closure, observation.event.current.providers provider = some closure →
      closure.savedEnvironment < observation.event.current.world.environments.size)
    (savedAliases : ∀ reference ∈ observation.event.current.aliases,
      reference.environment < observation.event.current.world.environments.size)
    (parent : Nat) (formal : Name) (raw : Received V) (node : Node Name D)
    (found : nodeAt observation.event.current.world.environments parent = some node)
    (descriptor : b.Descriptor) (fields : EventFields b)
    (actualReturn : (inputs base references).traceForm (observation.atInterface carrier.interface) =
      .pureReturn ⟨descriptor, observation.event.eta.views.value raw.value,
        observation.event.eta.views.root raw.value, observation.event⟩)
    (later : base.compatible observation.event
      (bindEvent observation.event parent formal raw node found descriptor fields))
    (coherent : base.eventCoherent
      (bindEvent observation.event parent formal raw node found descriptor fields))
    (guards : (base.worldGuards
      (bindEvent observation.event parent formal raw node found descriptor fields)).Valid) :
    Background (inputs base references) holes
      (.world (bindEvent observation.event parent formal raw node found descriptor fields)) := by
  have supplied := background_force_return_fields (inputs base references) holes carrier whole
    demandEvent demanded observation executed _ actualReturn
  exact bind_background_world base references holes holeFuture observation.event supplied.2.1 cells vector
    savedProviders savedAliases parent formal raw node found descriptor fields later coherent guards
    supplied.2.2.2

end YulangClosure.OriginalForcedParameter
