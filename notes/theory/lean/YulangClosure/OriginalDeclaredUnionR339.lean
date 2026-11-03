import YulangClosure.OriginalSourceEIInterpretationR331
import YulangClosure.OriginalSourceUnionConsumerR338

/-!
R339: derive the complete R306 source packet from the SAME live receiver.

EI §§3.3–3.4 and IF §3 retain independent original primitive/arm laws. This
parametric construction needs no concrete choice of W/Z and no finished EI
body, trace membership, branch packet or child contribution. Original callee
Return inputs, the checked receiver projection and the primitive's own license
remain genuine inputs. The result row is read from this receiver's traceForm.

The final theorem applies the derived trace at R159's unchanged ViewLogic
extension and computation target. Its actual Checking remains independent.
This is a reduction of the receiver-to-packet edge, not full EI registration,
source/native adequacy, arm-inventory construction or whole App admission.
-/
namespace YulangClosure.OriginalDeclaredUnionR339

open OriginalSource OriginalScopedClosure OriginalSourceInterpretation
open OriginalSourceEnvironment OriginalSourceChecking
open ComputedCallTypedFormationR310 OriginalComputedCallInterpretationR311
open OriginalSourceEIInterpretationR331
open SourceSignatureConstruction SourceContributionConstruction
open ComputedCallUnionRealizationR293 ComputedCallPhaseDescriptorR306

variable {s : Sorts} {View : Type}

section Receiver
variable (inputs : Inputs s) (registry : GuardRegistry inputs)
  (resolution : Resolution inputs registry) (leaves : Positive s → Positive s → Prop)
  (children : ∀ A B, leaves A B → A.Holds (Meaning inputs) → B.Holds (Meaning inputs))
  (request : Request) (declarations : PrimitiveDeclarations)
  (callee : s.Interface) (function : s.Descriptor)
  (returned : BoundReturn s request.original.position)
  (original : ReturnInputs inputs registry resolution leaves request declarations callee function returned)
  (current : Event s) (compatible : inputs.compatible returned.value.event current)
  (challenge : Challenge (receiverRow returned function current))
  (domain : CheckedDomain inputs challenge)
  (raw : RawObservation s) (executed : inputs.execute returned.provider challenge.input raw)
  (interface : s.Interface)
  (projection : Proof inputs registry leaves (inputs.checkedObservation challenge raw)
    (.field (.trace (raw.atInterface interface))))

include inputs registry resolution leaves children request declarations callee function returned
  original current compatible challenge domain raw executed interface projection

/-- All checked challenges and actual raw developments are retained. The local
finite projection may eliminate an original compound checkedObservation;
no equality to a singleton trace clause or source-only domain is assumed. -/
theorem receiver_trace : Meaning inputs (.trace (raw.atInterface interface)) := by
  have developments := all_live_receiver_developments inputs registry resolution leaves
    children request declarations callee function returned original current compatible
  have observed := (developments ⟨challenge, domain⟩).2 ⟨raw, executed⟩
  exact Proof.sound inputs registry children projection observed

/-- The original trace clause provides every guard, world, optional return
and dependent observation field. This packet is constructed, not supplied. -/
noncomputable def receiver_packet (state : Decoded s View) (scope : List Binder)
    (source : Endpoint) (read : state.interfaces source = interface) :
    Packet (branchCatalogue inputs state scope source) raw :=
  ⟨(), ComputedCallUnionClausesR308.evidenceOfHolds (Meaning inputs) _
    ((meaning_clause inputs _).mp (by
      rw [read]
      exact receiver_trace inputs registry resolution leaves children request declarations
        callee function returned original current compatible challenge domain raw executed
        interface projection))⟩

/-- No independent result membership is input. The SAME receiver trace
determines its result event, complete world and hereditary returned value. -/
theorem receiver_return (result : ValueRow s)
    (form : inputs.traceForm (raw.atInterface interface) = .pureReturn result) :
    result.event = raw.event ∧ Meaning inputs (.world raw.event) ∧
      Meaning inputs (.value result) := by
  have trace := (meaning_iff inputs _).mp
    (receiver_trace inputs registry resolution leaves children request declarations
      callee function returned original current compatible challenge domain raw executed
      interface projection)
  change PhiT inputs (Meaning inputs) (raw.atInterface interface) at trace
  have value := trace.2.2.2.1
  rw [form] at value
  exact ⟨value.1, trace.2.2.1, value.2⟩

/-- Construct the existing R311 result clause from the preceding actual
receiver. Its independent result/provider primitive law is not synthesized. -/
theorem returned_phase (state : Decoded s View) (result : ValueRow s)
    (form : inputs.traceForm (raw.atInterface interface) = .pureReturn result)
    (provider : s.Provider) (actual : inputs.actual result.value result.root provider)
    (resultInput : PrimitiveInput inputs registry resolution
      (primitiveGoal request declarations .result
        (returnedOperands returned ++ [.value result.value result.root,
          .descriptor result.descriptor, .provider provider,
          .observation raw, .event raw.event]))) :
    (phaseBody inputs registry resolution state request declarations
      (.returned returned result provider raw)).Holds (Meaning inputs) := by
  obtain ⟨same, world, value⟩ := receiver_return inputs registry resolution leaves children
    request declarations callee function returned original current compatible challenge
    domain raw executed interface projection result form
  exact ⟨primitive_input_sound inputs registry resolution _ resultInput _,
    ⟨same, actual⟩, world, value⟩

/-- The later event stays universally independent. Its actual compatibility
and original future primitive are used at that event, with the receiver's
actual returned provider. No future result or future phase proof is assumed. -/
theorem future_phase (state : Decoded s View) (result : ValueRow s)
    (form : inputs.traceForm (raw.atInterface interface) = .pureReturn result)
    (provider : s.Provider) (actual : inputs.actual result.value result.root provider)
    (later : Event s) (laterCompatible : inputs.compatible result.event later)
    (futureInput : PrimitiveInput inputs registry resolution
      (primitiveGoal request declarations .future
        [.value result.value result.root, .descriptor result.descriptor, .provider provider,
         .event result.event, .event later])) :
    (phaseBody inputs registry resolution state request declarations
      (.future result provider later)).Holds (Meaning inputs) := by
  have value := (receiver_return inputs registry resolution leaves children request declarations
    callee function returned original current compatible challenge domain raw executed
    interface projection result form).2.2
  exact future_introduction inputs registry resolution state request declarations result
    provider later value laterCompatible actual futureInput.leaf futureInput.found futureInput.before

/-- Apply the derived complete packet to R338/R306. A source-owned primitive
introduction, its catalogue agreement and its OWN license remain original
inputs. Neither a completed branch packet nor a completed child is supplied.
Every independent arm, including duplicates, remains in the installed result.
-/
theorem receiver_registered (state : Decoded s View) (scope : List Binder)
    (source : Endpoint) (read : state.interfaces source = interface)
    (graph : Graph (RawObservation s)) (old : Relations graph) (ops : Operators graph)
    (site left right : Nat) (arms : List Endpoint)
    (intro : Introduction (RawObservation s))
    (found : graph.node left = some (.primitive intro))
    (agreement : intro.catalogue = branchCatalogue inputs state scope source)
    (licensed :
      let packet := receiver_packet inputs registry resolution leaves children
        request declarations callee function returned original current compatible challenge
        domain raw executed interface projection state scope source read
      let originalPacket := agreement.symm ▸ packet
      intro.License raw originalPacket.port originalPacket.value) :
    let packet := receiver_packet inputs registry resolution leaves children request declarations
      callee function returned original current compatible challenge domain raw executed
      interface projection state scope source read
    let added := unionNode inputs state scope site left right source arms
    let installed := installUnion inputs state scope graph site left right source arms
    Nonempty (DeclContribution installed
      (relations installed (appendRelations graph added old) inputs state scope site source arms)
      (appendOperators graph added ops) graph.nodes.length raw added
      (injectSource inputs state scope source arms packet)) := by
  dsimp only
  let packet := receiver_packet inputs registry resolution leaves children request declarations
    callee function returned original current compatible challenge domain raw executed
    interface projection state scope source read
  have cancel {a b : Catalogue (RawObservation s)} (same : a = b)
      (packet : Packet b raw) : same ▸ (same.symm ▸ packet) = packet := by
    cases same
    rfl
  have transport : agreement ▸ (agreement.symm ▸ packet) = packet := cancel agreement packet
  obtain ⟨result, _⟩ := OriginalSourceUnionConsumerR338.primitive_result_fields inputs state
    scope graph old ops site left right source arms intro found agreement raw
    (agreement.symm ▸ packet) licensed
  rw [transport] at result
  exact ⟨result⟩

/-- Application at the original R159 computation-check edge. The complete
source trace premise of R293 is now derived from the same receiver. Annotation
alternatives, source children and admission are not changed or asserted here.
The original target Checking is still a genuine separate parent obligation. -/
theorem receiver_app_result (readout : RuntimeReadout s View) (ports : PortReadout s View)
    (checks : Declarations inputs registry) (kernel : Kernel (Payload s View))
    (environment : Environment (Payload s View)) (annotation : Option Annotation)
    (occurrence : Nat) (data : Logical s View) (state : Decoded s View)
    (decoded : decode readout environment = some state) (arms : List Endpoint)
    (read : (state.logical data).interfaces ⟨request.original.site, .callableImage⟩ = interface)
    (checked : Checking (OriginalSourceChecking.kernel inputs registry checks
      (environmentReading inputs readout ports) kernel)
      (environment.extend ⟨request.original.site, .viewLogic, 0⟩
        (scopeCandidate environment occurrence (.logical .viewLogic data)))
      ⟨.computation, request.original.site, request.original.context, ⟨request.original.site, .callableImage⟩, ⟨request.original.site, .synthesis⟩⟩) :
    (unionBody inputs (state.logical data) ⟨request.original.site, .callableImage⟩ arms raw).Holds
      (Meaning inputs) ∧
    Meaning inputs (.trace (raw.atInterface ((state.logical data).interfaces ⟨request.original.site, .synthesis⟩))) := by
  apply app_result_pair inputs registry readout ports checks kernel environment request.original.context ⟨request.original.site, annotation⟩
    occurrence data state decoded arms raw checked
  rw [read]
  exact receiver_trace inputs registry resolution leaves children request declarations
    callee function returned original current compatible challenge domain raw executed interface projection

end Receiver
end YulangClosure.OriginalDeclaredUnionR339
