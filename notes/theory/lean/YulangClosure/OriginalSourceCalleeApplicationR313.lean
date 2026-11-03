import YulangClosure.OriginalSourceCalleeWitnessR313
import YulangClosure.OriginalCalleeArgumentApplicationR312

namespace R313ParentApplication
open YulangClosure
open OriginalSource OriginalScopedClosure OriginalSourceInterpretation
open OriginalSourceEnvironment OriginalSourceChecking OriginalWorldReadout
open NativeClosureEnvironment SourceIdentityWorld OriginalParameterSemantics
open OriginalCalleeArgumentHistoryR312 OriginalSourceCalleeWitnessR313
variable {b : Sorts} {C Dict Rest Schema Body View : Type}

def toOriginal {s : Sorts} {call : Position} (fields : ReturnFields s call) :
    OriginalComputedCallInterpretationR311.BoundReturn s call :=
  ⟨fields.callee, fields.value, fields.provider⟩

/-- Applying the raw same-return witness to R311 still requires the ORIGINAL
callee membership, Return-form interpretation, checked Function transport and
actual-provider relation. A native closure tag proves none of these leaves. -/
theorem r311_calRet_from_actual_witness
    (p : Preparation b C Dict Rest Schema Body View)
    (received : Received Nat) (tail : List OriginalCalleeArgumentHistoryR312.Frame)
    (observation : (OriginalNameForceExtraction.Base b).Observation)
    (descriptor : b.Descriptor) (providers : Site → b.Provider)
    (provider : OriginalCalleeDelayProvenance.RuntimeValue)
    (view : SourceIdentityWorld.View Nat OriginalCalleeDelayProvenance.Metadata)
    (closure : OriginalValueEntryDemand.Closure Schema)
    (provided : (vectorStore (p.raw.values.map some)).cell received.value = some provider)
    (viewFound : (vectorStore (p.raw.views.map some)).cell received.view = some view)
    (matching : view.value = received.value)
    (executable : p.raw.executables received.value = some (.closure closure))
    (inputs : Inputs (S b C Rest Body View)) (registry : GuardRegistry inputs)
    (leaves : Positive (S b C Rest Body View) → Positive (S b C Rest Body View) → Prop)
    (children : ∀ A B, leaves A B → A.Holds (Meaning inputs) → B.Holds (Meaning inputs))
    (callee : b.Interface) (function : b.Descriptor)
    (member : Meaning inputs (.trace
      ((R312ParentApplication.actualBoundReturn p p.apply.call.position observation received descriptor providers provider).callee.atInterface callee)))
    (form : inputs.traceForm
      ((R312ParentApplication.actualBoundReturn p p.apply.call.position observation received descriptor providers provider).callee.atInterface callee) =
      .pureReturn (R312ParentApplication.actualBoundReturn p p.apply.call.position observation received descriptor providers provider).value)
    (checked : Proof inputs registry leaves
      (.field (.value (R312ParentApplication.actualBoundReturn p p.apply.call.position observation received descriptor providers provider).value))
      (.field (.value ((R312ParentApplication.actualBoundReturn p p.apply.call.position observation received descriptor providers provider).value.withDescriptor function))))
    (functionSort : inputs.valueForm function = .function)
    (actual : inputs.actual (p.calRet.eta.views.value received.value)
      (p.calRet.eta.views.root received.value) (providers provider.source)) :
    Option.map toOriginal (calleeWitness p ⟨⟨.returned received, .callee p.saved :: tail⟩⟩ observation descriptor providers) =
      some (R312ParentApplication.actualBoundReturn p p.apply.call.position observation received descriptor providers provider) ∧
    (OriginalComputedCallInterpretationR311.calRetBody inputs callee function
      (R312ParentApplication.actualBoundReturn p p.apply.call.position observation received descriptor providers provider)).Holds (Meaning inputs) := by
  constructor
  · rw [(actual_callee_witness p received tail observation descriptor providers provider view closure provided viewFound matching executable).1]
    rfl
  · exact OriginalComputedCallInterpretationR311.calRet_introduction inputs registry leaves children callee function _
      member form checked functionSort actual

section NameConsumer
variable (arena : Arena) (a : SourceApply arena)
variable (p : Preparation b C Dict Rest Schema Body View)
variable (program : p.raw.program = arena.program)
variable (sameApply : p.apply = a.toApplySource arena p.raw program)
variable (instruction : a.argumentCode.instruction = .name p.name ⟨.parameter, .observe⟩)
variable (caller : BoundCaller p) (base : Inputs (S b C Rest Body View))
variable (native : OriginalNameForceExtraction.Native b (OriginalValueEntryDemand.Dispatch C)
  OriginalCalleeDelayProvenance.Metadata Rest Body View)
variable (references : Body → Nat → Option Name) (interface : b.Interface)
variable (plain : native.dispatch = OriginalNameForceExtraction.noDictionaries)
variable (surrounding : Surrounding p caller (OriginalNameForceExtraction.inputs base native) references interface)
variable (reads : ∀ event, OriginalIdentityCarrier.Reach (OriginalNameForceExtraction.inputs base native) p.event event →
  NativeRead p caller native interface event)
variable (prefixes : ∀ event, OriginalIdentityCarrier.Reach (OriginalNameForceExtraction.inputs base native) p.event event →
  ∀ demand, (OriginalNameForceExtraction.inputs base native).demand ((p.row interface).atEvent event) demand →
    PrefixFields p base native references interface demand)

include a program sameApply instruction caller plain surrounding reads prefixes

/-- Genuine R293 injection at the original Name slot with arbitrary original
arms. The exact source instruction establishes Observe; independent all-Reach
world/license/prefix leaves remain explicit, as do Call q_c/Checking/admission. -/
theorem r293_name_force_from_source
    (scope : List Binder) (state : Decoded (S b C Rest Body View) View)
    (arms : List Endpoint)
    (slot : interface = state.interfaces ⟨p.nameSite, .synthesis⟩)
    (demanded : (OriginalParameterSemantics.inputs (OriginalNameForceExtraction.inputs base native) references).demand
      (p.row interface) p.event)
    (handle : native.handle (p.row interface).input.carrier = some p.delay.handle)
    (snapshot : native.executables p.event = delaySnapshot p.post)
    (modeRead : native.nameMode p.event p.delay.handle = modeAt arena p.post p.delay.handle)
    (n : Nat) :
    let raw := OriginalNameForceExtraction.observe native (p.row interface).input p.event p.delay (n + 2)
    Nonempty (SourceContributionConstruction.Packet
      (ComputedCallUnionRealizationR293.unionCatalogue
        (OriginalParameterSemantics.inputs (OriginalNameForceExtraction.inputs base native) references)
        state scope ⟨p.nameSite, .synthesis⟩ arms) raw) := by
  dsimp only
  let raw := OriginalNameForceExtraction.observe native (p.row interface).input p.event p.delay (n + 2)
  have whole := carrier_from_original_leaves p caller base native references interface plain surrounding reads prefixes
  have computed := caller_force_return p caller base native interface handle snapshot ⟨.parameter, .observe⟩
    (modeRead.trans (allocated_observe_mode arena a p program sameApply p.name instruction)) rfl plain n
  have designated := OriginalComputedCallInterpretationR311.designated_force_from_carrier
    (OriginalParameterSemantics.inputs (OriginalNameForceExtraction.inputs base native) references)
    (p.row interface) p.event raw whole demanded computed.1
  have member : Meaning
      (OriginalParameterSemantics.inputs (OriginalNameForceExtraction.inputs base native) references)
      (.trace (raw.atInterface (state.interfaces ⟨p.nameSite, .synthesis⟩))) := by
    rw [← slot]
    exact (meaning_clause _ _).mpr designated.2.2
  let packet := ComputedCallUnionClausesR308.sourcePacket
    (OriginalParameterSemantics.inputs (OriginalNameForceExtraction.inputs base native) references)
    state scope ⟨p.nameSite, .synthesis⟩ raw member
  exact ⟨ComputedCallUnionRealizationR293.injectSource
    (OriginalParameterSemantics.inputs (OriginalNameForceExtraction.inputs base native) references)
    state scope ⟨p.nameSite, .synthesis⟩ arms packet⟩
end NameConsumer

#check @R313ParentApplication.r311_calRet_from_actual_witness
#print axioms R313ParentApplication.r311_calRet_from_actual_witness
#check @R313ParentApplication.r293_name_force_from_source
#print axioms R313ParentApplication.r293_name_force_from_source
#check @YulangClosure.SourceAppAdmissionR159.app_admission_iff
#print axioms YulangClosure.SourceAppAdmissionR159.app_admission_iff
#check @YulangClosure.ComputedCallUnionRealizationR293.app_result_pair
#print axioms YulangClosure.ComputedCallUnionRealizationR293.app_result_pair
end R313ParentApplication
