import YulangClosure.OriginalCalleeArgumentHistoryR312
import YulangClosure.OriginalComputedCallInterpretationR311

namespace R312ParentApplication
open YulangClosure
open OriginalSource OriginalScopedClosure OriginalSourceInterpretation
open OriginalSourceEnvironment OriginalSourceChecking
open OriginalCalleeArgumentHistoryR312
open ComputedCallTypedFormationR310

abbrev sourceCall (call : ComputedCallTypedFormationR310.CallRecord) : CallOccurrence :=
  ⟨call.position, call.site, call.context, call.premises, call.callee, call.argument⟩


def actualBoundReturn {b : Sorts} {C Dict Rest Schema Body View : Type}
    (p : Preparation b C Dict Rest Schema Body View) (call : Position)
    (observation : (OriginalNameForceExtraction.Base b).Observation)
    (received : SourceIdentityWorld.Received Nat) (descriptor : b.Descriptor)
    (providers : Site → b.Provider) (provider : OriginalCalleeDelayProvenance.RuntimeValue) :
    OriginalComputedCallInterpretationR311.BoundReturn (S b C Rest Body View) call :=
  ⟨⟨observation, p.calRet⟩,
    ⟨descriptor, p.calRet.eta.views.value received.value,
      p.calRet.eta.views.root received.value, p.calRet⟩,
    providers provider.source⟩

section Application
variable {b : Sorts} {C Dict Rest Schema Body View : Type}
variable (p : Preparation b C Dict Rest Schema Body View) (caller : BoundCaller p)
variable (base : Inputs (S b C Rest Body View))
variable (native : OriginalNameForceExtraction.Native b (OriginalValueEntryDemand.Dispatch C)
  OriginalCalleeDelayProvenance.Metadata Rest Body View)
variable (references : Body → Nat → Option Name) (interface : b.Interface)
variable (plain : native.dispatch = OriginalNameForceExtraction.noDictionaries)
variable (surrounding : Surrounding p caller (OriginalNameForceExtraction.inputs base native) references interface)
variable (reads : ∀ event, OriginalIdentityCarrier.Reach (OriginalNameForceExtraction.inputs base native) p.event event →
  NativeRead p caller native interface event)
variable (prefixes : ∀ event, OriginalIdentityCarrier.Reach (OriginalNameForceExtraction.inputs base native) p.event event →
  ∀ demand, ((OriginalNameForceExtraction.inputs base native)).demand ((p.row interface).atEvent event) demand →
    PrefixFields p base native references interface demand)
variable (request : Request) (sameCall : sourceCall request.original = p.apply.call)
variable (observation : (OriginalNameForceExtraction.Base b).Observation)
variable (received : SourceIdentityWorld.Received Nat) (descriptor : b.Descriptor)
variable (providers : Site → b.Provider) (provider : OriginalCalleeDelayProvenance.RuntimeValue)
local notation "returned" => actualBoundReturn p request.original.position observation received descriptor providers provider
variable (registry : GuardRegistry (OriginalParameterSemantics.inputs (OriginalNameForceExtraction.inputs base native) references))
variable (resolution : OriginalComputedCallInterpretationR311.Resolution (OriginalParameterSemantics.inputs (OriginalNameForceExtraction.inputs base native) references) registry)
variable (declarations : OriginalComputedCallInterpretationR311.PrimitiveDeclarations)
local notation "reifyGoal" => OriginalComputedCallInterpretationR311.primitiveGoal request declarations OriginalComputedCallInterpretationR311.Use.reify
  (OriginalComputedCallInterpretationR311.returnedOperands returned ++ [Operand.carrier (p.row interface)])
include caller plain surrounding reads prefixes sameCall

/-- R311's actual argument edge only; no Call judgment, independent arm law,
q_c, source typing or complete History/NativeExtraction is assumed/concluded. -/
theorem r311_argument_from_actual_preparation
    (provided : (OriginalWorldReadout.vectorStore (p.raw.values.map some)).cell received.value = some provider)
    (leaf : OriginalComputedCallInterpretationR311.PrimitiveLeaf (OriginalParameterSemantics.inputs (OriginalNameForceExtraction.inputs base native) references) registry reifyGoal)
    (found : resolution reifyGoal = some leaf)
    (before : leaf.entry.before.Holds (OriginalParameterSemantics.inputs (OriginalNameForceExtraction.inputs base native) references) registry.original) :
    p.apply.call.position = request.original.position ∧
    p.returned observation received descriptor providers = some
      ((returned).callee, (returned).value, (returned).provider) ∧
    (returned).callee.event = p.calRet ∧ (returned).value.event = p.calRet ∧
    (OriginalComputedCallInterpretationR311.argumentBody (OriginalParameterSemantics.inputs (OriginalNameForceExtraction.inputs base native) references) registry resolution request declarations
      returned (p.row interface)).Holds (Meaning (OriginalParameterSemantics.inputs (OriginalNameForceExtraction.inputs base native) references)) := by
  refine ⟨(congrArg CallOccurrence.position sameCall).symm,
    actual_return_same_event p observation received descriptor providers provider provided, rfl, rfl, ?_⟩
  exact OriginalComputedCallInterpretationR311.argument_introduction (OriginalParameterSemantics.inputs (OriginalNameForceExtraction.inputs base native) references) registry resolution request
    declarations _ (p.row interface) leaf found before
    (carrier_from_original_leaves p caller base native references interface plain surrounding reads prefixes)



/-- R293 applies to the actual Name Force branch, not to the missing complete
Call result. The arbitrary ORIGINAL arms list is retained in the catalogue;
source injection supplies no independent arm law, q_c or child license. -/
theorem r293_name_force_source_packet
    (scope : List Binder) (state : Decoded (S b C Rest Body View) View)
    (arms : List Endpoint)
    (slot : interface = state.interfaces ⟨p.nameSite, .synthesis⟩)
    (demanded : (OriginalParameterSemantics.inputs (OriginalNameForceExtraction.inputs base native) references).demand
      (p.row interface) p.event)
    (handle : native.handle (p.row interface).input.carrier = some p.delay.handle)
    (snapshot : native.executables p.event = delaySnapshot p.post)
    (mode : OriginalNameForceExtraction.NameMode)
    (modeFound : native.nameMode p.event p.delay.handle = some mode)
    (lexical : mode.lexicalObserve = true) (n : Nat) :
    let raw := OriginalNameForceExtraction.observe native (p.row interface).input p.event p.delay (n + 2)
    Nonempty (SourceContributionConstruction.Packet
      (ComputedCallUnionRealizationR293.unionCatalogue
        (OriginalParameterSemantics.inputs (OriginalNameForceExtraction.inputs base native) references)
        state scope ⟨p.nameSite, .synthesis⟩ arms) raw) := by
  dsimp only
  let raw := OriginalNameForceExtraction.observe native (p.row interface).input p.event p.delay (n + 2)
  have whole := carrier_from_original_leaves p caller base native references interface plain surrounding reads prefixes
  have computed := caller_force_return p caller base native interface handle snapshot mode modeFound lexical plain n
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

end Application

#check @r311_argument_from_actual_preparation
#print axioms r311_argument_from_actual_preparation
#check @r293_name_force_source_packet
#print axioms r293_name_force_source_packet
#check @YulangClosure.SourceAppAdmissionR159.app_admission_iff
#print axioms YulangClosure.SourceAppAdmissionR159.app_admission_iff
#check @YulangClosure.ComputedCallUnionRealizationR293.app_result_pair
#print axioms YulangClosure.ComputedCallUnionRealizationR293.app_result_pair
end R312ParentApplication
