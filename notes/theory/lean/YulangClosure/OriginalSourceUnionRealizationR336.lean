import YulangClosure.OriginalSourceScopedInterpretationR335

/-!
R336: an actual source-owned branch packet and argument-child application.

EI-All's ArmDecl insertion/use inventory is not emitted by the source syntax
inventory. No list of semantic arms, primitive license or EI interpretation is
invented here. Instead the actual tick argument is read from R335's authentic
Call, its original formal binding is computed, and the existing original Name
interpretation is applied at the SAME R159 ViewLogic extension. Complete Return
fields supply the actual R293 branch catalogue. This is an argument Name leaf,
not the whole Call source tag and not a licensed R306 child.

The parent application uses the EXISTING foldedNameKernel interpretation;
it does not claim equality with an arbitrary independent source kernel.
-/
namespace YulangClosure.OriginalSourceUnionRealizationR336

open OriginalSource OriginalScopedClosure OriginalSourceInterpretation
open OriginalSourceEnvironment OriginalSourceChecking
open ComputedCallTypedFormationR310 OriginalSourceScopedInterpretationR335
open OriginalSourceContractResolutionR311

variable {s : Sorts} {View : Type}

/-- Exact formal selected by the actual make initializer, including entry
and single-use facts computed by original source generation. -/
def seedBinding : Binding :=
  {name := 1, owner := 41, kind := .formal, entry := some .value, singleUse := true}

def seedReference (origin : Declaration) : NameReference :=
  ⟨programPosition (tickRequest origin).original.argument, 5,
    (tickRequest origin).original.context, 1, seedBinding⟩

theorem seed_original_reference (origin : Declaration) :
    nameReference ⟨(tickRequest origin).original.argument, []⟩ =
      some (seedReference origin) := by
  with_unfolding_all rfl

theorem seed_original_binding (origin : Declaration) :
    lookupBinding (tickRequest origin).original.context 1 = some seedBinding := by
  with_unfolding_all rfl

/-- The scoped child and inert-argument code are identical; the local CalRet
binder is retained and is not confused with an actual returned event. -/
theorem seed_original_child (origin : Declaration) :
    (tickRequest origin).original.argument.erase =
      sourceRules (tickRequest origin).original.context (.name ⟨5, none⟩ 1) ∧
    (tickRequest origin).operands.argument.original =
      (tickRequest origin).original.argument ∧
    (tickRequest origin).operands.argument.reference.key.scope =
      [.calRet (tickRequest origin).original.position] := by
  with_unfolding_all exact ⟨rfl, rfl, rfl⟩

/-- Source construction from raw original installed-binding equations. No
desired source judgment, checking judgment or descriptor membership is input.
The independent source Name interpretation is the existing folded kernel. -/
theorem seed_source_from_binding (inputs : Inputs s)
    (readout : RuntimeReadout s View) (original : Kernel (Payload s View))
    (environment : Environment (Payload s View)) (state : Decoded s View)
    (decoded : decode readout environment = some state) (origin : Declaration)
    (address : Nat) (atName : state.assignment.binding 1 = some address)
    (bound : address < inputs.installedCount state.assignment.event)
    (found : inputs.installed state.assignment.event address =
      some (.value (state.assignment.descriptor ⟨5, .finalRoot⟩)
        (state.assignment.value ⟨5, .finalRoot⟩) (state.assignment.root ⟨5, .finalRoot⟩))) :
    SourceJudgment (foldedNameKernel inputs readout original 5 1) environment
      (tickRequest origin).original.context (.name ⟨5, none⟩ 1) := by
  apply (source_reconstruction _ _ _ _).mp
  exact formal_name_from_raw_binding inputs readout original environment state decoded
    (tickRequest origin).original.context 5 1 seedBinding
    (seed_original_binding origin) rfl rfl address atName bound found

/-- Exact reduction, including the converse: the source child contains the
same decoded state and actual installed binding, not an extra assumption. -/
theorem seed_source_iff_binding (inputs : Inputs s)
    (readout : RuntimeReadout s View) (original : Kernel (Payload s View))
    (environment : Environment (Payload s View)) (origin : Declaration) :
    SourceJudgment (foldedNameKernel inputs readout original 5 1) environment
      (tickRequest origin).original.context (.name ⟨5, none⟩ 1) ↔
    ∃ (state : Decoded s View) (address : Nat),
      decode readout environment = some state ∧
      state.assignment.binding 1 = some address ∧
      address < inputs.installedCount state.assignment.event ∧
      inputs.installed state.assignment.event address =
        some (.value (state.assignment.descriptor ⟨5, .finalRoot⟩)
          (state.assignment.value ⟨5, .finalRoot⟩) (state.assignment.root ⟨5, .finalRoot⟩)) := by
  constructor
  · intro proof
    simp only [SourceJudgment, sourceRules, seed_original_binding, Option.map_some,
      seedBinding] at proof
    cases proof with
    | rule locals _ =>
      have first := locals _ (List.mem_cons_self ..)
      cases first with
      | atom valid =>
        simp only [foldedNameKernel, atom, valueFormalAtom] at valid
        simp only [beq_self_eq_true, Bool.and_self, reduceCtorEq, true_or,
          and_self, ite_true] at valid
        obtain ⟨state, decoded, name, address, names, atName, bound, found⟩ := valid
        cases names
        exact ⟨state, address, decoded, atName, bound, found⟩
  · rintro ⟨state, address, decoded, atName, bound, found⟩
    exact seed_source_from_binding inputs readout original environment state decoded
      origin address atName bound found

/-- The primitive atom is outside the selected Name interpreter. This exact
independent primitive law remains the original one. -/
theorem seed_kernel_keeps_tick (inputs : Inputs s)
    (readout : RuntimeReadout s View) (original : Kernel (Payload s View))
    (environment : Environment (Payload s View)) (origin : Declaration) :
    (foldedNameKernel inputs readout original 5 1).atom environment
        (tickPrimitive origin).data ↔
      original.atom environment (tickPrimitive origin).data := by
  simp only [foldedNameKernel, ScopedPrimitive.data, tickPrimitive, atom]
  simp

/-- Exact parent equivalence in the existing folded Name instance. No source
child is assumed on the right, and no raw-binding premise is strengthened.
The independent original kernel and all its non-Name laws are unchanged. -/
theorem tick_parent_iff_raw_argument (inputs : Inputs s)
    (readout : RuntimeReadout s View) (original : Kernel (Payload s View))
    (environment : Environment (Payload s View)) (origin : Declaration) :
    SourceJudgment (foldedNameKernel inputs readout original 5 1) environment
      (tickRequest origin).original.context
      (.app ⟨3, none⟩ (.primitive ⟨4, none⟩ 12) (.name ⟨5, none⟩ 1)) ↔
    ∃ candidate, original.admitted environment ⟨3, .viewLogic, 0⟩ candidate ∧
      let after := environment.extend ⟨3, .viewLogic, 0⟩ candidate
      (∀ premise ∈ SourceAppAdmissionR159.appPremises
        (tickRequest origin).original.context ⟨3, none⟩
        (.primitive ⟨4, none⟩ 12) (.name ⟨5, none⟩ 1),
        Local (foldedNameKernel inputs readout original 5 1) after premise) ∧
      original.atom after (tickPrimitive origin).data ∧
      ∃ (state : Decoded s View) (address : Nat),
        decode readout after = some state ∧
        state.assignment.binding 1 = some address ∧
        address < inputs.installedCount state.assignment.event ∧
        inputs.installed state.assignment.event address =
          some (.value (state.assignment.descriptor ⟨5, .finalRoot⟩)
            (state.assignment.value ⟨5, .finalRoot⟩) (state.assignment.root ⟨5, .finalRoot⟩)) := by
  rw [tick_app_parent_iff]
  apply exists_congr
  intro candidate
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  exact and_congr (seed_kernel_keeps_tick inputs readout original _ origin)
    (seed_source_iff_binding inputs readout original _ origin)

/-- Apply the constructed actual argument child to the unchanged R159 App
rule. Both child SourceJudgments have disappeared: the primitive retains its
original atom, the Name uses raw original binding equations. All original
App locals, admission and the SAME candidate extension remain explicit.
This specializes R159 to its existing folded-Name interpretation only. -/
theorem tick_parent_from_raw_argument (inputs : Inputs s)
    (readout : RuntimeReadout s View) (original : Kernel (Payload s View))
    (environment : Environment (Payload s View)) (origin : Declaration)
    (candidate : ScopedValue (Payload s View))
    (admitted : original.admitted environment ⟨3, .viewLogic, 0⟩ candidate)
    (state : Decoded s View)
    (decoded : decode readout (environment.extend ⟨3, .viewLogic, 0⟩ candidate) = some state)
    (address : Nat) (atName : state.assignment.binding 1 = some address)
    (bound : address < inputs.installedCount state.assignment.event)
    (found : inputs.installed state.assignment.event address =
      some (.value (state.assignment.descriptor ⟨5, .finalRoot⟩)
        (state.assignment.value ⟨5, .finalRoot⟩) (state.assignment.root ⟨5, .finalRoot⟩)))
    (locals : ∀ premise ∈ SourceAppAdmissionR159.appPremises
      (tickRequest origin).original.context ⟨3, none⟩
      (.primitive ⟨4, none⟩ 12) (.name ⟨5, none⟩ 1),
      Local (foldedNameKernel inputs readout original 5 1)
        (environment.extend ⟨3, .viewLogic, 0⟩ candidate) premise)
    (primitive : original.atom (environment.extend ⟨3, .viewLogic, 0⟩ candidate)
      (tickPrimitive origin).data) :
    SourceJudgment (foldedNameKernel inputs readout original 5 1) environment
      (tickRequest origin).original.context
      (.app ⟨3, none⟩ (.primitive ⟨4, none⟩ 12) (.name ⟨5, none⟩ 1)) := by
  apply (tick_app_parent_iff _ environment origin).mpr
  refine ⟨candidate, admitted, locals, ?_, ?_⟩
  · exact (seed_kernel_keeps_tick inputs readout original _ origin).mpr primitive
  · exact seed_source_from_binding inputs readout original _ state decoded origin
      address atName bound found

/-- Actual original full Return interpretation: original world, same event,
independently installed Value, all hard guards and all hereditary fields.
No source execution sample supplies these universal semantic leaves. -/
theorem seed_return_meaning (inputs : Inputs s) (state : Decoded s View)
    (address : Nat) (world : Meaning inputs (.world state.assignment.event))
    (found : inputs.installed state.assignment.event address =
      some (.value (state.assignment.descriptor ⟨5, .finalRoot⟩)
        (state.assignment.value ⟨5, .finalRoot⟩) (state.assignment.root ⟨5, .finalRoot⟩)))
    (raw : RawObservation s) (sameEvent : raw.event = state.assignment.event)
    (form : inputs.traceForm (raw.atInterface (state.interfaces ⟨5, .synthesis⟩)) =
      .pureReturn (state.assignment.row 5))
    (guards : (inputs.observationGuards
      (raw.atInterface (state.interfaces ⟨5, .synthesis⟩))).Valid)
    (fields : (inputs.observationFields
      (raw.atInterface (state.interfaces ⟨5, .synthesis⟩))).Holds (Meaning inputs)) :
    Meaning inputs (.trace (raw.atInterface (state.interfaces ⟨5, .synthesis⟩))) := by
  have value := formal_name_value_from_raw_binding inputs state 5 address world found
  apply (return_observation_iff inputs _ _ form).mpr
  refine ⟨?_, guards, ?_, ⟨sameEvent.symm, value⟩, fields⟩
  · simpa only [RawObservation.atInterface, sameEvent] using ((world_unfold inputs _).mp world).1
  · simpa only [RawObservation.atInterface, sameEvent] using world

/-- The packet inhabits the actual R293 complete branch catalogue at the
source-owned scoped Name endpoint. No Union/arm list or license is supplied. -/
theorem seed_branch_packet (inputs : Inputs s) (state : Decoded s View)
    (origin : Declaration) (address : Nat)
    (world : Meaning inputs (.world state.assignment.event))
    (found : inputs.installed state.assignment.event address =
      some (.value (state.assignment.descriptor ⟨5, .finalRoot⟩)
        (state.assignment.value ⟨5, .finalRoot⟩) (state.assignment.root ⟨5, .finalRoot⟩)))
    (raw : RawObservation s) (sameEvent : raw.event = state.assignment.event)
    (form : inputs.traceForm (raw.atInterface (state.interfaces ⟨5, .synthesis⟩)) =
      .pureReturn (state.assignment.row 5))
    (guards : (inputs.observationGuards
      (raw.atInterface (state.interfaces ⟨5, .synthesis⟩))).Valid)
    (fields : (inputs.observationFields
      (raw.atInterface (state.interfaces ⟨5, .synthesis⟩))).Holds (Meaning inputs)) :
    Nonempty (SourceContributionConstruction.Packet
      (ComputedCallUnionRealizationR293.branchCatalogue inputs state
        (binderTelescope (seedReference origin).position) ⟨5, .synthesis⟩) raw) := by
  have member := seed_return_meaning inputs state address world found raw sameEvent form guards fields
  exact ⟨ComputedCallUnionClausesR308.sourcePacket inputs state
    (binderTelescope (seedReference origin).position) ⟨5, .synthesis⟩ raw member⟩

end YulangClosure.OriginalSourceUnionRealizationR336
