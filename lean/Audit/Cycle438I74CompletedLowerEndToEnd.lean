import Yulang.GeneralDeclarativeI65I74CompletedLowerEntry438
import Yulang.GeneralDeclarativeWitnessVarianceFixtures357

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 14000
set_option maxHeartbeats 1800000
namespace Yulang.C438CompletedEntryAudit
open GeneralDeclarativeWitnessConstructorModes357
open GeneralDeclarations (Declaration Equation)
open GeneralSourceMetadataRows291 (Row)
open GeneralSourceMetadataBareBundle291 (InputBundle)

def seedBody : Equation := ⟨80,6,.app 20 [.var 8]⟩
def seed : Declaration := ⟨701,11,[.app 20 [.var 8]],[],[seedBody],[]⟩
def observe : Declaration := ⟨702,22,[.app 20 [.var 9]],[],[],[]⟩
def bundle (snapshotClass : GeneralSourceMetadataRows291.Class) (duplicate := false) : InputBundle :=
  let originals : List Row := [⟨20,some ⟨[.type],20⟩,.unclassified⟩]
  let snapshot : List Row := [⟨20,some ⟨[.type],20⟩,snapshotClass⟩]
  ⟨⟨.absent,originals⟩,⟨.absent,snapshot⟩,
     ⟨1,[⟨11,1,[(6,none)]⟩,⟨22,1,[]⟩]⟩, if duplicate then [seed,observe,observe] else [seed,observe]⟩

def env? (data : InputBundle) : Option Environment := do
  let source := GeneralDeclarativeWitnessVarianceFixtures357.source
  let graph ← GeneralDeclarativeWitnessSparseVariance357.compile source
  let book ← GeneralSourceMetadataBareBundle291.compile data
  return ⟨3,2,0,source,graph,book⟩

def native : Environment := (env? (bundle .unclassified)).get (by decide +kernel)
open GeneralDeclarativeI65
open GeneralDeclarativeI65.CompletedLower437
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry point)
open GeneralDictionaryAssociatedProvenance (Body lookup lookup_exact)
open GeneralDeclarativeOutputs320 (bodyPattern)
open GeneralDeclarationPatterns (normalize)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeEmissionForest322 (Placement)
open CommonDeclaredNominalInspection (Parameter)
open CommonNominalFullCarrier (Equivalent nominal subtype_refl)
open CommonRecursiveNominalIntervals (Endpoint)
open GeneralDeclarativeI65.I72 (fixedValueCode403)

def output0 : GeneralDeclarativeHead320.Equation := ⟨40,.nominal 20 [.variable 30]⟩
def decoy : GeneralDeclarativeHead320.Equation := ⟨40,.nominal 20 [.variable 32]⟩
def reflAtom : PresenceNormalForm.Atom Nat := .tyLe (.var 30) (.var 30)
def atoms : List (PresenceNormalForm.Atom Nat) :=
  [reflAtom,.tyLe (.var 30) (.var 32),.tyLe (.var 32) (.var 34),
    .tyLe (.var 30) (.var 34),.tyLe (.var 40) (.var 41),.tyLe (.var 41) (.var 42)]
def raw : GeneralDeclarativeHead320.State := ⟨⟨atoms,[]⟩,[output0,decoy]⟩
def nativeOrigin : Endpoint Nat := .nominal 20 [.inl (.point (.ordinary (.var 30)))]
def coValue : Parameter := ⟨.value,.covariant⟩
def opened : List Origin := [⟨10,[101],nativeOrigin⟩,
  ⟨41,[202],I72.unaryNominalPoint404 20 32⟩,⟨42,[303],I72.unaryNominalPoint404 20 34⟩,
  ⟨41,[999],I72.unaryNominalPoint404 20 32⟩]
def core : State := ⟨⟨native,raw,[]⟩,List.replicate 20 [] ++ [[coValue]],opened,[]⟩
def seedRequest : Request := ⟨[101],⟨11,[point 10],[⟨6,40⟩]⟩⟩
def seedIndex : Fin seedRequest.demand.outputs.length := ⟨0,by decide⟩
def mode : Use native 20 1 := (readUse native 20 1).get (by decide +kernel)
def originalBody : Body := .explicit seedBody

def originalPlan : B6MixedRhs401 core false (normalize (bodyPattern originalBody)) :=
  .declaredApp (params := [coValue]) 20 mode (by decide +kernel) (by decide +kernel)
    (.cons (.valuePoint 8 rfl (by decide +kernel) ()) .nil)

def atlas : B6OccurrenceAtlas401 core :=
  ⟨fun q d i b =>
    match q.demand.arguments, q.demand.outputs with
    | [a],[o] =>
      if q.occurrence = [101] ∧ q.demand.role = 11 ∧ a.lower = 10 ∧ a.center = 10 ∧ a.upper = 10 ∧
          o.name = 6 ∧ o.target = 40 ∧ d = 0 ∧ i.val = 0 then
        if source : b = originalBody then some (source.symm ▸ originalPlan) else none
      else none
    | _,_ => none⟩


open GeneralDeclarativeI65.I72
open GeneralDeclarativeI65.I72.CompletedEntry438
open Checker408 (Problem Result)

def logicalState : I72.State := ⟨core,atlas⟩
def asked : GeneralDeclarativeWhere319.Capture := ⟨40,41,42⟩
def query : GeneralDeclarativeI65.Request := ⟨[202],⟨22,[asked],[]⟩⟩
def problem : Problem := ⟨logicalState,query⟩
def desired : Result := ⟨.selected observe.id [],.selected (.node observe.id []),[]⟩

def producerEscape : List410.ExactEscapeWire :=
  ⟨(List.range 43).map (fun n => if n=10 then 0 else 1),[0,2]⟩

def observerEscape : List410.ExactEscapeWire :=
  ⟨(List.range 43).map (fun n => if n ∈ [40,41,42] then 2 else if n ∈ [30,32,34] then 1 else 0),
    [2,1,0]⟩

def wire : Wire438 := ⟨seedRequest,0,0,producerEscape,2,1,observerEscape⟩

theorem public_entry_accepts_original_completed_lower438 :
    check problem desired (.completedLower wire) = true := by decide +kernel

private theorem capture_from_projections438 (arg : GeneralDeclarativeWhere319.Capture)
    (lo : arg.lower = 30) (mid : arg.center = 32) (hi : arg.upper = 34) :
    arg = ⟨30,32,34⟩ := by
  cases arg
  simp_all

theorem checked_public_path_is_same_B6_source_and_selected_root438 :
    ∃ a : Replay438 logicalState query wire,
      replay438 logicalState query wire = some a ∧
      a.selected.invocation.row = observe ∧
      a.selected.invocation.chosen.producer.event.frame.ordinal = 0 ∧
      a.selected.invocation.chosen.authoredOrdinal = 1 ∧
      a.selected.invocation.chosen.need.ordinal.val = 0 ∧
      a.selected.invocation.chosen.need.producer.occurrence = [101] ∧
      a.selected.head.retained.rowOrdinal = 0 ∧
      a.selected.invocation.chosen.gate.arg.lower = 40 ∧
      a.selected.invocation.frame.input 9 = ⟨30,32,34⟩ ∧
      a.selected.invocation.chosen.gate.upper.issuer = [303] ∧
      a.selected.invocation.actualPayload.source.issuer = [202] := by
  let exact := (replay438 logicalState query wire).get (by decide +kernel)
  have upper : exact.selected.invocation.chosen.gate.upper.issuer = [303] :=
    congrArg Origin.issuer (Option.some.inj exact.actualUpper).symm
  have capture : exact.selected.invocation.frame.input 9 = ⟨30,32,34⟩ := by
    let value := exact.selected.invocation.frame.input 9
    change value = _
    have found : value.lower = 30 ∧ value.center = 32 ∧ value.upper = 34 := by decide +kernel
    exact capture_from_projections438 value found.1 found.2.1 found.2.2
  have lower : exact.selected.invocation.chosen.gate.arg.lower = 40 :=
    congrArg GeneralDeclarativeWhere319.Capture.lower
      (List.cons.inj exact.selected.invocation.chosen.gate.exactArg).1.symm
  have source : exact.selected.invocation.chosen.need.producer.occurrence = [101] :=
    congrArg GeneralDeclarativeI65.Request.occurrence exact.producer
  have proved : exact.selected.invocation.row = observe ∧
      exact.selected.invocation.chosen.producer.event.frame.ordinal = 0 ∧
      exact.selected.invocation.chosen.authoredOrdinal = 1 ∧
      exact.selected.invocation.chosen.need.ordinal.val = 0 := by decide +kernel
  have some_get (o : Option (Replay438 logicalState query wire)) (present : o.isSome) :
      o = some (o.get present) := by
    cases o with
    | none => simp at present
    | some a => rfl
  exact ⟨exact,some_get _ (by decide +kernel),proved.1,proved.2.1,proved.2.2.1,proved.2.2.2,source,exact.keptAt,lower,
    capture,upper,exact.centerIssuer⟩

theorem public_entry_checks_wrong_fixed_row_center_and_request438 :
    check problem desired (.completedLower { wire with seedRetainedRow := 1 }) = false ∧
    check problem desired (.completedLower { wire with seedOrigin := 1 }) = false ∧
    check problem desired (.completedLower { wire with centerOrigin := 3 }) = false ∧
    check problem desired (.completedLower { wire with upperOrigin := 1 }) = false ∧
    check problem desired (.completedLower { wire with producer := { seedRequest with occurrence := [102] } }) = false ∧
    check problem desired (.completedLower { wire with producer := query }) = false ∧
    check problem Check408.rawReport (.completedLower wire) = false ∧
    check problem desired .unsupported = false := by decide +kernel

def actualSeed : SeedReplay438 logicalState wire.producer wire.seedRetainedRow :=
  (replaySeed438 logicalState wire).get (by decide +kernel)

def previousWrite : List Check408.Write :=
  Check408.encodedEventWrites (CompletedSeed437.chosenEvent actualSeed.basis actualSeed.outputs)

theorem original_report_does_not_reissue_producer_or_change_dictionary438 :
    previousWrite.length = 1 ∧
    check problem {desired with writes := previousWrite} (.completedLower wire) = false ∧
    check problem {desired with verdict := .selected (.node seed.id [])} (.completedLower wire) = false ∧
    check problem {desired with tree := .selected seed.id []} (.completedLower wire) = false :=
  by decide +kernel

def withRawCycle : GeneralDeclarativeHead320.State :=
  {raw with equations := raw.equations ++ [⟨30,.variable 40⟩]}

def cyclicCore : GeneralDeclarativeI65.State := {core with current := {core.current with ordinary := withRawCycle}}

def cyclicPlan : B6MixedRhs401 cyclicCore false (normalize (bodyPattern originalBody)) :=
  .declaredApp (params := [coValue]) 20 mode (by decide +kernel) (by decide +kernel)
    (.cons (.valuePoint 8 rfl (by decide +kernel) ()) .nil)

def cyclicAtlas : B6OccurrenceAtlas401 cyclicCore :=
  ⟨fun q d i b =>
    match q.demand.arguments, q.demand.outputs with
    | [a],[o] =>
      if q.occurrence = [101] ∧ q.demand.role = 11 ∧ a.lower = 10 ∧ a.center = 10 ∧ a.upper = 10 ∧
          o.name = 6 ∧ o.target = 40 ∧ d = 0 ∧ i.val = 0 then
        if source : b = originalBody then some (source.symm ▸ cyclicPlan) else none
      else none
    | _,_ => none⟩

def certifiedRawProblem : Problem := ⟨⟨cyclicCore,cyclicAtlas⟩,query⟩
def cycleWire : GeneralDeclarativeWitnessCycle350.Wire := ⟨0,⟨0,.same,30⟩,[],.forward 2⟩
def originalRawWitness : CompletedEntry438.Witness :=
  .previous (.previous (.previous (.previous (.previous (.previous (.previous (.previous (.previous (.previous (.previous (.previous (.previous (.previous (.previous (.previous (.previous (.previous (.rawRoot cycleWire))))))))))))))))))

theorem exact_raw_K2_still_enters_in_original_public_branch438 :
    check certifiedRawProblem desired (.completedLower wire) = false ∧
    check certifiedRawProblem Check408.rawReport originalRawWitness = true ∧
    check problem Check408.rawReport originalRawWitness = false ∧
    List410.checkExactEscape withRawCycle 10 producerEscape = true := by decide +kernel

def sample : GeneralDeclarativeI65.Model :=
  ⟨fun n => ((if n ∈ [10,40,41,42] then nominal 20 [.inl (.base .int)] else .base .int),Common.rowEmpty),
    fun _ => none,fun n =>
      if n=10 then some nativeOrigin
      else if n=41 then some (unaryNominalPoint404 20 32)
      else if n=42 then some (unaryNominalPoint404 20 34)
      else none⟩

theorem original_fixture_fits438 : I72.Fits logicalState sample := by
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  · intro x h
    change x ∈ atoms at h
    simp only [atoms,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl <;> exact subtype_refl _
  · intro x h; change x ∈ [] at h; cases h
  · intro row h
    change row ∈ [output0,decoy] at h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl <;> exact ⟨subtype_refl _,subtype_refl _⟩
  · intro x h; change x ∈ [] at h; cases h
  · intro x h
    change x ∈ opened at h
    simp only [opened,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl <;> rfl


theorem actual_lower_has_no_independent_authored_route438 :
    ∀ origin ∈ core.origins, ¬OriginRoute core origin asked.lower := by
  intro origin present route
  have occurs : core.origins.any (routeMember core asked.lower) = true :=
    List.any_eq_true.mpr ⟨origin,present,actual_route_iff.mpr route⟩
  have absent : core.origins.any (routeMember core asked.lower) = false := by decide +kernel
  rw [absent] at occurs
  cases occurs

theorem public_completed_report_has_one_model_without_authored_lower438 :
    sample.nativeSyntax 40 = none ∧
    R18 logicalState query desired.verdict ∧
    DictionaryEvidence18 logicalState sample query (.node observe.id []) := by
  have claimed := (verified_R18_result_classifies_in_same_State438 problem desired
    (.completedLower wire) public_entry_accepts_original_completed_lower438).1
  have observed := dictionary_sound_R18 _ _ _ claimed sample original_fixture_fits438
  exact ⟨rfl,claimed,observed⟩

#print axioms public_entry_accepts_original_completed_lower438
#print axioms checked_public_path_is_same_B6_source_and_selected_root438
#print axioms public_entry_checks_wrong_fixed_row_center_and_request438
#print axioms original_report_does_not_reissue_producer_or_change_dictionary438
#print axioms exact_raw_K2_still_enters_in_original_public_branch438
#print axioms actual_lower_has_no_independent_authored_route438
#print axioms public_completed_report_has_one_model_without_authored_lower438

end Yulang.C438CompletedEntryAudit
