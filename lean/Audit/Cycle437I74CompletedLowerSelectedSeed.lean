import Yulang.GeneralDeclarativeI65I74CompletedLowerRetained437
import Yulang.GeneralDeclarativeI65I74CompletedLowerNativeHeader437
import Yulang.GeneralDeclarativeWitnessVarianceFixtures357
import Yulang.GeneralDeclarativeI65I72CompletedUnaryGate406
import Yulang.GeneralDeclarativeI65I74ExactEscape410

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 14000
set_option maxHeartbeats 1800000
namespace Yulang.C437SelectedSeed
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
def raw : GeneralDeclarativeHead320.State := ⟨⟨[reflAtom],[]⟩,[output0,decoy]⟩
def nativeOrigin : Endpoint Nat := .nominal 20 [.inl (.point (.ordinary (.var 30)))]
def coValue : Parameter := ⟨.value,.covariant⟩
def core : State := ⟨⟨native,raw,[]⟩,List.replicate 20 [] ++ [[coValue]], [⟨10,[101],nativeOrigin⟩],[]⟩
def seedRequest : Request := ⟨[101],⟨11,[point 10],[⟨6,40⟩]⟩⟩
def seedIndex : Fin seedRequest.demand.outputs.length := ⟨0,by decide⟩
def frame : AuthoredBodyFrame393 core seedRequest :=
  frameAtSource395 (row := seed) (by decide +kernel) 0 (by decide +kernel)
    ⟨fun _ _ => point 0,fun _ _ => 0⟩ (fun n => if n=8 then point 30 else point 0)
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

theorem original_source_capture_is_named437 : frame.slots originalBody 8 = some (point 30) := rfl

def sameNamesWrongOccurrence : Request := ⟨[102],seedRequest.demand⟩

theorem atlas_guards_original_occurrence_and_declaration437 :
    atlas.read seedRequest 0 seedIndex originalBody = some originalPlan ∧
    atlas.read sameNamesWrongOccurrence 0 seedIndex originalBody = none ∧
    atlas.read seedRequest 1 seedIndex originalBody = none := ⟨rfl,rfl,rfl⟩

def selectedRhs : NamedMixedTree401 core (frame.slots originalBody) false (normalize (bodyPattern originalBody)) :=
  .declaredApp (params := [coValue]) 20 mode (by decide +kernel) (by decide +kernel)
    (.cons (.valuePoint 8 rfl (by decide +kernel) ⟨point 30,original_source_capture_is_named437⟩) .nil)

def originalTypedOutput : NamedMixedOutput401 atlas frame seedIndex := by
  have whole := CompletedNativeHeader437.checkedHeader (s := core.current) (by decide +kernel)
  have checked := whole.1.2 frame.decl (List.mem_of_getElem? frame.authored)
  have body : lookup (authoredRegistry core.current).roles frame.decl seedRequest.demand.outputs[seedIndex].name =
      some originalBody := by decide +kernel
  exact ⟨originalBody,(lookup_exact _ _ checked.identified.2.2.1 _ _).mp body,originalPlan,rfl,selectedRhs,rfl⟩


open GeneralDeclarativeI65.I72
open CommonRoleOutermostResolver (Tree Summarizes)
open CommonRecursiveNominalIntervals (ContextWellFormed)
open GeneralDeclarativeWitnessSparseIntervals357 (Legal names visited visitedList)

def logicalState : I72.State := ⟨core,atlas⟩

def seedOrigin : Origin := ⟨10,[101],nativeOrigin⟩

def comparedFromActualMode : DeclaredComparison native raw core.modes false nativeOrigin nativeOrigin := by
  have table : core.modes[20]? = some [coValue] := by decide +kernel
  have key : Legal native core.modes (20,1) := ⟨mode,[coValue],by decide +kernel,table⟩
  have wf : ContextWellFormed core.modes false nativeOrigin :=
    .nominal table (.cons (.valuePoint (.ordinary false (.var 30))) (.nil false))
  refine ⟨?_,wf,wf,.nominal table (.cons (.covariantValue (.ordinary ?_)) .nil)⟩
  · intro site observed
    have hit : site = (20,1) := by simpa [nativeOrigin,visited,visitedList] using observed
    exact hit ▸ key
  · exact List.mem_cons_self

def authoredPointWindow : ModeWindow core (point 10) (.app 20 [.var 8]) :=
  ⟨seedOrigin,seedOrigin,.direct,.direct,List.mem_cons_self,List.mem_cons_self,
    20,[.var 8],rfl,_,_,rfl,rfl,comparedFromActualMode⟩

def realChoice : AuthoredUnaryChoice405 logicalState seedRequest seed := by
  have x := CompletedNativeHeader437.checkedHeader (s := core.current) (by decide +kernel)
  exact ⟨20,8,point 10,rfl,rfl,by decide +kernel,x.1,x.2.1 seed (by decide +kernel),
    mode,by rfl,by decide +kernel,authoredPointWindow,30,30,rfl,rfl⟩

def actualPayload : UnaryActualPayload405 realChoice :=
  ⟨point 30,⟨List.mem_cons_self,List.mem_cons_self,List.mem_cons_self,List.mem_cons_self⟩,
    ⟨.refl 30,.refl 30⟩,seedOrigin,List.mem_cons_self,.direct,rfl⟩

def producerEscape : List410.ExactEscapeWire :=
  ⟨(List.range 43).map (fun n => if n=10 then 0 else 1),[0,2]⟩

theorem source_root_is_safe437 : ¬ RootCycle logicalState seedRequest := by
  intro cyclic
  obtain ⟨arg,actual,cycle⟩ := cyclic
  have same : arg = point 10 := List.mem_singleton.mp actual
  subst arg
  exact List410.exact_escape_refutes_raw_root_K2410
    (s := raw) (site := 10) (w := producerEscape) (by decide +kernel) cycle

private theorem actual_singleton_pick437 {s : GeneralDeclarativeI65.State} {q : GeneralDeclarativeI65.Request}
    {r : Declaration} {rows : List Declaration} (shape : rows = [r])
    (candidate : AuthoredCandidate s q r) :
    StoredAt395 (shape.symm ▸ CandidateTape.next (.matched candidate) .nil) candidate 0 := by
  cases shape
  exact .here candidate .nil

def originalElection : SelectedHeadOrigin395 (row := seed) (authoredNativeTape405 realChoice actualPayload) :=
  let pick := authoredNativeCandidate405 realChoice actualPayload
  ⟨pick,0,0,actual_singleton_pick437 realChoice.visibleOnly pick,by decide +kernel,by decide +kernel⟩

theorem elected_frame_is_the_actual_typed_frame437 :
    preoutputFrameOfOrigin399 originalElection unusedPlacement403 (fun _ => emptyCapture403) = frame := rfl

def realOutputEvent : Event logicalState seedRequest :=
  ⟨frame,originalElection.pick.head,fun j =>
    (show seedIndex = j from Fin.eq_of_val_eq (Nat.lt_one_iff.mp j.isLt).symm) ▸ originalTypedOutput⟩

theorem producer_output_is_same_occurrence437 :
    (realOutputEvent.outputs seedIndex).receipt = originalTypedOutput.receipt := rfl

def typedSelected : AuthoredNativeSelected405 realOutputEvent :=
  ⟨realChoice,actualPayload,originalElection,elected_frame_is_the_actual_typed_frame437.symm,rfl⟩

theorem retainedOriginal : RetainedTypedValueRows403 realOutputEvent := by
  intro i
  have i0 : i = seedIndex := Fin.eq_of_val_eq (Nat.lt_one_iff.mp i.isLt)
  subst i
  exact ⟨output0.right,rfl,List.mem_cons_self⟩

def actualTrace : SourceTrace PriorSource406 logicalState seedRequest (.selected seed.id []) (some realOutputEvent) :=
  .selected realOutputEvent source_root_is_safe437 (.inr ⟨rfl,⟨typedSelected⟩,.inr retainedOriginal⟩) .nil .nil

def producedDictionary : CommonRoleOutermostResolver.Dictionary := .node seed.id []

theorem actualSummary : Summarizes (.selected seed.id []) (.selected producedDictionary) :=
  .selected .nil (.selected rfl)

def needFromActual : OutputNeed logicalState := needOfSelected404 realOutputEvent producedDictionary seedIndex

def actualSupport : SupportForest PriorSource406 logicalState [needFromActual] :=
  .cons actualTrace actualSummary rfl .nil

theorem one_selected_source_supplies_exact_retained_lower437 :
    (actualSupport.atOriginal 0 rfl).event.frame.ordinal = 0 ∧
      needFromActual.producer.occurrence = [101] ∧ needFromActual.ordinal.val = 0 ∧
      needFromActual.expected.original.target = 40 ∧
      raw.equations[0]? = some ⟨40,.nominal 20 [.variable 30]⟩ := ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem selected_seed_has_dictionary_in_every_fitting_model437 (m : GeneralDeclarativeI65.Model) (fit : I72.Fits logicalState m) :
    DictionaryEvidence logicalState m seedRequest producedDictionary := by
  obtain ⟨_,_,dictionary⟩ := authored_native_dictionary_reuses_given_trace405 actualTrace actualSummary
  exact dictionary m fit

def seedLower : Payload 40 needFromActual.expected := ⟨rfl,.nominal 20 [.variable 30],0,rfl⟩

theorem selected_seed_and_its_lower_in_every_same_model437
    (m : GeneralDeclarativeI65.Model) (fit : I72.Fits logicalState m) :
    DictionaryEvidence logicalState m seedRequest producedDictionary ∧ seedLower.Means m :=
  ⟨selected_seed_has_dictionary_in_every_fitting_model437 m fit,
    retained_literal_typed_output_means_same_lower437 seedLower rfl m fit⟩

def sample : GeneralDeclarativeI65.Model :=
  ⟨fun n => ((if n=10 ∨ n=40 then nominal 20 [.inl (.base .int)] else .base .int),Common.rowEmpty),
    fun _ => none,fun n => if n=10 then some nativeOrigin else none⟩

theorem actual_seed_sample_fits437 : I72.Fits logicalState sample := by
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  · intro x h
    change x ∈ [reflAtom] at h
    obtain rfl := List.mem_singleton.mp h
    exact subtype_refl _
  · intro x h; change x ∈ [] at h; cases h
  · intro row h
    change row ∈ [output0,decoy] at h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl <;> exact ⟨subtype_refl _,subtype_refl _⟩
  · intro x h; change x ∈ [] at h; cases h
  · intro x h
    change x ∈ [seedOrigin] at h
    obtain rfl := List.mem_singleton.mp h
    rfl

theorem seed_and_retained_value_when_lower_has_no_authored_syntax437 :
    sample.nativeSyntax 40 = none ∧ DictionaryEvidence logicalState sample seedRequest producedDictionary ∧
      seedLower.Means sample :=
  ⟨rfl,selected_seed_and_its_lower_in_every_same_model437 sample actual_seed_sample_fits437⟩

#print axioms selected_seed_and_its_lower_in_every_same_model437
#print axioms seed_and_retained_value_when_lower_has_no_authored_syntax437
#print axioms source_root_is_safe437
#print axioms elected_frame_is_the_actual_typed_frame437
#print axioms one_selected_source_supplies_exact_retained_lower437
#print axioms selected_seed_has_dictionary_in_every_fitting_model437

end Yulang.C437SelectedSeed
