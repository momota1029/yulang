import Yulang.GeneralDeclarativeI65I74CompletedLowerRetained437
import Yulang.GeneralDeclarativeI65I74CompletedLowerNativeHeader437
import Yulang.GeneralDeclarativeWitnessVarianceFixtures357
import Yulang.GeneralDeclarativeI65I74CompletedLowerSeed437
import Yulang.GeneralDeclarativeI65I74ExactEscape410
import Yulang.GeneralDeclarativeI65I74CompletedLowerCenter437
import Yulang.GeneralDeclarativeI65Origins367

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 14000
set_option maxHeartbeats 1800000
namespace Yulang.C437ReadCompletedCenter
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


open GeneralDeclarativeI65.I72.CompletedSeed437

def realBasis : SeedBasis logicalState seedRequest seed :=
  ⟨realChoice,actualPayload,source_root_is_safe437,0,by decide +kernel,by decide +kernel,rfl⟩

theorem basis_reads_actual_frame437 : realBasis.frame = frame := rfl

def actualOutputs : SeedOutputs realBasis :=
  fun j => (show seedIndex = j from Fin.eq_of_val_eq (Nat.lt_one_iff.mp j.isLt).symm) ▸ originalTypedOutput


def selectedOutput : OneOutput actualOutputs := (readOneOutput actualOutputs rfl 0).get (by decide +kernel)

def need : OutputNeed logicalState := exactNeed realBasis actualOutputs seedIndex

def forest : SupportForest PriorSource406 logicalState [need] :=
  exactSupport realBasis actualOutputs selectedOutput.values seedIndex

def asked : GeneralDeclarativeWhere319.Capture := ⟨40,41,42⟩

def query : GeneralDeclarativeI65.Request := ⟨[202],⟨22,[asked],[]⟩⟩

def upperSource : Origin := ⟨42,[303],unaryNominalPoint404 20 34⟩

def centerSource : Origin := ⟨41,[202],unaryNominalPoint404 20 32⟩

def actualGate : CompletedUnaryGate406 logicalState query observe need := by
  have authority := CompletedNativeHeader437.checkedHeader (s := core.current) (by decide +kernel)
  refine ⟨20,9,asked,rfl,rfl,by decide +kernel,authority.1,authority.2.1 observe (by decide +kernel),
    30,rfl,?_,upperSource,List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
    .direct,34,rfl,by decide +kernel⟩
  change TypedCovariantPoint404 20 30 selectedRhs
  exact ⟨rfl,rfl,rfl⟩

theorem lower_has_no_original_source_route437 : ∀ o ∈ core.origins, ¬OriginRoute core o asked.lower := by
  intro origin present route
  have occurs : core.origins.any (routeMember core asked.lower) = true :=
    List.any_eq_true.mpr ⟨origin,present,actual_route_iff.mpr route⟩
  have absent : core.origins.any (routeMember core asked.lower) = false := by decide +kernel
  rw [absent] at occurs
  cases occurs

def observerEscape : List410.ExactEscapeWire :=
  ⟨(List.range 43).map (fun n => if n ∈ [40,41,42] then 2 else if n ∈ [30,32,34] then 1 else 0),
    [2,1,0]⟩

theorem consumer_raw_root_old_graph_is_safe437 : ¬RootCycle logicalState query := by
  rintro ⟨a,found,bad⟩
  obtain rfl := List.mem_singleton.mp found
  exact List410.exact_escape_refutes_raw_root_K2410
    (s := raw) (site := 40) (w := observerEscape) (by decide +kernel) bad

def election : PreselectedUnary406 logicalState query observe forest :=
  ⟨need,0,rfl,actualGate,consumer_raw_root_old_graph_is_safe437,1,by decide +kernel,by decide +kernel⟩

theorem consumer_source_receipt_and_original_upper_stay_distinct437 :
    election.producer.event.frame.ordinal = 0 ∧ election.authoredOrdinal = 1 ∧
    need.producer.occurrence = [101] ∧ need.ordinal.val = 0 ∧ need.expected.original.target = 40 ∧
    upperSource.slot = 42 ∧ upperSource.issuer = [303] :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩


open GeneralDeclarativeI65.I72.CompletedConsumer437

def reads (j : Nat) : Option (List Nat × List Nat) :=
  (readCenterAt election j).map fun found =>
    let span := (originalNativeFrame406 election found.center).input 9
    (found.center.source.issuer,[span.lower,span.center,span.upper])

/-- Center row #1 is the actual request. Row #2 is the real
upper endpoint, and #3 is the same physical center and syntax
as row #1, but from the wrong request occurrence. -/
theorem exact_center_reader_checks_original_issuer_after_election437 :
    reads 1 = some ([202],[30,32,34]) ∧ reads 2 = none ∧ reads 3 = none ∧ reads 4 = none :=
  by decide +kernel

def checkedCenter : ReadCenter election 1 := (readCenterAt election 1).get (by decide +kernel)

def replayEmpty : CompletedInvocation406 logicalState query [] :=
  buildEmptyInvocation election checkedCenter rfl rfl

theorem read_scoped_consumer_same_model437 (m : GeneralDeclarativeI65.Model) (fit : I72.Fits logicalState m) :
    DictionaryEvidence logicalState m seedRequest (seedDictionary seed) ∧ selectedOutput.kept.payload.Means m ∧
      CompletedInvocationMeaning406 replayEmpty m := by
  obtain ⟨producer,lower⟩ := exact_support_preserves_one_model437 realBasis actualOutputs
    selectedOutput.values selectedOutput.i m fit
  exact ⟨producer,lower,exact_empty_invocation_reads_original_capture437 election checkedCenter rfl rfl m fit⟩

#print axioms readCenterAt
#print axioms exact_empty_invocation_reads_original_capture437
#print axioms exact_center_reader_checks_original_issuer_after_election437
#print axioms read_scoped_consumer_same_model437

end Yulang.C437ReadCompletedCenter
