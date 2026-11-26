import Yulang.GeneralDeclarativeI65I74CompletedLowerRetained437
import Yulang.GeneralDeclarativeI65I74CompletedLowerNativeHeader437
import Yulang.GeneralDeclarativeWitnessVarianceFixtures357

set_option backward.isDefEq.respectTransparency false
namespace Yulang.C437RetainedFixture
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
def raw : GeneralDeclarativeHead320.State := ⟨⟨[],[]⟩,[output0,decoy]⟩
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

def checksRetainedAt (ordinal : Nat) : Bool :=
  match fixedValueCode403 originalTypedOutput.rhs with
  | none => false
  | some code => decide (raw.equations[ordinal]? = some ⟨originalTypedOutput.receipt.original.target,code⟩)

theorem same_target_literal_decoy_is_not_the_typed_output437 :
    checksRetainedAt 0 = true ∧ checksRetainedAt 1 = false := by decide +kernel

def readLower : Payload 40 originalTypedOutput.receipt := ⟨rfl,.nominal 20 [.variable 30],0,rfl⟩

def sample (fallback : Option (Endpoint Nat)) : Model :=
  ⟨fun n => ((if n=10 ∨ n=40 then nominal 20 [.inl (.base .int)] else .base .int),Common.rowEmpty),
    fun _ => none,fun n => if n=10 then some nativeOrigin else if n=40 then fallback else none⟩

theorem sampleFits (fallback : Option (Endpoint Nat)) : Fits core (sample fallback) := by
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  · intro x h; change x ∈ [] at h; cases h
  · intro x h; change x ∈ [] at h; cases h
  · intro row h
    change row ∈ [output0,decoy] at h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl <;> exact ⟨subtype_refl _,subtype_refl _⟩
  · intro x h; change x ∈ [] at h; cases h
  · intro x h
    change x ∈ [⟨10,[101],nativeOrigin⟩] at h
    obtain rfl := List.mem_singleton.mp h
    rfl

theorem original_lower_meaning_ignores_unused_nativeSyntax437 (fallback : Option (Endpoint Nat)) :
    readLower.Means (sample fallback) :=
  retained_literal_typed_output_means_same_lower437 readLower rfl _ (sampleFits fallback)

theorem retained_and_decoy_have_equal_values_in_fitting_sample437 :
    GeneralNominalCenteredHeadMatExpressions.value
      (GeneralDeclarativeHead320.environment (sample none).assignment) .actual output0.right =
    GeneralNominalCenteredHeadMatExpressions.value
      (GeneralDeclarativeHead320.environment (sample none).assignment) .actual decoy.right := rfl

#print axioms atlas_guards_original_occurrence_and_declaration437
#print axioms retained_and_decoy_have_equal_values_in_fitting_sample437
#print axioms same_target_literal_decoy_is_not_the_typed_output437
#print axioms original_lower_meaning_ignores_unused_nativeSyntax437

end Yulang.C437RetainedFixture
