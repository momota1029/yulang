import Yulang.GeneralDeclarativeI65I74MergedOutputEntry439
import Yulang.GeneralNominalCenteredHeadAllocMergeSource
import Yulang.GeneralDeclarativeWitnessVarianceFixtures357

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
namespace Yulang.C439MergedAudit
open GeneralDeclarativeI65
open GeneralDeclarativeI65.I72
open GeneralDeclarativeI65.I72.MergedOutput439
open GeneralDeclarations (Declaration)
open GeneralSourceMetadataRows291 (Row)
open GeneralSourceMetadataBareBundle291 (InputBundle)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarativeWitnessDeclaredState357 (point)
open Checker408 (Problem Result)
open CommonNominalFullCarrier (variant subtype_refl)

abbrev parent := GeneralNominalCenteredHeadAllocMergeSource.parent
abbrev child := GeneralNominalCenteredHeadAllocMergeSource.leaf

def rival : Declaration := {child with id := 99}

def renamedTail : GeneralDeclarations.Clause :=
  {GeneralNominalCenteredHeadAllocMergeSource.lastClause with outputs :=
    [⟨43,1,.variant 0 (.app 2 [])⟩]}

def renamedParent : Declaration := {parent with requirements :=
  [GeneralNominalCenteredHeadAllocMergeSource.firstClause,renamedTail]}

def renamedChild : Declaration := {child with associated :=
  [⟨45,0,.app 2 []⟩,⟨46,1,.app 2 []⟩]}

def bundle (decls : List Declaration) (twoNames : Bool) : InputBundle :=
  let rs : List Row := [⟨2,some ⟨[],2⟩,.primitive (.scalar .int)⟩]
  let associated := if twoNames then [(0,none),(1,none)] else [(0,none)]
  ⟨⟨.absent,rs⟩,⟨.absent,rs⟩,⟨0,[⟨0,1,[]⟩,⟨1,0,associated⟩]⟩,decls⟩

def env? (decls : List Declaration) (twoNames := false) : Option Environment := do
  let source := GeneralDeclarativeWitnessVarianceFixtures357.source
  let graph ← GeneralDeclarativeWitnessSparseVariance357.compile source
  let book ← GeneralSourceMetadataBareBundle291.compile (bundle decls twoNames)
  pure ⟨3,2,0,source,graph,book⟩

def env : Environment := (env? [parent,child]).get (by decide +kernel)

def raw : GeneralDeclarativeHead320.State :=
  ⟨⟨[],[]⟩,[⟨0,intCode⟩,⟨1,intCode⟩,⟨2,tickCode⟩]⟩

def origin : Origin := ⟨0,[7],.ordinary (.base .int)⟩

def otherIssuer : Origin := ⟨0,[900],.ordinary (.base .int)⟩

def core (src := env) (initial := raw) : GeneralDeclarativeI65.State :=
  ⟨⟨src,initial,[]⟩,[],[origin,otherIssuer],[]⟩

def state (s : GeneralDeclarativeI65.State) : I72.State :=
  ⟨s,⟨fun _ _ _ _ => none⟩⟩

def request : I72.Request := ⟨[7],⟨0,[point 0],[]⟩⟩

def problem : Problem := ⟨state (core env raw),request⟩

def expected : Result := ⟨.selected 37 [.rejected],.rejected,[]⟩

def witness : Wire439 := ⟨0,⟨[0,1,2],[0,2,2]⟩⟩


theorem scoped_header_recognizes_actual_closed_nullary_child439 :
    CompletedNativeHeader437.checkHeader env = false ∧ checkHeader439 env = true := by
  decide +kernel

theorem real_public_check_rejects_only_at_the_merged_child439 :
    check problem expected (.mergedOutput witness) = true := by decide +kernel

def original : Original439 problem.state problem.root :=
  (replay439 problem.state problem.root witness).get (by decide +kernel)

theorem actual_compiler_child_and_report_addresses439 :
    original.frame.ordinal = 0 ∧ original.frame.decl.id = 37 ∧ original.leaf.id = 38 ∧
    original.firstClause.id = 42 ∧ original.lastClause.id = 44 ∧
    frameWhereKids400 original.frame =
      [⟨[7,0],⟨1,[],[⟨0,1⟩]⟩⟩,⟨[7,1],⟨1,[],[⟨0,2⟩]⟩⟩] ∧
    original.representative.occurrence = [7,0] ∧
    original.representative.demand.outputs = [⟨0,1⟩,⟨0,2⟩] ∧
    original.report = expected := by
  have numeric : original.frame.ordinal = 0 ∧ original.frame.decl.id = 37 ∧ original.leaf.id = 38 ∧
      original.firstClause.id = 42 ∧ original.lastClause.id = 44 ∧
      original.leftCell = 1 ∧ original.rightCell = 2 ∧ original.childRole = 1 ∧ original.outName = 0 :=
    by decide +kernel
  refine ⟨numeric.1,numeric.2.1,numeric.2.2.1,numeric.2.2.2.1,numeric.2.2.2.2.1,?_,rfl,?_,?_⟩
  · rw [original.exactKids,numeric.2.2.2.2.2.1,numeric.2.2.2.2.2.2.1,
      numeric.2.2.2.2.2.2.2.1,numeric.2.2.2.2.2.2.2.2]
    rfl
  · rw [Original439.representative,numeric.2.2.2.2.2.1,numeric.2.2.2.2.2.2.1,
      numeric.2.2.2.2.2.2.2.2]
  · simp [Original439.report,expected,numeric.2.1]

def originalModel : GeneralDeclarativeI65.Model :=
  ⟨fun n => ((if n = 2 then variant 0 (.base .int) else .base .int),Common.rowEmpty),
    fun _ => none, fun n => if n = 0 then some (.ordinary (.base .int)) else none⟩

theorem original_separate_output_cells_have_a_real_model439 : I72.Fits problem.state originalModel := by
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  · intro x h; change x ∈ [] at h; cases h
  · intro x h; change x ∈ [] at h; cases h
  · intro e h
    change e ∈ [⟨0,intCode⟩,⟨1,intCode⟩,⟨2,tickCode⟩] at h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl <;> exact ⟨subtype_refl _,subtype_refl _⟩
  · intro x h; change x ∈ [] at h; cases h
  · intro x h
    change x ∈ [origin,otherIssuer] at h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl <;> rfl

theorem tested_public_report_is_supported_and_only_merging_is_impossible439 :
    I72.Fits problem.state originalModel ∧
    R19 problem.state problem.root expected.verdict ∧
    ReportEvidence problem.state originalModel problem.root expected ∧
    ¬ ∃ m : I72.Model, I72.Fits problem.state m ∧ original.MergedOutput m := by
  obtain ⟨classifies,same⟩ := verified_R19_result_classifies_in_same_State439 problem expected
    (.mergedOutput witness) real_public_check_rejects_only_at_the_merged_child439
  exact ⟨original_separate_output_cells_have_a_real_model439,classifies,
    same _ original_separate_output_cells_have_a_real_model439,
    no_fitting_extension_equalizes_the_named_output439 original⟩

def competitor : Environment := (env? [parent,child,rival]).get (by decide +kernel)
def withRival : Problem := ⟨state (core competitor raw),request⟩

def differentOutputName : Environment :=
  (env? [renamedParent,renamedChild] true).get (by decide +kernel)
def withRenamed : Problem := ⟨state (core differentOutputName raw),request⟩

def sameCellRaw : GeneralDeclarativeHead320.State :=
  ⟨⟨[],[]⟩,[⟨0,intCode⟩,⟨0,intCode⟩,⟨2,tickCode⟩]⟩

def wronglyReusedParentCell : Problem := ⟨state (core env sameCellRaw),request⟩

theorem actual_rival_and_different_name_not_this_conflict439 :
    checkHeader439 competitor = true ∧
    (visible withRival.state.core ⟨[7,0],⟨1,[],[⟨0,1⟩]⟩⟩).length = 2 ∧
    check withRival expected (.mergedOutput witness) = false ∧
    checkHeader439 differentOutputName = true ∧
    check withRenamed expected (.mergedOutput witness) = false ∧
    check wronglyReusedParentCell expected (.mergedOutput witness) = false :=
  by decide +kernel

theorem original_child_location_cannot_be_replaced_or_duplicated439 :
    check problem Check408.rawReport (.mergedOutput witness) = false ∧
    check problem ⟨.selected 37 [.rejected,.rejected],.rejected,[]⟩ (.mergedOutput witness) = false ∧
    check problem ⟨.selected 99 [.rejected],.rejected,[]⟩ (.mergedOutput witness) = false ∧
    check problem expected (.mergedOutput {witness with originalInput := 1}) = false :=
  by decide +kernel


def cyclicRaw : GeneralDeclarativeHead320.State :=
  ⟨⟨[],[]⟩,[⟨0,.variant 0 (.variable 0)⟩,⟨1,intCode⟩,⟨2,tickCode⟩]⟩

def actualRawCycle : Problem := ⟨state (core env cyclicRaw),request⟩

def rawCycleWire : GeneralDeclarativeWitnessCycle350.Wire :=
  ⟨0,⟨0,.same,0⟩,[],.same⟩

def oldRawRoot : MergedOutput439.Witness :=
  .previous (.previous (.previous (.previous (.previous (.previous (.previous (.previous (.previous (.previous (.previous (.previous (.previous (.previous (.previous (.previous (.previous (.previous (.previous (.rawRoot rawCycleWire)))))))))))))))))))

theorem actual_old_raw_K2_still_uses_its_own_location439 :
    check actualRawCycle expected (.mergedOutput witness) = false ∧
    check actualRawCycle Check408.rawReport oldRawRoot = true ∧
    check problem Check408.rawReport oldRawRoot = false := by decide +kernel

def boolBook : InputBundle :=
  let b := bundle [parent,child] false
  let rs : List Row := [⟨2,some ⟨[],2⟩,.primitive (.scalar .bool)⟩]
  ⟨⟨.absent,rs⟩,⟨.absent,rs⟩,b.roles,b.declarations⟩

def actualNonIntMetadata : Environment :=
  {env with source := (GeneralSourceMetadataBareBundle291.compile boolBook).get (by decide +kernel)}

def wrongCoreTranslation : Problem := ⟨state (core actualNonIntMetadata raw),request⟩

theorem literal_int_raw_rows_do_not_supply_nonint_source439 :
    checkHeader439 actualNonIntMetadata = true ∧
    check wrongCoreTranslation expected (.mergedOutput witness) = false := by decide +kernel

#print axioms actual_old_raw_K2_still_uses_its_own_location439
#print axioms literal_int_raw_rows_do_not_supply_nonint_source439
#print axioms scoped_header_recognizes_actual_closed_nullary_child439
#print axioms real_public_check_rejects_only_at_the_merged_child439
#print axioms actual_compiler_child_and_report_addresses439
#print axioms original_separate_output_cells_have_a_real_model439
#print axioms tested_public_report_is_supported_and_only_merging_is_impossible439
#print axioms actual_rival_and_different_name_not_this_conflict439
#print axioms original_child_location_cannot_be_replaced_or_duplicated439

end Yulang.C439MergedAudit
