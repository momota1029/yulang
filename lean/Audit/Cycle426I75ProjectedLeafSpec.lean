import Yulang.GeneralDeclarativeI65I75ProjectedLeafEntry426

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1800

namespace Yulang.GeneralDeclarativeI65.I72.ProjectedRetention423.Spec426
open GeneralDeclarativeI65
open CommonNominalFullCarrier (Equivalent Ty)

open Checker408 (Problem)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarations (Declaration)
open GeneralDeclarativeWitnessSparseVariance357 (Source compile)
open GeneralSourceMetadataBareBundle291 (InputBundle)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open OpenTail414 (openRow openTerm)
open ExplicitPick419 (pickSyntax)
open CommonNominalFullCarrier (subtype_refl)

-- Exact C425 split-state control, re-expressed for standalone audit.
-- The source identities, original bounds and typed plan match C423.
-- Slot 10 is unused by that original fixture and is reserved for the second retained row.
def fixtureBodies425 : Source 0 0 0 := ⟨[],Fin.elim0,Fin.elim0⟩
def authoredBody : GeneralDeclarations.Equation := ⟨92,3,.var 8⟩
def fixtureDecl425 : Declaration := ⟨57,7,[pickSyntax 20 8 13],[],[authoredBody],[]⟩
def otherDecl425 : Declaration := ⟨58,9,[],[],[],[]⟩
def fixtureSource425 : InputBundle :=
  ⟨⟨.absent,[]⟩,⟨.absent,[]⟩,⟨1,[⟨7,1,[(3,none)]⟩,⟨9,0,[]⟩]⟩,[otherDecl425,fixtureDecl425]⟩
def originalOrigins425 : List Origin :=
  [⟨0,[44],openTerm 20 3 5⟩,⟨2,[55],openTerm 20 4 6⟩]
def splitRows : List Equation :=
  [openRow 0 20 3 5,openRow 2 20 4 6,⟨12,.variable 11⟩]
def splitAtoms : List (PresenceNormalForm.Atom Nat) :=
  [requiredLower 20 11 1,requiredUpper 20 11 1]

def actualBuild425 (rows : List Equation) (atoms : List (PresenceNormalForm.Atom Nat))
    (sources : List Origin := originalOrigins425) :
    Option Problem := do
  let program ← compile fixtureBodies425
  let bundle ← GeneralSourceMetadataBareBundle291.compile fixtureSource425
  let env : Environment := ⟨0,0,0,fixtureBodies425,program,bundle⟩
  let s : GeneralDeclarativeI65.State :=
    ⟨⟨env,⟨⟨atoms,[(0,1),(1,2)]⟩,rows⟩,[]⟩,[],sources,[]⟩
  let atlas : B6OccurrenceAtlas401 s := ⟨fun q decl i body =>
    if q.occurrence == [61,423] && decl == 1 && i.val == 0 then
      if h : body = .explicit authoredBody then
        some (h.symm ▸ (MixedRhs401.binder 8 () : B6MixedRhs401 s false
          (GeneralDeclarationPatterns.normalize (GeneralDeclarativeOutputs320.bodyPattern (.explicit authoredBody)))))
      else none
    else none⟩
  pure ⟨⟨s,atlas⟩,⟨[61,423],⟨7,[⟨0,1,2⟩],[⟨3,12⟩]⟩⟩⟩

def splitProblem : Problem :=
  (actualBuild425 splitRows splitAtoms).get (by decide +kernel)
def sourceWire425 : RecordEndpoints422.Wire :=
  ⟨⟨0,0⟩,⟨1,1⟩,1,⟨[0,0,0,1,1,1,1,1,0,0,1,1,1],[0,1]⟩⟩
def splitInput : PrepareWire := ⟨sourceWire425,.requiredChannel ⟨2,0,1⟩⟩
def preparedSplit : PreparedWrite splitProblem :=
  (readRetainedPickWrite423 splitProblem splitInput).get (by decide +kernel)
def absentB6 : Problem :=
  ⟨⟨splitProblem.state.core,⟨fun _ _ _ _ => none⟩⟩,splitProblem.root⟩

def splitModel : I72.Model :=
  ⟨fun n =>
    ((if n = 0 then GeneralDeclarativeRecordSplit330.lo 20
      else if n = 1 then GeneralDeclarativeRecordSplit330.hidden 20
      else if n = 2 then GeneralDeclarativeRecordSplit330.hi 20
      else if n = 3 then .bottom
      else if n = 4 ∨ n = 10 ∨ n = 11 ∨ n = 12 then .top
      else .exactEmpty),Common.rowEmpty),
    fun _ => none,fun n => if n = 0 then some (openTerm 20 3 5)
      else if n = 2 then some (openTerm 20 4 6) else none⟩

theorem original_split_model_fits_with_exact_required_target_constraints425 :
    I72.Fits splitProblem.state splitModel := by
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  · intro atom mem
    change atom ∈ splitAtoms at mem
    simp only [splitAtoms,List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl
    · exact CommonNominalFullCarrier.subtype_refl _
    · exact (GeneralDeclarativeRecordSplit330.interval 20).2
  · intro pair mem
    change pair ∈ [(0,1),(1,2)] at mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl
    · exact (GeneralDeclarativeRecordSplit330.interval 20).1
    · exact (GeneralDeclarativeRecordSplit330.interval 20).2
  · intro e mem
    change e ∈ splitRows at mem
    simp only [splitRows,List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl <;> exact ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩
  · intro _ none; cases none
  · intro o mem
    change o ∈ originalOrigins425 at mem
    simp only [originalOrigins425,List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl <;> rfl

def withOrdinaryReceiptExtras425 (added : List Equation) : Problem :=
  let current := splitProblem.state.core
  let next := {current with current := {current.current with ordinary :=
    {current.current.ordinary with equations := splitRows ++ added}}}
  let atlas : B6OccurrenceAtlas401 next := ⟨fun q n i body =>
    if q.occurrence == [61,423] && n == 1 && i.val == 0 then
      if h : body = .explicit authoredBody then
        some (h.symm ▸ (MixedRhs401.binder 8 () : B6MixedRhs401 next false
          (GeneralDeclarationPatterns.normalize (GeneralDeclarativeOutputs320.bodyPattern (.explicit authoredBody)))))
      else none
    else none⟩
  ⟨⟨next,atlas⟩,splitProblem.root⟩

def decodedRoot425 : Equation := ⟨0,.record 20 (.variable 3) (.primitive .emptyRecord [])⟩
def cyclicReceiptRoot425 : Problem := withOrdinaryReceiptExtras425 [decodedRoot425,⟨3,.variable 0⟩]
def cyclicButOnlyPayload425 : Problem :=
  withOrdinaryReceiptExtras425 [decodedRoot425,⟨3,.variant 88 (.variable 3)⟩]

open ProjectedCore425
open Check408 (Write)
open Checker408 (Result)

def leafWire426 : ProjectedRowsWire426 := ⟨sourceWire425,⟨2,0,1⟩⟩

def splitLeaf426 : ProjectedLeafPacket426 splitProblem :=
  (checkableProjectedLeaf426 splitProblem leafWire426).get (by decide +kernel)

def testTag426 : Nat := 19

def realReport426 : Result :=
  ⟨.selected 57 [],.selected (.node 57 []),[encodeProjectedWrite425 testTag426 preparedSplit]⟩

theorem actual_leaf_report_verified_without_named_capture426 :
    checkProjectedLeafReport426 splitProblem testTag426 realReport426 leafWire426 = true := by
  decide +kernel

theorem actual_leaf_report_rejects_changed_root_dictionary_target_and_reserved_tag426 :
    checkProjectedLeafReport426 splitProblem testTag426
      {realReport426 with tree := .selected 58 []} leafWire426 = false ∧
    checkProjectedLeafReport426 splitProblem testTag426
      {realReport426 with verdict := .selected (.node 58 [])} leafWire426 = false ∧
    checkProjectedLeafReport426 splitProblem testTag426
      {realReport426 with writes := [{encodeProjectedWrite425 testTag426 preparedSplit with
          target := ⟨3,17⟩}]} leafWire426 = false ∧
    checkProjectedLeafReport426 splitProblem 8 (splitLeaf426.exactReport 8) leafWire426 = false := by
  decide +kernel

def sourceDespiteMissingTarget426 : Problem :=
  (actualBuild425 (splitRows.take 2) splitAtoms).get (by decide +kernel)

theorem original_leaf_is_visible_without_output_retention_but_report_is_not_verified426 :
    (readProjectedLeafSource426 sourceDespiteMissingTarget426 leafWire426.source).isSome = true ∧
    checkProjectedLeafReport426 sourceDespiteMissingTarget426 testTag426 realReport426 leafWire426 = false := by
  decide +kernel

theorem true_raw_K2_defeats_projected_leaf_but_uninspected_payload_loop_does_not426 :
    checkProjectedLeafReport426 cyclicReceiptRoot425 testTag426 realReport426 leafWire426 = false ∧
    checkProjectedLeafReport426 cyclicButOnlyPayload425 testTag426 realReport426 leafWire426 = true := by
  decide +kernel

theorem original_leaf_body_evaluates_in_real_split_model426 :
    splitLeaf426.original.out.valueAt splitModel = some ([61,423],1,0,12,.top) ∧
    GeneralDeclarativeRecordChannel330.project 20 true [] (splitModel.assignment 1).1 = some (.inter .top .bottom) := by
  obtain ⟨_,v,seen,actual,_⟩ := original_core_and_required_rows_produce_same_model_meaning426
    splitLeaf426.original.out splitLeaf426.retained splitModel
    original_split_model_fits_with_exact_required_target_constraints425
  have lab : splitLeaf426.original.out.label = 20 := by decide +kernel
  have center : splitLeaf426.original.out.arg.center = 1 := by decide +kernel
  rw [lab,center] at seen
  change GeneralDeclarativeRecordChannel330.project 20 false []
    (GeneralDeclarativeRecordSplit330.hidden 20) = some v at seen
  have same := Option.some.inj ((GeneralDeclarativeRecordSplit330.required_top 20).symm.trans seen)
  have wrote : (splitProblem.root.occurrence,splitLeaf426.original.out.ordinal,
    splitLeaf426.original.outIndex.val,splitProblem.root.demand.outputs[splitLeaf426.original.outIndex].target)
      = ([61,423],1,0,12) := by decide +kernel
  subst v
  have occurrence := congrArg Prod.fst wrote
  have declaration := congrArg (fun x => x.2.1) wrote
  have ordinal := congrArg (fun x => x.2.2.1) wrote
  have target := congrArg (fun x => x.2.2.2) wrote
  change splitProblem.root.occurrence = [61,423] at occurrence
  change splitLeaf426.original.out.ordinal = 1 at declaration
  change splitLeaf426.original.outIndex.val = 0 at ordinal
  change splitProblem.root.demand.outputs[splitLeaf426.original.outIndex].target = 12 at target
  refine ⟨?_,GeneralDeclarativeRecordSplit330.optional_bottom 20⟩
  simpa only [occurrence,declaration,ordinal,target] using actual

#print axioms actual_leaf_report_verified_without_named_capture426
#print axioms actual_leaf_report_rejects_changed_root_dictionary_target_and_reserved_tag426
#print axioms original_leaf_is_visible_without_output_retention_but_report_is_not_verified426
#print axioms true_raw_K2_defeats_projected_leaf_but_uninspected_payload_loop_does_not426
#print axioms original_leaf_body_evaluates_in_real_split_model426

end Yulang.GeneralDeclarativeI65.I72.ProjectedRetention423.Spec426
