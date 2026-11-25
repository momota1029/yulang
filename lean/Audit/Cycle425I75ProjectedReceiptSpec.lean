import Yulang.GeneralDeclarativeI65I75ProjectedReceiptMeaning425


set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1800

namespace Yulang.GeneralDeclarativeI65.I72.ProjectedRetention423.Spec425
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

-- Minimal standalone re-expression of the C423 split fixture.
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

-- Two different retained ordinary variables justify the same actual B6 binder.
def altRows425 : List Equation := splitRows ++ [⟨12,.variable 10⟩]
def altAtoms425 : List (PresenceNormalForm.Atom Nat) :=
  splitAtoms ++ [requiredLower 20 10 1,requiredUpper 20 10 1]
def twoRows : Problem := (actualBuild425 altRows425 altAtoms425).get (by decide +kernel)
def transportInput : PrepareWire := splitInput
def alternativeInput : PrepareWire := ⟨sourceWire425,.requiredChannel ⟨3,2,3⟩⟩
def firstReceipt : PreparedWrite twoRows :=
  (readRetainedPickWrite423 twoRows transportInput).get (by decide +kernel)
def otherReceipt : PreparedWrite twoRows :=
  (readRetainedPickWrite423 twoRows alternativeInput).get (by decide +kernel)

def actualKey425 : ProjectedReceiptKey425 :=
  ⟨[61,423],1,57,92,0,3,12,⟨8,13,20,0,1,2,3,4,5,6,[44],[55]⟩⟩

theorem actual_split_state_reads_original_full_receipt425 :
    readProjectedReceipt425 splitProblem splitInput actualKey425 = some preparedSplit := by
  apply read_projected_receipt_is_exact425.mpr
  refine ⟨(Option.some_get _).symm,?_⟩
  decide +kernel

/-- Only same-source readback, not new source rejection. -/
theorem projected_receipt_rejects_wrong_positions_and_witnesses425 :
    (readProjectedReceipt425 splitProblem splitInput {actualKey425 with occurrence := [61,424]}).isNone = true ∧
    (readProjectedReceipt425 splitProblem splitInput {actualKey425 with declarationOrdinal := 0}).isNone = true ∧
    (readProjectedReceipt425 splitProblem splitInput {actualKey425 with declarationId := 58}).isNone = true ∧
    (readProjectedReceipt425 splitProblem splitInput {actualKey425 with associatedEquationId := 91}).isNone = true ∧
    (readProjectedReceipt425 splitProblem splitInput {actualKey425 with outputOrdinal := 1}).isNone = true ∧
    (readProjectedReceipt425 splitProblem splitInput {actualKey425 with outputName := 13}).isNone = true ∧
    (readProjectedReceipt425 splitProblem splitInput {actualKey425 with fixedTarget := 11}).isNone = true ∧
    (readProjectedReceipt425 splitProblem splitInput
      {actualKey425 with site := {actualKey425.site with fieldBinder := 13}}).isNone = true ∧
    (readProjectedReceipt425 splitProblem splitInput
      {actualKey425 with site := {actualKey425.site with label := 21}}).isNone = true ∧
    (readProjectedReceipt425 splitProblem splitInput
      {actualKey425 with site := {actualKey425.site with center := 11}}).isNone = true ∧
    (readProjectedReceipt425 splitProblem splitInput
      {actualKey425 with site := {actualKey425.site with tailUpper := 5}}).isNone = true ∧
    (readProjectedReceipt425 splitProblem splitInput
      {actualKey425 with site := {actualKey425.site with lowerIssuer := [55]}}).isNone = true :=  by
  repeat (first | apply And.intro | decide +kernel)

theorem missing_original_B6_cannot_be_replaced_by_matching_projection_key425 :
    (readProjectedReceipt425 absentB6 splitInput actualKey425).isNone = true := by decide +kernel

theorem projected_equation_keeps_original_B6_with_an_actual_split_model425 :
    ∃ v : Ty,
      actualKey425.valueAt splitModel = some v ∧
      preparedSplit.typed.actualRightValue splitModel = some ([61,423],1,0,12,v) ∧
      Equivalent (splitModel.assignment 12).1 v ∧ Equivalent (splitModel.assignment 11).1 v := by
  obtain ⟨_,v,seen,rhs,target,retained⟩ :=
    read_projected_receipt_keeps_real_original_equation425
      actual_split_state_reads_original_full_receipt425 splitModel
      original_split_model_fits_with_exact_required_target_constraints425
  have pos : preparedSplit.retained.rowAt = (2,11) := by decide +kernel
  rw [pos] at retained
  exact ⟨v,seen,rhs,target,retained⟩

/-- Different positions can justify the value without becoming its lexical address. -/
theorem two_original_row_proofs_use_one_projected_key425 :
    projectedKey425 firstReceipt = actualKey425 ∧ projectedKey425 otherReceipt = actualKey425 ∧
    firstReceipt.retained.rowAt = (2,11) ∧ otherReceipt.retained.rowAt = (3,10) := by
  repeat (first | apply And.intro | decide +kernel)


#print axioms actual_split_state_reads_original_full_receipt425
#print axioms projected_receipt_rejects_wrong_positions_and_witnesses425
#print axioms missing_original_B6_cannot_be_replaced_by_matching_projection_key425
#print axioms projected_equation_keeps_original_B6_with_an_actual_split_model425
#print axioms two_original_row_proofs_use_one_projected_key425

end Yulang.GeneralDeclarativeI65.I72.ProjectedRetention423.Spec425

namespace Yulang.GeneralDeclarativeI65.I72.ProjectedRetention423.Spec425
open GeneralDeclarativeI65
open Checker408 (Problem)
open GeneralDeclarativeHead320 (Equation)

theorem both_actual_retained_row_reads_keep_the_identical_B6_term425 :
    HEq firstReceipt.typed.plan otherReceipt.typed.plan := by
  have a : readProjectedReceipt425 twoRows transportInput actualKey425 = some firstReceipt :=
    read_projected_receipt_is_exact425.mpr
      ⟨(Option.some_get _).symm,two_original_row_proofs_use_one_projected_key425.1⟩
  have b : readProjectedReceipt425 twoRows alternativeInput actualKey425 = some otherReceipt :=
    read_projected_receipt_is_exact425.mpr
      ⟨(Option.some_get _).symm,two_original_row_proofs_use_one_projected_key425.2.1⟩
  exact (one_exact_receipt_replays_one_original_B6_term425 a b).2.2.2.2

theorem both_distinct_retained_row_witnesses_fit_one_state425 :
    I72.Fits twoRows.state splitModel := by
  have prior := original_split_model_fits_with_exact_required_target_constraints425
  refine ⟨⟨⟨⟨?_,prior.1.1.1.2⟩,?_⟩,prior.1.2⟩,prior.2⟩
  · intro atom members
    change atom ∈ altAtoms425 at members
    rcases List.mem_append.mp members with old|new
    · exact prior.1.1.1.1 atom old
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at new
      rcases new with rfl|rfl
      · exact CommonNominalFullCarrier.subtype_refl _
      · exact (GeneralDeclarativeRecordSplit330.interval 20).2
  · intro e members
    change e ∈ altRows425 at members
    rcases List.mem_append.mp members with old|new
    · exact prior.1.1.2 e old
    · simp only [List.mem_singleton] at new
      subst e
      exact ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩

theorem both_actual_split_receipts_replay_the_same_body_and_model_value425 :
    firstReceipt.original.assoc = otherReceipt.original.assoc ∧
    HEq firstReceipt.typed.plan otherReceipt.typed.plan ∧
    firstReceipt.typed.actualRightValue splitModel = otherReceipt.typed.actualRightValue splitModel := by
  have a : readProjectedReceipt425 twoRows transportInput actualKey425 = some firstReceipt :=
    read_projected_receipt_is_exact425.mpr
      ⟨(Option.some_get _).symm,two_original_row_proofs_use_one_projected_key425.1⟩
  have b : readProjectedReceipt425 twoRows alternativeInput actualKey425 = some otherReceipt :=
    read_projected_receipt_is_exact425.mpr
      ⟨(Option.some_get _).symm,two_original_row_proofs_use_one_projected_key425.2.1⟩
  exact same_receipt_key_preserves_source_and_model_write425 a b splitModel
    both_distinct_retained_row_witnesses_fit_one_state425

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

def actualRootCycleWire425 : RepeatedCenters421.Witness :=
  .previous (.previous (.previous (.previous (.previous
    (.previous (.previous (.previous (.previous (.previous (.previous
      (.previous (.previous (.rawRoot ⟨0,⟨3,.same,3⟩,[],.forward 4⟩)))))))))))))

theorem actual_raw_K2_precedes_an_unchanged_projected_receipt425 :
    (readProjectedReceipt425 cyclicReceiptRoot425 splitInput actualKey425).isNone = true ∧
    RepeatedCenters421.check cyclicReceiptRoot425 Check408.rawReport actualRootCycleWire425 = true := by
  constructor <;> decide +kernel

theorem off_root_payload_loop_does_not_fake_projected_receipt_K2425 :
    (readProjectedReceipt425 cyclicButOnlyPayload425 splitInput actualKey425).isSome = true ∧
    RepeatedCenters421.check cyclicButOnlyPayload425 Check408.rawReport actualRootCycleWire425 = false := by
  constructor <;> decide +kernel

#print axioms both_actual_retained_row_reads_keep_the_identical_B6_term425
#print axioms both_distinct_retained_row_witnesses_fit_one_state425
#print axioms both_actual_split_receipts_replay_the_same_body_and_model_value425
#print axioms actual_raw_K2_precedes_an_unchanged_projected_receipt425
#print axioms off_root_payload_loop_does_not_fake_projected_receipt_K2425
end Yulang.GeneralDeclarativeI65.I72.ProjectedRetention423.Spec425

namespace Yulang.GeneralDeclarativeI65.I72.ProjectedRetention423.Spec425
open CommonNominalFullCarrier (Ty Equivalent record)
open Checker408 (Problem)
open GeneralDeclarativeI65

def missingFirstAuthoredOrigin425 : Problem :=
  (actualBuild425 splitRows splitAtoms (originalOrigins425.drop 1)).get (by decide +kernel)
def missingSecondAuthoredOrigin425 : Problem :=
  (actualBuild425 splitRows splitAtoms (originalOrigins425.take 1)).get (by decide +kernel)

theorem exact_key_does_not_replace_either_authored_endpoint425 :
    (readProjectedReceipt425 missingFirstAuthoredOrigin425 splitInput actualKey425).isSome = false ∧
    (readProjectedReceipt425 missingSecondAuthoredOrigin425 splitInput actualKey425).isSome = false := by
  constructor <;> decide +kernel

theorem real_split_receipt_has_captured_meaning_without_literal_record425 :
    actualKey425.OriginalSites splitProblem.state.core ∧ actualKey425.Meaning splitModel ∧
      ¬ (∃ f t : Ty, Equivalent (splitModel.assignment actualKey425.site.center).1
        (record actualKey425.site.label f t)) := by
  refine ⟨accepted_projected_receipt_names_both_original_endpoint_sources425
    actual_split_state_reads_original_full_receipt425,
    (accepted_exact_key_denotes_full_projected_capture425 actual_split_state_reads_original_full_receipt425
      splitModel original_split_model_fits_with_exact_required_target_constraints425).1,?_⟩
  rintro ⟨f,t,wrong⟩
  exact GeneralDeclarativeRecordSplit330.no_literal 20 f t wrong

#print axioms exact_key_does_not_replace_either_authored_endpoint425
#print axioms real_split_receipt_has_captured_meaning_without_literal_record425
end Yulang.GeneralDeclarativeI65.I72.ProjectedRetention423.Spec425
