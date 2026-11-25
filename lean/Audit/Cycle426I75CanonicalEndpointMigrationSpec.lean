import Yulang.GeneralDeclarativeI65I75CanonicalEndpointReport426
import Yulang.GeneralDeclarativeI65I74RecordEndpointsRuleBoundary422

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1800

namespace Yulang.GeneralDeclarativeI65.I72.ProjectedRetention423.MigrationSpec426
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


open Checker408 (Result)
open ProjectedCore425
open CommonRoleOutermostResolver (Dictionary)

def onlyRequired426 : ProjectedRowsWire426 := ⟨sourceWire425,⟨2,0,1⟩⟩
def exactProjectedReport426 : Result :=
  ⟨.selected 57 [],.selected (.node 57 []),[encodeProjectedWrite425 19 preparedSplit]⟩

theorem projected_leaf_offered_report_is_real426 :
    checkProjectedLeafReport426 splitProblem 19 exactProjectedReport426 onlyRequired426 = true := by
  decide +kernel

theorem actual_split_projection_has_canonical_dictionary_evidence426 :
    ∀ m : I72.Model, I72.Fits splitProblem.state m →
      I72.DictionaryEvidence splitProblem.state m splitProblem.root (.node 57 []) := by
  intro m fit
  obtain ⟨packet,_,same,meaning⟩ :=
    checked_projected_report_has_canonical_dictionary_evidence426 projected_leaf_offered_report_is_real426
  have exactDictionary : packet.original.dictionary = .node 57 [] := by
    exact (CommonRoleOutermostResolver.Result.selected.inj
      (congrArg Check408.Result.verdict same)).symm
  simpa only [exactDictionary] using meaning m fit

theorem actual_split_has_no_legacy_classification_even_with_projected_dictionary_evidence426
    (R : SourcePrimitives) (d : Dictionary) :
    ¬ I72.Classifies R splitProblem.state splitProblem.root (.selected d) := by
  have noCenter : RecordEndpoints422.NoCenterRecord preparedSplit.original := by
    intro label field rest present
    have center : preparedSplit.original.arg.center = 1 := by decide +kernel
    rw [center] at present
    change (⟨1,.record label field rest⟩ : Equation) ∈ splitRows at present
    simp only [splitRows,List.mem_cons,List.not_mem_nil,or_false] at present
    rcases present with clash|clash|clash <;> cases clash
  refine RecordEndpoints422.primitives_only_cannot_add_genuine_nonpoint_record_selection422
    preparedSplit.original noCenter splitModel original_split_model_fits_with_exact_required_target_constraints425.1.1 ?_ R d
  have endpoints : (preparedSplit.original.arg.lower,preparedSplit.original.arg.upper) = (0,2) := by
    decide +kernel
  have lo := congrArg Prod.fst endpoints
  have hi := congrArg Prod.snd endpoints
  change preparedSplit.original.arg.lower = 0 at lo
  change preparedSplit.original.arg.upper = 2 at hi
  rw [lo,hi]
  change ¬ Equivalent (GeneralDeclarativeRecordSplit330.lo 20) (GeneralDeclarativeRecordSplit330.hi 20)
  intro forced
  exact GeneralDeclarativeRecordSplit330.no_literal 20 .bottom .exactEmpty
    ⟨CommonNominalFullCarrier.subtype_trans (GeneralDeclarativeRecordSplit330.interval 20).2 forced.2,
      (GeneralDeclarativeRecordSplit330.interval 20).1⟩

#print axioms projected_leaf_offered_report_is_real426
#print axioms actual_split_projection_has_canonical_dictionary_evidence426
#print axioms actual_split_has_no_legacy_classification_even_with_projected_dictionary_evidence426

end Yulang.GeneralDeclarativeI65.I72.ProjectedRetention423.MigrationSpec426
