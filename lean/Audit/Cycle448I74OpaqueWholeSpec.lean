import Yulang.GeneralDeclarativeI65I74OpaqueWholeEntry448

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3600000
namespace Yulang.GeneralDeclarativeI65.I72.Opaque448.Whole.MixedSpec
open Yulang.GeneralDeclarativeI65
open GeneralDeclarativeWitnessSparseVariance357 (Source compile)
open GeneralDeclarativeWitnessConstructorModes357 (Environment Use readUse)
open GeneralDeclarativeWitnessSparseIntervals357 (names)
open GeneralDeclarations (Declaration)
open GeneralDeclarativeWhere319 (Capture)
open GeneralSourceMetadataBareBundle291 (InputBundle)
open GeneralSourceMetadataRows291 (Row)
open Checker408 (Result)
open Named409 (NamedHead VerifiedName)
open RetainedFull445
open VisibleInput
open Roster
open CommonRoleOutermostResolver (All₂)

def bodySource : Source 4 0 0 :=
  ⟨[⟨90,[]⟩,⟨91,[]⟩],
    fun i => if i.val = 0 then .union (.variant 3 (.inl 2)) (.variant 4 (.inl 3))
      else if i.val = 1 then .base .bool else if i.val = 2 then .nominal 90 [] else .base .unit,
    fun i => i.elim0⟩

def chosen : Declaration := ⟨88,7,[.app 90 []],[],[],[]⟩
def rival : Declaration := ⟨89,7,[.app 91 []],[],[],[]⟩
def matchingRival : Declaration := ⟨90,7,[.app 90 []],[],[],[]⟩

def inBase : InputBundle :=
  let rows : List Row := [⟨90,some ⟨[],90⟩,.unclassified⟩,⟨91,some ⟨[],91⟩,.unclassified⟩]
  ⟨⟨.absent,rows⟩,⟨.absent,rows⟩,⟨0,[⟨7,1,[]⟩]⟩,[]⟩

def ownRow : LocatedDeclaration := ⟨1,chosen⟩
def otherRow : LocatedDeclaration := ⟨2,rival⟩
def overlapRow : LocatedDeclaration := ⟨2,matchingRival⟩

def unloaded : CallerScope := ⟨[27],1,[],[88,89,90]⟩
def loaded : CallerScope := ⟨[27],1,[2],[88,89,90]⟩
def inaccessible : CallerScope := ⟨[27],1,[2],[88]⟩

def tracked : Origin := ⟨9,[42],.nominal 90 []⟩
def point : Capture := ⟨9,9,9⟩

def build (scope : CallerScope) (catalog : List LocatedDeclaration) : Option FullProblem := do
  let variance ← compile bodySource
  let book ← GeneralSourceMetadataBareBundle291.compile (projectInput inBase scope catalog)
  let environment : Environment := ⟨4,0,0,bodySource,variance,book⟩
  let core : GeneralDeclarativeI65.State :=
    ⟨⟨environment,⟨⟨[],[]⟩,[⟨9,.nominal 90 []⟩]⟩,[]⟩,
      List.replicate 92 [],[tracked],[]⟩
  let b6 : B6OccurrenceAtlas401 core := ⟨fun _ _ _ _ => none⟩
  pure (liftProblem ⟨⟨core,b6⟩,⟨scope.occurrence,⟨7,[point],[]⟩⟩⟩)

def mixed : FullProblem := (build loaded [otherRow,ownRow]).get (by decide +kernel)
def overlap : FullProblem := (build loaded [overlapRow,ownRow]).get (by decide +kernel)
def wire : NamedWire := ⟨0,⟨[],[0]⟩⟩
def expected : Result := Check408.nullaryReport chosen

def actual : WholeChoice mixed.old :=
  (readWholeChoice mixed.old wire).get (by decide +kernel)

theorem exact_mixed_whole_input448 :
    SameResolvedInput mixed inBase loaded [otherRow,ownRow] ∧
    visible mixed.state.base.core mixed.root = [rival,chosen] ∧
    actual.picked = chosen ∧ actual.tape.live = [chosen] ∧ actual.tape.waits = false := by
  have kept := bare_roster_keeps_all_hits_and_no_waits448 actual.point.known actual.roster
    (fun _ present => present)
  exact ⟨⟨rfl,rfl⟩,rfl,rfl,kept.1.trans actual.only,kept.2⟩

def rivalRead : BareRow mixed.state.base.core rival :=
  (readBareRow mixed.state.base.core rival).get (by decide +kernel)

def rivalMiss : RigidCandidateMiss mixed.state.base.core mixed.root rival :=
  rivalRead.mismatch actual.point.known (by decide +kernel)

theorem selected_after_genuine_rigid_rival_retains_ordinal_one448
    (origin : SelectedHeadOrigin395 (row := actual.picked) actual.tape) :
    origin.rawOrdinal = 1 := by
  have source := origin.authored
  change [rival,chosen][origin.rawOrdinal]? = some chosen at source
  cases loc : origin.rawOrdinal with
  | zero => simp [loc,rival,chosen] at source
  | succ k =>
    cases k with
    | zero => rfl
    | succ k => simp [loc] at source

def model : I72.Model :=
  ⟨fun _ => (CommonNominalFullCarrier.nominal 90 [],Common.rowEmpty),
    fun _ => none,fun n => if n = 9 then some (.nominal 90 []) else none⟩

theorem mixed_fits_full448 : FitsFull mixed.state model := by
  refine ⟨⟨⟨⟨⟨PresenceNormalForm.all_nil _ _,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩
  · intro _ absent; cases absent
  · intro item atRow
    have eq : item = (⟨9,.nominal 90 []⟩ : GeneralDeclarativeHead320.Equation) :=
      List.mem_singleton.mp atRow
    cases eq
    exact ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩
  · intro _ absent; cases absent
  · intro item atOrigin
    have eq : item = tracked := List.mem_singleton.mp atOrigin
    cases eq
    rfl
  · intro _ absent; cases absent

theorem real_other_name_is_not_a_match_in_the_same_model448
    (bad : SourceHead mixed.state.base.core mixed.root rival) : False :=
  rigid_candidate_excludes_a_source_head rivalMiss bad model mixed_fits_full448.1

theorem actual_mixed_roster_passes_cumulative_check448 :
    Whole.check_full448 mixed expected (.wholeBare wire) = true := by decide +kernel

theorem mixed_check_reports_sound_in_the_same_model448 :
    ReportEvidence448 mixed model expected :=
  (Whole.check_full_sound448 _ _ _ actual_mixed_roster_passes_cumulative_check448).2 _ mixed_fits_full448

theorem mixed_selected_dictionary_is_genuine448 :
    I72.DictionaryEvidence mixed.state.base model mixed.root (.node 88 []) := by
  obtain ⟨_,_,_,meaning⟩ := whole_choice_assembly448 actual
  exact meaning model mixed_fits_full448.1

def probe (program : Option FullProblem) (tag : Whole.Witness) (r : Result := expected) : Option Bool :=
  program.map fun p => Whole.check_full448 p r tag

/-- info: [some true, some true, some true, some false, some false, some true, some false] -/
#guard_msgs in
#eval [probe (build unloaded [overlapRow,ownRow]) (.wholeBare wire),
  probe (build loaded [otherRow,ownRow]) (.wholeBare wire),
  probe (build loaded [ownRow,otherRow]) (.wholeBare wire),
  probe (build loaded [overlapRow,ownRow]) (.wholeBare wire),
  probe (build loaded [otherRow,ownRow]) (.wholeBare wire) (Check408.nullaryReport rival),
  probe (build unloaded [overlapRow,ownRow]) (.previous (.opaqueName wire)),
  probe (build loaded [otherRow,ownRow]) (.previous (.opaqueName wire))]

#print axioms exact_mixed_whole_input448
#print axioms selected_after_genuine_rigid_rival_retains_ordinal_one448
#print axioms mixed_fits_full448
#print axioms real_other_name_is_not_a_match_in_the_same_model448
#print axioms actual_mixed_roster_passes_cumulative_check448
#print axioms mixed_check_reports_sound_in_the_same_model448
#print axioms mixed_selected_dictionary_is_genuine448

end Yulang.GeneralDeclarativeI65.I72.Opaque448.Whole.MixedSpec
