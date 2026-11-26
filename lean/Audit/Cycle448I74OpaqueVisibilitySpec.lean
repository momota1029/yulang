import Yulang.GeneralDeclarativeI65I74OpaqueVisibility448

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3600000
namespace Yulang.GeneralDeclarativeI65.I72.Opaque448.Spec
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
open CommonRoleOutermostResolver (All₂)

def bodySource : Source 3 0 0 :=
  ⟨[⟨90,[]⟩],
    fun i => if i.val = 0 then .union (.variant 3 (.inl 1)) (.variant 4 (.inl 2))
      else if i.val = 1 then .nominal 90 [] else .base .unit,
    fun i => i.elim0⟩

def chosen : Declaration := ⟨88,7,[.app 90 []],[],[],[]⟩
def rival : Declaration := ⟨89,7,[.app 90 []],[],[],[]⟩

def inBase : InputBundle :=
  let rows : List Row := [⟨90,some ⟨[],90⟩,.unclassified⟩]
  ⟨⟨.absent,rows⟩,⟨.absent,rows⟩,⟨0,[⟨7,1,[]⟩]⟩,[]⟩

def ownRow : LocatedDeclaration := ⟨1,chosen⟩
def otherRow : LocatedDeclaration := ⟨2,rival⟩

def unloaded : CallerScope := ⟨[27],1,[],[88,89]⟩
def loaded : CallerScope := ⟨[27],1,[2],[88,89]⟩
def inaccessible : CallerScope := ⟨[27],1,[2],[88]⟩

def tracked : Origin := ⟨9,[42],.nominal 90 []⟩
def point : Capture := ⟨9,9,9⟩

def build (scope : CallerScope) (catalog : List LocatedDeclaration) : Option FullProblem := do
  let variance ← compile bodySource
  let book ← GeneralSourceMetadataBareBundle291.compile (projectInput inBase scope catalog)
  let environment : Environment := ⟨3,0,0,bodySource,variance,book⟩
  let core : GeneralDeclarativeI65.State :=
    ⟨⟨environment,⟨⟨[],[]⟩,[⟨9,.nominal 90 []⟩]⟩,[]⟩,
      List.replicate 91 [],[tracked],[]⟩
  let b6 : B6OccurrenceAtlas401 core := ⟨fun _ _ _ _ => none⟩
  pure (liftProblem ⟨⟨core,b6⟩,⟨scope.occurrence,⟨7,[point],[]⟩⟩⟩)

def hiddenProblem : FullProblem := (build unloaded [ownRow,otherRow]).get (by decide +kernel)
def rivalProblem : FullProblem := (build loaded [ownRow,otherRow]).get (by decide +kernel)

theorem recursive_body_is_still_present448 : bodySource.bodies 1 = .nominal 90 [] := rfl

theorem hidden_projection_is_the_actual_full_state448 :
    build unloaded [ownRow] = build unloaded [ownRow,otherRow] ∧
    build inaccessible [ownRow,otherRow] = build unloaded [ownRow,otherRow] ∧
    SameResolvedInput hiddenProblem inBase unloaded [ownRow,otherRow] ∧
    SameResolvedInput rivalProblem inBase loaded [ownRow,otherRow] := by
  exact ⟨rfl,rfl,⟨rfl,rfl⟩,⟨rfl,rfl⟩⟩

theorem call_sees_exactly_the_real_roles448 :
    visible hiddenProblem.state.base.core hiddenProblem.root = [chosen] ∧
    visible rivalProblem.state.base.core rivalProblem.root = [chosen,rival] := ⟨rfl,rfl⟩

def wire : NamedWire := ⟨0,⟨[],[0]⟩⟩
def expected : Result := Check408.nullaryReport chosen

theorem hidden_same_role_accepted448 :
    check_full448 hiddenProblem expected (.opaqueName wire) = true := by decide +kernel

theorem loaded_visible_matching_rival_refuses_old_report448 :
    ∀ w, check_full448 rivalProblem expected (.opaqueName w) = false := by
  intro w
  exact local_opaque_declines_nonsingleton448 (by decide +kernel) w

def model : I72.Model :=
  ⟨fun _ => (CommonNominalFullCarrier.nominal 90 [],Common.rowEmpty),
    fun _ => none,fun n => if n = 9 then some (.nominal 90 []) else none⟩

theorem hidden_problem_has_actual_model448 : FitsFull hiddenProblem.state model := by
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

theorem same_fitting_model_consumes_actual_selected_report448 :
    ReportEvidenceFull hiddenProblem.state model hiddenProblem.root expected :=
  (check_full_sound448 _ _ _ hidden_same_role_accepted448).2 _ hidden_problem_has_actual_model448

private abbrev RState := rivalProblem.state.base.core
private abbrev RReq := rivalProblem.root

private def sourceUse : Use RState.current.environment 90 0 :=
  (readUse RState.current.environment 90 0).get (by decide +kernel)

private theorem sourceMode : names sourceUse.mode 0 = some [] := by decide +kernel
private theorem sourceTable : RState.modes[90]? = some [] := by decide +kernel

private def sameBareHead (d : Declaration) (head : d.head = [.app 90 []]) :
    SourceHead RState RReq d := by
  refine .ordered (fun _ => emptyCapture403) ?_
  rw [head]
  change All₂ (DeepHead RState (fun _ => emptyCapture403)) [point] [.app 90 []]
  let cmp : DeclaredComparison RState.current.environment RState.current.ordinary RState.modes false
    (.nominal 90 []) (.nominal 90 []) := by
      refine ⟨?_,.nominal sourceTable (.nil false),.nominal sourceTable (.nil false),
        .nominal sourceTable .nil⟩
      intro site visitedSite
      have at90 : site = (90,0) := by
        simpa [GeneralDeclarativeWitnessSparseIntervals357.visited.eq_def,
          GeneralDeclarativeWitnessSparseIntervals357.visitedList.eq_def] using visitedSite
      subst site
      exact ⟨sourceUse,[],sourceMode,sourceTable⟩
  let read : ModeWindow RState point (.app 90 []) :=
    ⟨tracked,tracked,.direct,.direct,List.mem_cons_self,List.mem_cons_self,
      90,[],rfl,[],[],rfl,rfl,cmp⟩
  refine .cons (.declared (found := []) read ?_) .nil
  exact .nominal sourceUse sourceMode sourceTable .nil

private theorem rivalry_header_is_valid (d : Declaration)
    (h : RetainedSplit446.LocalHeader.selectedHeader RState.current.environment d = true) :
    d.requirements = [] ∧ GeneralDeclarativeWitnessModeCoverage357.DeclarationCovered RState.current.environment d ∧
      GeneralDeclarations.DeclarationChecked
        (GeneralDeclarativeWitnessDeclaredState357.authoredRegistry RState.current).constructors
        (GeneralDeclarativeWitnessDeclaredState357.authoredRegistry RState.current).roles d :=
  (RetainedSplit446.LocalHeader.selected_header_exact446 RState.current d).mp h

def genuineFirst : AuthoredCandidate RState RReq chosen :=
  let header := rivalry_header_is_valid chosen (by decide +kernel)
  ⟨List.mem_cons_self,header.2.1,header.2.2.signature,sameBareHead chosen rfl⟩

def genuineRival : AuthoredCandidate RState RReq rival :=
  let header := rivalry_header_is_valid rival (by decide +kernel)
  ⟨List.mem_cons_of_mem _ List.mem_cons_self,header.2.1,header.2.2.signature,sameBareHead rival rfl⟩

def actualRivalTape : CandidateTape RState RReq (visible RState RReq) :=
  .next (.matched genuineFirst) (.next (.matched genuineRival) .nil)

theorem both_actual_opaque_heads_match448 :
    actualRivalTape.live = [chosen,rival] ∧ actualRivalTape.waits = false ∧ chosen.id ≠ rival.id :=
  ⟨rfl,rfl,by decide⟩

theorem two_actual_matches_cannot_yield_old_selected_tape448 :
    ¬TapedMatch RState RReq actualRivalTape chosen := by
  intro accepted
  have shape := both_actual_opaque_heads_match448.1.symm.trans accepted.one
  have lengths := congrArg List.length shape
  cases lengths

def probe (program : Option FullProblem) (w : NamedWire := wire) (r : Result := expected) : Option Bool :=
  program.map fun p => check_full448 p r (.opaqueName w)

/-- info: [some true, some true, some true, some false, some false, some false] -/
#guard_msgs in
#eval [probe (build unloaded [ownRow]),probe (build unloaded [ownRow,otherRow]),
  probe (build inaccessible [ownRow,otherRow]),probe (build loaded [ownRow,otherRow]),
  probe (build unloaded [ownRow,otherRow]) ⟨1,⟨[],[0]⟩⟩,
  probe (build unloaded [ownRow,otherRow]) wire (Check408.nullaryReport rival)]

#print axioms recursive_body_is_still_present448
#print axioms hidden_projection_is_the_actual_full_state448
#print axioms call_sees_exactly_the_real_roles448
#print axioms hidden_same_role_accepted448
#print axioms loaded_visible_matching_rival_refuses_old_report448
#print axioms hidden_problem_has_actual_model448
#print axioms same_fitting_model_consumes_actual_selected_report448
#print axioms both_actual_opaque_heads_match448
#print axioms two_actual_matches_cannot_yield_old_selected_tape448

end Yulang.GeneralDeclarativeI65.I72.Opaque448.Spec
