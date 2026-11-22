import Yulang.GeneralDeclarativeWitnessPointReplay349

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000
namespace Yulang.GeneralDeclarativeWitnessPointFixture349
open GeneralCandidateInspection (Primitive)
open GeneralSourceMetadataRows291 (Source)
open GeneralSourceMetadataBareBundle291 (InputBundle)
open GeneralDeclarations (Declaration)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWitnessPointInput349 (PointProblem)
open GeneralDeclarativeWitnessPointReplay349 (check obtained checked_result)
open GeneralDeclarativeWitnessTree349 (Report)
open GeneralDeclarativeWitnessGround349 (row)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarativeEvidence320 (Evidence)
open GeneralSourceMetadataBundle291 (registry)
open GeneralSourceMetadataRows291 (interpretation)

def kind : Primitive := .scalar .int
def tables : Source := ⟨.absent,[⟨11,some ⟨[],11⟩,.primitive kind⟩]⟩
def decl : Declaration := ⟨8,7,[.app 11 []],[],[],[]⟩
def input : InputBundle := ⟨tables,tables,⟨0,[⟨7,1,[(0,some (.app 11 []))]⟩]⟩,[decl]⟩
def state : State := ⟨⟨[],[]⟩,[row 0 kind,row 4 kind]⟩
def demand : Demand := ⟨7,[⟨0,0,0⟩],[⟨0,4⟩]⟩
def problem : PointProblem := ⟨⟨input,state,demand⟩,0,kind⟩

def answer : Report := ⟨.selected 8 [],.selected (.node 8 []),[⟨0,4⟩]⟩

theorem accepted : check problem answer = true := by decide +kernel

theorem wrong_target : check problem { answer with outputs := [⟨0,5⟩] } = false := rfl

theorem wrong_dictionary :
    check problem { answer with result := .selected (.node 8 [.node 8 []]) } = false := by decide +kernel

theorem wrong_diagnostic : check problem { answer with tree := .pending } = false := by decide +kernel

def missing : PointProblem :=
  { problem with problem := {problem.problem with state := ⟨⟨[],[]⟩,[row 4 kind]⟩} }

theorem no_source : check missing answer = false := rfl

def mismatch : PointProblem :=
  { problem with problem := {problem.problem with state := ⟨⟨[],[]⟩,[row 0 kind,row 4 (.scalar .str)]⟩} }

theorem no_receipt : check mismatch answer = false := rfl

def crowded : PointProblem :=
  { problem with problem := {problem.problem with source :=
    {input with declarations := [decl,{decl with id := 9}]} } }

theorem no_selection_claim : check crowded answer = false := rfl

def model : Assignment := fun _ => (.base .int,Common.rowEmpty)

theorem fixed_state_model : Models state model := by
  refine ⟨⟨?_,?_⟩,?_⟩
  · exact PresenceNormalForm.all_nil _ _
  · intro _ h
    cases h
  · intro e h
    change e ∈ [row 0 kind,row 4 kind] at h
    rcases List.mem_cons.mp h with here|there
    · subst e
      exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _
    · cases List.mem_singleton.mp there
      exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _

theorem nonvacuous :
    ∃ a : GeneralDeclarativeWitnessPointReplay349.Accepted problem answer,
      Models state model ∧ Evidence (registry a.table) (interpretation a.table.snapshot)
        model demand (.node a.impl.id []) := by
  obtain ⟨a⟩ := obtained accepted
  exact ⟨a,fixed_state_model,(checked_result a).2.2.2.2 model fixed_state_model⟩

end Yulang.GeneralDeclarativeWitnessPointFixture349
