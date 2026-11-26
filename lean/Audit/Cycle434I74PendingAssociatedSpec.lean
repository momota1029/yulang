import Yulang.GeneralDeclarativeI65I74PendingAssociatedNoCompletion434
import Yulang.GeneralDeclarativeWitnessUnfinished350

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 3000
namespace Yulang.GeneralDeclarativeI65.I72.PendingAssocAudit434
open GeneralDeclarativeI65 PendingAssociated434
open GeneralDeclarations (Declaration Clause OutputBinder)
open GeneralDeclarativeWitnessSparseVariance357 (Source compile)
open GeneralDeclarativeWitnessConstructorModes357 (Environment Use readUse)
open GeneralSourceMetadataBareBundle291 (InputBundle)
open GeneralSourceMetadataRows291 (Row)
open GeneralDeclarativeWitnessDeclaredState357 (point)
open CommonDeclaredNominalInspection (Parameter)
open CommonNominalFullCarrier (Ty nominal subtype_refl)
open Checker408 (Problem Result)
open WhereAssociated432 (invariantUnaryValuePlan432)

def listCtor : Nat := 40
def outputBinder : OutputBinder := ⟨9,50,51⟩
def recurse : Clause := ⟨50,20,[.var 8],[⟨51,6,.var 9⟩]⟩
def rhs : GeneralDeclarations.Equation := ⟨52,6,.app listCtor [.var 9]⟩
def rDecl : Declaration :=
  ⟨218,20,[.app listCtor [.var 8]],[recurse],[rhs],[outputBinder]⟩

private def bits : Source 0 0 0 := ⟨[],Fin.elim0,Fin.elim0⟩
private def bundle : InputBundle :=
  let constructors : List Row := [⟨listCtor,some ⟨[.type],listCtor⟩,.invariant⟩]
  ⟨⟨.absent,constructors⟩,⟨.absent,constructors⟩,⟨1,[⟨20,1,[(6,none)]⟩]⟩,[rDecl]⟩
private def env? : Option Environment := do
  let pp ← compile bits
  let cc ← GeneralSourceMetadataBareBundle291.compile bundle
  pure ⟨0,0,0,bits,pp,cc⟩
def env : Environment := env?.get (by decide +kernel)

def literalSeed : Origin := ⟨6,[72],sourceInput434 listCtor 4⟩
def separatelyAuthored : Origin := ⟨4,[14],sourceInput434 listCtor 8⟩

def raw (b : Nat) : GeneralDeclarativeHead320.State :=
  ⟨⟨[],[]⟩,[outerRow434 listCtor 6 4,retainedOutput434 listCtor 4 b,untouchedOutput434 b]⟩

def param : Parameter := ⟨.value,.invariant⟩
def normModes := List.replicate 40 [] ++ [[param]]
def core (b : Nat) (extra : List Origin) : GeneralDeclarativeI65.State :=
  ⟨⟨env,raw b,[]⟩,normModes,literalSeed :: extra,[]⟩

def listUse : Use env listCtor 1 := (readUse env listCtor 1).get (by decide +kernel)

def typed (b : Nat) (extra : List Origin) :
    B6MixedRhs401 (core b extra) false
      (GeneralDeclarationPatterns.normalize (GeneralDeclarativeOutputs320.bodyPattern (.explicit rhs))) :=
  invariantUnaryValuePlan432 listCtor outputBinder.name param listUse
    (by change GeneralDeclarativeWitnessSparseIntervals357.names listUse.mode 1 = some [param]; decide +kernel)
    (by change normModes[listCtor]? = some [param]; decide +kernel) rfl rfl

def atlas (b : Nat) (extra : List Origin) (includeOriginal : Bool) :
    B6OccurrenceAtlas401 (core b extra) :=
  ⟨fun q ordinal i body =>
    if includeOriginal && q.occurrence == [72] && ordinal == 0 && i.val == 0 then
      if source : body = .explicit rhs then some (source.symm ▸ typed b extra)
      else none
    else none⟩

def request (b : Nat) : Request := ⟨[72,0],⟨20,[point 4],[⟨6,b⟩]⟩⟩
def problem (b : Nat) (extra : List Origin := []) (includeOriginal : Bool := true) : Problem :=
  ⟨⟨core b extra,atlas b extra includeOriginal⟩,request b⟩

def wire : PendingAssociated434.Wire :=
  ⟨⟨[0,1,2,3,4,5,6,7,8],[2,2,2,2,1,2,0,2,1]⟩,
    ⟨[0,1,2,3,4,5,6,7,8],[2,2,2,2,0,2,2,2,1]⟩,
    [0,1,2,3,4,5,6,7,8]⟩

theorem literal_R_child_pending_through_R17_434 :
    check (problem 8) pendingReport (.pendingAssociated wire) = true := by decide +kernel

theorem actual_parent_requires_original_R_child_even_though_it_is_pending434 :
    ((replay434 (problem 8) wire).map fun o =>
      (o.original.parent.occurrence,o.original.episode.a,o.original.episode.b,
        (o.original.event.kids.map GeneralDeclarativeI65.Request.occurrence),
        o.original.parent.demand.arguments.map (fun x => x.lower))) =
      some ([72],4,8,[[72,0]],[6]) := by decide +kernel

theorem independently_authored_A_is_not_pending_from_just_output434 :
    check (problem 8 [separatelyAuthored]) pendingReport (.pendingAssociated wire) = false := by
  decide +kernel

theorem missing_actual_B6_source_or_wrong_occurrence_cannot_certify_pending434 :
    check (problem 8 [] false) pendingReport (.pendingAssociated wire) = false ∧
    check {problem 8 with root := ⟨[72,1],(request 8).demand⟩}
      pendingReport (.pendingAssociated wire) = false := by decide +kernel

def seedCycle : GeneralDeclarativeWitnessCycle350.Wire := ⟨0,⟨1,.same,4⟩,[],.same⟩
def oldRoot : ExplicitPick419.Witness :=
  .previous (.previous (.previous (.previous (.previous (.previous
    (.previous (.previous (.previous (.previous (.previous (.rawRoot seedCycle)))))))))))

def rawWitness : PendingAssociated434.Witness :=
  .previous (.previous (.previous (.previous (.previous (.previous oldRoot)))))

theorem same_unfinished_equation_creating_K2_uses_old_raw_first434 :
    check (problem 4) pendingReport (.pendingAssociated wire) = false ∧
    check (problem 4) Check408.rawReport rawWitness = true := by decide +kernel

theorem finite_original_R_example_report_has_no_output_or_selection434 :
    Classifies R17 (problem 8).state (request 8) .pending :=
  (verified_R17_result_classifies_in_same_State434 _ _ _
    literal_R_child_pending_through_R17_434).1

def fittingModel : I72.Model :=
  ⟨fun n => ((if n = 6 then nominal listCtor [.inl (nominal listCtor [.inl (.base .int)])]
                  else if n = 4 then nominal listCtor [.inl (.base .int)]
                  else .base .int),Common.rowEmpty),
    fun _ => none,fun n => if n = 6 then some literalSeed.endpoint else none⟩

theorem genuine_fitting_same_state_for_literal_R_pending434 : I72.Fits (problem 8).state fittingModel := by
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  · intro _ h; cases h
  · intro _ h; cases h
  · intro row h
    change row ∈ [outerRow434 listCtor 6 4,retainedOutput434 listCtor 4 8,untouchedOutput434 8] at h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl <;> exact ⟨subtype_refl _,subtype_refl _⟩
  · intro _ h; cases h
  · intro o h
    obtain rfl := List.mem_singleton.mp h
    rfl

theorem report_evidence_in_actual_fitting_state434 :
    ReportEvidence (problem 8).state fittingModel (request 8) pendingReport :=
  (check_sound _ _ _ literal_R_child_pending_through_R17_434).2 _
    genuine_fitting_same_state_for_literal_R_pending434

theorem actual_finite_R_path_cannot_be_completed434
    (d : CommonRoleOutermostResolver.Dictionary) :
    ¬ Classifies R17 (problem 8).state (request 8) (.selected d) :=
  checked_pending_is_not_selected434 literal_R_child_pending_through_R17_434 d

#print axioms actual_finite_R_path_cannot_be_completed434
#print axioms exact_episode_model_fits434
#print axioms original_pending_child_has_no_dictionary_in_fitting_model434
#print axioms original_pending_child_is_not_selected434
#print axioms original_pending_parent_has_no_selected_trace434

#print axioms literal_R_child_pending_through_R17_434
#print axioms actual_parent_requires_original_R_child_even_though_it_is_pending434
#print axioms independently_authored_A_is_not_pending_from_just_output434
#print axioms missing_actual_B6_source_or_wrong_occurrence_cannot_certify_pending434
#print axioms same_unfinished_equation_creating_K2_uses_old_raw_first434
#print axioms finite_original_R_example_report_has_no_output_or_selection434
#print axioms genuine_fitting_same_state_for_literal_R_pending434
#print axioms report_evidence_in_actual_fitting_state434
#print axioms exact_episode_has_no_finite_completion434
#print axioms previous_R16_entry_is_unchanged434
#print axioms check_sound
#print axioms dictionary_sound_R17
#print axioms real_raw_K2_refuses_pending_witness434
end Yulang.GeneralDeclarativeI65.I72.PendingAssocAudit434
