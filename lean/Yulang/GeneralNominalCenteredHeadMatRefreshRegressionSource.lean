import Yulang.GeneralNominalCenteredHeadMatStepComposition
import Yulang.GeneralNominalCenteredSourceUnsettledRefreshDecision

set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralNominalCenteredHeadMatRefreshRegressionSource
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredSourceUnsettledRefreshWitness
open GeneralNominalCenteredHeadMatStepJournal
open GeneralNominalCenteredHeadMatEffects
open GeneralNominalCenteredHeadMatExpressions
open GeneralNominalCenteredHeadMatSchemas
open CommonNominalFullCarrier

abbrev start : State roles := initial context root

theorem coverage : GeneralNominalCenteredHeadWFSource.Coverage registry interpretation := by
  have int : GeneralNominalCenteredHeadWFSource.ConstructorUse constructors interpretation 2 0 :=
    ⟨⟨[],2⟩,rfl,rfl,Or.inl ⟨.scalar .int,rfl,rfl⟩⟩
  have pair : GeneralNominalCenteredHeadWFSource.ConstructorUse constructors interpretation 5 2 :=
    ⟨⟨[.type,.type],5⟩,rfl,rfl,Or.inl ⟨.pair,rfl,rfl⟩⟩
  constructor
  · intro declaration member
    rcases List.mem_cons.mp member with rfl | member
    · refine ⟨⟨⟨pair,trivial,trivial,trivial⟩,trivial⟩,?_,?_⟩
      · intro clause member; cases List.mem_singleton.mp member
        exact ⟨⟨trivial,trivial⟩,by intro equation present; cases List.mem_singleton.mp present; trivial⟩
      · intro equation member; cases List.mem_singleton.mp member; exact ⟨int,trivial⟩
    · cases List.mem_singleton.mp member
      refine ⟨⟨⟨pair,⟨int,trivial⟩,trivial,trivial⟩,trivial⟩,?_,?_⟩
      · intro clause member; cases List.mem_singleton.mp member
        exact ⟨⟨trivial,trivial⟩,by intro equation present; cases present⟩
      · intro equation member; cases List.mem_singleton.mp member; trivial
  · intro role name body declared
    simp only [roles] at declared
    split at declared
    · simp at declared
    · simp at declared

theorem head_prepared : GeneralNominalCenteredHeadCandidates.Prepared registry context root p :=
  GeneralNominalCenteredHeadCandidates.old_prepared_head preparedP

theorem head_unique : GeneralNominalCenteredHeadCandidates.Unique registry context root p.id packetP.children := by
  have chosen := GeneralNominalCenteredHeadCandidates.old_survivor_head survivorP
  refine ⟨chosen,?_⟩
  intro key children found
  have copy := found
  obtain ⟨_,declaration,visible,_,keyEq,roleEq,_⟩ := copy
  have same := p_only declaration visible roleEq
  subst declaration
  have identity : key = p.id := keyEq.symm
  subst key
  exact ⟨rfl,GeneralNominalCenteredHeadCandidates.survivor_children_functional checked found chosen⟩

theorem frame : GeneralNominalCenteredHeadOutputs.Frame registry start.core root p.id planP :=
  ⟨rfl,rfl,rfl,rfl,List.mem_singleton_self _,List.mem_singleton_self _,
    List.mem_cons_self,rfl,locatedP,head_prepared⟩

theorem requests_start (member : output ∈ GeneralNominalCenteredHeadOutputs.requests start.core root) :
    output = ⟨0,2⟩ := by
  obtain ⟨site,present,_,within⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp member
  cases List.mem_singleton.mp present
  exact List.mem_singleton.mp within

theorem ready : Ready start.core root planP :=
  ready_of_wf coverage (List.mem_cons_self) rfl (by
    intro output member
    cases requests_start member
    exact ⟨none,rfl⟩)

def effectP : Effect roles := ⟨registry,start.core,planP,frame,head_unique,ready⟩
def installed : State roles := install start effectP

theorem emitted_schema : GeneralNominalCenteredHeadMatPlans.emittedSchema planP =
    { equations := [⟨2,.actual,.primitive (.scalar .int) []⟩,
      ⟨1,.lower,.variable 0⟩,⟨1,.upper,.variable 0⟩,⟨outputP,.actual,.variable 2⟩] } := by
  unfold GeneralNominalCenteredHeadMatPlans.emittedSchema
  rw [bindingsP]
  unfold requests
  simp only [GeneralCanonicalChildOrder.canonicalEmit,p_sorted]
  simp [GeneralNominalMaterialization.rootRequests,GeneralDeclarationDemands.emitAll,
    GeneralDeclarationDemands.emit,emissionRequests,inputRequests,
    GeneralDeclarationDemands.outputTarget,GeneralDeclarationDemands.inputInterval,
    GeneralDeclarationDemands.childDemand,Declaration.outputNames,GeneralNominalAllocation.capture,
    GeneralNominalAllocation.allocation,GeneralNominalAllocation.occurrences,
    GeneralNominalDemandMerging.pointSite,root,p,childR,List.ofFn_succ,normalize,generated,materialize,Schema.append,
    translate,translateMany,application,GeneralCandidateInspection.Primitive.parameters,
    constructors,GeneralDeclarationExamples.constructors,interpretation,outputP]

theorem child_schema (valid : childR.Signature roles) :
    GeneralNominalCenteredHeadMatPlans.childSchema planP childR valid =
      { equations := [⟨1,.actual,.variable 0⟩] } := by
  have requests : planP.childRequests childR valid = [⟨.var 0,1,.actual⟩] := by
    unfold Plan.childRequests
    change (List.ofFn fun index : Fin 1 => _) = _
    simp [List.ofFn_succ,childR]
    exact childP_center valid ⟨0,by change 0 < 1; omega⟩
  simp [GeneralNominalCenteredHeadMatPlans.childSchema,requests,generated,materialize,translate,Schema.append]

theorem variable_zero (model mode) : variables planP model mode 0 = (model 1).1 := by
  have capture : (GeneralNominalPacketSupport.capture packetP).inputs 0 = (1,1) := by
    unfold GeneralNominalPacketSupport.capture; rw [bindingsP]; rfl
  cases mode <;> simp [variables,show (0 : Nat) ∉ packetP.declaration.outputNames by decide +kernel,
    binderP_zero,capture]

theorem input_models (model : GeneralNominalCommonBridge.Assignment)
    (sourceValid : GeneralNominalState.Models source model) :
    GeneralNominalCenteredHeadMatStepPackets.Inputs planP model := by
  refine ⟨ordinaryP model,?_,point_root_holds source.seed root (fun _ => rfl) model,
    binderP_fits model,headSchemaP_holds model sourceValid,?_,?_⟩
  · rw [reportP_exact]; exact projectionP model
  · intro equation member nonactual
    rw [emitted_schema] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact False.elim (nonactual rfl)
    · change Equivalent (model 1).1 (variables planP model .lower 0)
      rw [variable_zero]; exact ⟨subtype_refl _,subtype_refl _⟩
    · change Equivalent (model 1).1 (variables planP model .upper 0)
      rw [variable_zero]; exact ⟨subtype_refl _,subtype_refl _⟩
    · exact False.elim (nonactual rfl)
  · intro clause member valid
    cases List.mem_singleton.mp member
    refine ⟨(childrenP_holds model _ (List.mem_singleton_self _) valid).1,?_⟩
    rw [child_schema]
    intro equation member
    cases List.mem_singleton.mp member
    change Equivalent (model 1).1 (variables planP model .actual 0)
    rw [variable_zero]; exact ⟨subtype_refl _,subtype_refl _⟩

theorem packet_model : GeneralNominalCenteredHeadMatStepPackets.Holds planP witness := by
  refine ⟨witness_source,input_models witness witness_source,?_⟩
  unfold GeneralNominalCenteredHeadMatStepPackets.Outputs
  rw [emitted_schema]
  intro equation member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact ⟨subtype_refl _,subtype_refl _⟩
  · change Equivalent (witness 1).1 (variables planP witness .lower 0)
    rw [variable_zero]; exact ⟨subtype_refl _,subtype_refl _⟩
  · change Equivalent (witness 1).1 (variables planP witness .upper 0)
    rw [variable_zero]; exact ⟨subtype_refl _,subtype_refl _⟩
  · change Equivalent (witness outputP).1 (variables planP witness .actual 2)
    rw [actual_variable,binderP_two]; exact ⟨subtype_refl _,subtype_refl _⟩

theorem emitted_exact : planP.emitted = [emittedChild] := by
  unfold Plan.emitted
  rfl

theorem aliases_eq {first last : Nat}
    (alias : GeneralNominalSaturationState.Alias installed.core.erased.current first last) : first = last := by
  induction alias with
  | refl => rfl
  | edge member => cases member
  | symm _ ih => exact ih.symm
  | trans _ _ one two => exact one.trans two

theorem requests_installed (member : output ∈ GeneralNominalCenteredHeadOutputs.requests installed.core root) :
    output = ⟨0,2⟩ := by
  obtain ⟨site,present,alias,within⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp member
  change site ∈ [_] ++ planP.emitted.map Site.observed at present
  rw [emitted_exact] at present
  rcases List.mem_append.mp present with prior | child
  · cases List.mem_singleton.mp prior
    exact List.mem_singleton.mp within
  · have same : site = emittedChild.observed := List.mem_singleton.mp child
    subst site
    exact False.elim (child_identity_not_root (aliases_eq alias).symm)

theorem class_effects (only : ∀ output ∈ GeneralNominalCenteredHeadOutputs.requests core root, output = ⟨0,2⟩) :
    ClassEffects core root planP witness := by
  constructor
  · intro output member body looked
    cases only output member
    have bodyEq : body = .explicit ⟨101,0,.app 2 []⟩ := Option.some.inj looked.symm
    subst body
    intro equation present
    have same : equation = ⟨2,.actual,.primitive (.scalar .int) []⟩ := List.mem_singleton.mp present
    subst equation
    exact ⟨subtype_refl _,subtype_refl _⟩
  · intro first one last two _
    cases only first one
    cases only last two
    exact ⟨subtype_refl _,subtype_refl _⟩

theorem start_model : Models start witness :=
  (point_initial_models (fun _ => rfl)).mpr witness_source

theorem installation_model : InstallationModels start effectP witness :=
  ⟨start_model,packet_model,⟨GeneralNominalCenteredHeadMatStepPackets.head_equations packet_model,
    class_effects (fun _ member => requests_start member)⟩,
    class_effects (fun _ member => requests_installed member),by intro prior member; cases member⟩

theorem installed_model : Models installed witness := (install_models rfl).mpr installation_model

end Yulang.GeneralNominalCenteredHeadMatRefreshRegressionSource
