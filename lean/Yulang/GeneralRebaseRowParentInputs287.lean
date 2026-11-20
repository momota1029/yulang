import Yulang.GeneralRebaseRowParentOutput287

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 12500000
namespace Yulang.GeneralRebaseRowParentInputs287
open GeneralRebaseRowChildSource287
open GeneralRebaseRowParentPacket287
open GeneralRebaseRowParentOutput287
open GeneralNominalVersionedPlans231 (Inputs Outputs Ordinary Holds SchemaHolds variables)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalOriginTerms (Same)
open GeneralNominalRecursiveInspection
open GeneralNominalCenters (Plan)
open GeneralDeclarations
open CommonNominalFullCarrier

abbrev parentOrigin : Origin := .nominal (.source 1) 0 0

theorem headSchema (choice : Bool) : (plan choice).headSchema =
    ⟨[⟨0,parentOrigin,.actual⟩],[(.source 1,.nominal 0 1)],false⟩ := by
  unfold Plan.headSchema
  rw [query]
  simp [GeneralNominalMaterialization.schemas,GeneralNominalMaterialization.schema,
    GeneralNominalMaterialization.Schema.append,plan,GeneralNominalCenters.rootSite,root,
    roles,GeneralDeclarationExamples.outputRole,List.ofFn_succ,parentOrigin]

theorem parent_actual (m : Assignment) (rawValid : GeneralNominalState.Models raw m) :
    Same m parentOrigin (.source 0) := by
  have seen := GeneralNominalRecursiveInspection.nominal_argument_bounds raw m rawValid 1 outer rfl 0 (0,0) rfl
  refine ⟨seen.1,⟨_,.source 0⟩,?_⟩
  intro a b ha hb
  cases hb
  exact ⟨(seen.2 a ha).2,(seen.2 a ha).1⟩

theorem head_holds (choice : Bool) (m : Assignment) (rawValid : GeneralNominalState.Models raw m) :
    SchemaHolds (plan choice) (plan choice).headSchema m := by
  rw [headSchema]
  constructor
  · intro item member
    cases List.mem_singleton.mp member
    obtain ⟨args,fit,equal⟩ := GeneralNominalState.nominal_models raw m rawValid 1 outer rfl
    have len : args.length = 1 := (GeneralNominalLinearMaterializationFacts.fitsAll_length _ _ _ _ fit)
    exact ⟨⟨_,.source 1⟩,by intro value observed; cases observed; exact ⟨args,len,equal⟩⟩
  · intro entry member
    cases List.mem_singleton.mp member
    simp only [ite_true,bound_name]
    exact parent_actual m rawValid

theorem ordinary (choice : Bool) (m : Assignment) : Ordinary (packet choice) m := by
  refine ⟨?_,?_,?_⟩
  · rw [GeneralRebaseRowParentPacket287.bindings]
    intro first one last two _
    cases List.mem_singleton.mp one
    cases List.mem_singleton.mp two
    exact subtype_refl _
  · unfold GeneralNominalVersionedAllocation231.merges
    rw [GeneralRebaseRowParentPacket287.bindings]
    intro atom present
    cases present
  · change PresenceNormalForm.All CommonNominalFullCarrier.model m
      (selfChecks raw (GeneralNominalPacketSupport.report (packet choice)))
    rw [parent_report]
    exact GeneralNominalUnaryCaptureFacts.self_models raw 1 0 0 (0,0) m (subtype_refl _)

theorem projection (choice : Bool) (m : Assignment) (h : GeneralNominalState.Models raw m) :
    ProjectionModels raw (GeneralNominalPacketSupport.report (packet choice)) m := by
  rw [parent_report]
  exact GeneralNominalUnaryCaptureFacts.projection_models raw m h 1 outer rfl 0 (0,0) rfl

theorem inputs_hold (choice : Bool) (m : Assignment) (valid : GeneralNominalState.Models raw m) :
    Inputs (plan choice) m := by
  refine ⟨ordinary choice m,projection choice m valid,?_,?_,head_holds choice m valid,?_,?_⟩
  · intro index
    exact ⟨subtype_refl _,subtype_refl _⟩
  · intro name used
    have identity : name = 0 := by
      rcases used with onHead | ⟨clause,member,inChild⟩
      · simpa [Declaration.inputNames,GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,GeneralDeclarationPatterns.variablesArgs,GeneralDeclarationPatterns.Pattern.variables] using onHead
      · change clause ∈ parentDecl.requirements at member
        cases List.mem_singleton.mp member
        simpa [GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,GeneralDeclarationPatterns.variablesArgs,GeneralDeclarationPatterns.Pattern.variables] using inChild
    subst name
    change GeneralNominalCaptureMerges.Fits m ((GeneralNominalVersionedFrame231.capture (packet choice)).inputs 0)
      (m (GeneralNominalVersionedFrame231.binder (plan choice) 0)).1
    rw [capture,bound_name]
    exact ⟨subtype_refl _,subtype_refl _⟩
  · rw [emitted]
    intro entry member noActual
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl
    · cases noActual rfl
    · change Equivalent (m 0).1 (variables (plan choice) m .lower 0)
      rw [variables_same]
      exact ⟨subtype_refl _,subtype_refl _⟩
    · change Equivalent (m 0).1 (variables (plan choice) m .upper 0)
      rw [variables_same]
      exact ⟨subtype_refl _,subtype_refl _⟩
  · intro clause member signature
    change clause ∈ parentDecl.requirements at member
    cases List.mem_singleton.mp member
    rw [child_schema,child_site]
    refine ⟨?_,?_⟩
    · intro i
      exact ⟨subtype_refl _,subtype_refl _⟩
    · intro entry member
      cases List.mem_singleton.mp member
      change Equivalent (m 0).1 (variables (plan choice) m .actual 0)
      rw [variables_same]
      exact ⟨subtype_refl _,subtype_refl _⟩

theorem parent_packet (choice : Bool) (m : Assignment) :
    Holds (plan choice) m ↔ GeneralNominalState.Models raw m ∧ Equivalent (m 2).1 (F (F (m 0).1)) :=
  ⟨fun h => ⟨h.1,(outputs_exact choice m).mp h.2.2⟩,
    fun h => ⟨h.1,inputs_hold choice m h.1,(outputs_exact choice m).mpr h.2⟩⟩

end Yulang.GeneralRebaseRowParentInputs287
