import Yulang.GeneralPositiveForkSource309
import Yulang.GeneralRebaseDisplayPacket276

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 23000
set_option maxHeartbeats 12500000
namespace Yulang.GeneralPositiveForkPlan309
open GeneralPositiveForkSource309
open GeneralDeclarationExamples (roles)
open GeneralNominalExamples (state context interpretation listDescriptor)
open GeneralNominalCenters
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
open GeneralDeclarations
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedPlans231
open GeneralNominalRecursiveInspection
open GeneralNominalVersionedFrame231 (capture binder childSite children)

abbrev packet : GeneralNominalSaturationState.Packet roles :=
  ⟨compiled,context true,GeneralNominalDemandMerging.pointSite root,parent,parent_checked,[(0,0)]⟩
abbrev plan : Plan roles := ⟨packet,rootSite (state true).seed root,rfl⟩
abbrev origin : Origin := .nominal (.source 0) 0 0
abbrev loSig : loClause.Signature roles := ⟨rfl,fun _ h => nomatch h⟩
abbrev hiSig : hiClause.Signature roles := ⟨rfl,fun _ h => nomatch h⟩
abbrev loSite := childSite plan loClause loSig
abbrev hiSite := childSite plan hiClause hiSig
abbrev kids : List (Occurrence roles) := [loSite.occurrence,hiSite.occurrence]

theorem query : GeneralNominalInspection.queries (state true) interpretation parent =
    [.nominal 0 [.variables [0]]] := GeneralNominalNonleafPlan193.query

theorem report : GeneralNominalPacketSupport.report packet =
    GeneralNominalUnaryCaptureFacts.captured (state true) 0 0 0 (1,1) :=
  GeneralNominalUnaryCaptureFacts.report_exact (context true) parent 0 listDescriptor rfl 0 (1,1) rfl query

theorem bindings : packet.bindings = [(0,(1,1))] := by
  change GeneralNominalRecursiveInspection.bindings _ (GeneralNominalPacketSupport.report packet) = _
  rw [report]
  rfl

theorem center : binder plan 0 = 1 := by
  rw [GeneralNominalVersionedFrame231.binder_eq]
  unfold Plan.binder GeneralNominalPacketSupport.capture
  simp only [show ¬ 0 ∈ parent.outputNames from by decide +kernel,ite_false]
  rw [bindings]
  rfl

theorem capture_exact : (capture packet).inputs 0 = (1,1) := by
  change (GeneralNominalVersionedAllocation231.capture _ _ _ _ packet.bindings).inputs 0 = _
  rw [bindings]
  rfl

theorem canonical_clauses :
    GeneralCanonicalChildOrder.canonicalRequirements parent.requirements = [loClause,hiClause] := by
  simp [GeneralCanonicalChildOrder.canonicalRequirements]

theorem emitted : GeneralNominalVersionedChildren232.emitted plan = [loSite,hiSite] := by
  unfold GeneralNominalVersionedChildren232.emitted
  let pick : Clause → Site roles := fun c => if c.id = 10 then loSite else hiSite
  calc
    _ = (GeneralCanonicalChildOrder.canonicalRequirements parent.requirements).attach.map
        (fun c => pick c.val) := by
      apply List.map_congr_left
      intro c _
      have h : c.val ∈ parent.requirements :=
        (GeneralCanonicalChildOrder.canonicalRequirements_perm _).mem_iff.mpr c.property
      rcases List.mem_cons.mp h with same|tail
      · rcases c with ⟨c,h⟩
        change c = hiClause at same
        subst c
        rfl
      · have same := List.mem_singleton.mp tail
        rcases c with ⟨c,h⟩
        change c = loClause at same
        subst c
        rfl
    _ = _ := by
      rw [List.attach_map_val,canonical_clauses]
      rfl

theorem ordered_children : children packet = kids := by
  rw [← GeneralNominalVersionedChildren232.emitted_occurrences plan,emitted]
  rfl

theorem args_low :
    ∀ i, loSite.occurrence.demand.arguments i = (1,1) := by decide +kernel
theorem args_high :
    ∀ i, hiSite.occurrence.demand.arguments i = (1,1) := by decide +kernel
theorem center_low : ∀ i, loSite.center i = 1 := by decide +kernel
theorem center_high : ∀ i, hiSite.center i = 1 := by decide +kernel

theorem vars (m : Assignment) : ∀ mode, variables plan m mode 0 = (m 1).1 := by
  intro mode
  unfold variables
  simp only [show ¬ 0 ∈ parent.outputNames from by decide +kernel,ite_false]
  cases mode <;> simp only [capture_exact,center]

theorem head_schema : plan.headSchema = GeneralNominalNonleafPlan193.plan.headSchema := rfl

theorem output_schema : emittedSchema plan =
    ⟨[⟨1,.actual,.variable 0⟩,⟨1,.lower,.variable 0⟩,⟨1,.upper,.variable 0⟩,
        ⟨1,.lower,.variable 0⟩,⟨1,.upper,.variable 0⟩],false⟩ := by
  change GeneralNominalCenteredHeadMatSchemas.generated _ _ (emittedRequests packet) = _
  unfold emittedRequests GeneralCanonicalChildOrder.canonicalEmit
  unfold GeneralNominalVersionedFrame231.capture GeneralNominalVersionedFrame231.frame
  rw [bindings]
  simp [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements]
  rfl

theorem child_schema (c : Clause) (member : c ∈ parent.requirements) (sig : c.Signature roles) :
    childSchema plan c sig = ⟨[⟨1,.actual,.variable 0⟩],false⟩ := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl
  all_goals
    unfold childSchema childRequests
    change GeneralNominalCenteredHeadMatSchemas.generated _ _ [⟨.var 0,_,.actual⟩] = _
  · rw [center_high (⟨0,by decide +kernel⟩)]; rfl
  · rw [center_low (⟨0,by decide +kernel⟩)]; rfl

theorem ordinary (m : Assignment) (valid : GeneralNominalState.Models (state true) m) :
    Ordinary packet m := by
  have old := (GeneralRebaseDisplayPacket276.ordinary_exact m valid)
  have same : GeneralNominalPacketSupport.report packet =
      GeneralNominalPacketSupport.report GeneralNominalNonleafPlan193.packet :=
    report.trans GeneralNominalNonleafPlan193.raw_report.symm
  refine ⟨?_,?_,?_⟩
  · rw [bindings,← GeneralNominalNonleafPlan193.bindings]
    exact old.1
  · unfold GeneralNominalVersionedAllocation231.merges
    rw [bindings]; intro _ h; cases h
  · rw [same]; exact old.2.2

theorem holds (m : Assignment) (valid : GeneralNominalState.Models (state true) m) : Holds plan m := by
  have old := GeneralRebaseDisplayPacket276.holds m valid
  have reports : GeneralNominalPacketSupport.report packet =
    GeneralNominalPacketSupport.report GeneralNominalNonleafPlan193.packet :=
    report.trans GeneralNominalNonleafPlan193.raw_report.symm
  have outputs : Outputs plan m := by
    unfold Outputs
    rw [output_schema]
    intro e member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl <;>
      change Equivalent (m 1).1 (variables plan m _ 0) <;>
      rw [vars] <;> exact ⟨subtype_refl _,subtype_refl _⟩
  refine ⟨valid,⟨ordinary m valid,?_,(point_root_holds _ _ (fun _ => rfl) m),?_,?_,fun e mem _ => outputs e mem,?_⟩,outputs⟩
  · rw [reports]; exact old.2.1.2.1
  · intro name used
    have zero : name = 0 := by
      rcases used with head|⟨c,member,used⟩
      · simpa [Declaration.inputNames,GeneralDeclarationPatterns.variablesArgs,
          GeneralDeclarationPatterns.Pattern.variables,GeneralDeclarationPatterns.normalizeArgs,
          GeneralDeclarationPatterns.normalize] using head
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl|rfl <;>
          simpa [GeneralDeclarationPatterns.variablesArgs,GeneralDeclarationPatterns.Pattern.variables,
            GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize] using used
    subst name
    rw [capture_exact,center]
    exact ⟨subtype_refl _,subtype_refl _⟩
  · have past := old.2.1.2.2.2.2.1
    rw [head_schema,GeneralNominalNonleafPlan193.head_schema] at *
    refine ⟨past.1,?_⟩
    intro u member
    cases List.mem_singleton.mp member
    simp only [ite_true,center]
    simpa only [ite_true,GeneralRebaseDisplayPacket276.center] using past.2 _ (List.mem_singleton_self _)
  · intro c member sig
    have schema := child_schema c member sig
    refine ⟨?_,?_⟩
    · intro i
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl
      · change Subtype (m (hiSite.occurrence.demand.arguments i).1).1 (m (hiSite.center i)).1 ∧
            Subtype (m (hiSite.center i)).1 (m (hiSite.occurrence.demand.arguments i).2).1
        rw [args_high,center_high]
        exact ⟨subtype_refl _,subtype_refl _⟩
      · change Subtype (m (loSite.occurrence.demand.arguments i).1).1 (m (loSite.center i)).1 ∧
            Subtype (m (loSite.center i)).1 (m (loSite.occurrence.demand.arguments i).2).1
        rw [args_low,center_low]
        exact ⟨subtype_refl _,subtype_refl _⟩
    · rw [schema]
      intro atom hit
      cases List.mem_singleton.mp hit
      change Equivalent (m 1).1 (variables plan m .actual 0)
      rw [vars]
      exact ⟨subtype_refl _,subtype_refl _⟩

end Yulang.GeneralPositiveForkPlan309
