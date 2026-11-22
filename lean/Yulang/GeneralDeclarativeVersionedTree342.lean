import Yulang.GeneralDeclarativeVersionedReceipt342
import Yulang.GeneralDeclarativeVersionedChildWitness342

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 18000
set_option maxHeartbeats 13000000
namespace Yulang.GeneralDeclarativeVersionedTree342
open GeneralWherePhysicalCommit319 (final newChild emission produced)
open GeneralWherePhysicalCurrentRead319 (plan)
open GeneralWherePhysicalCurrentPick319 (sourceRoot different_occ)
open GeneralWherePhysicalReobserve319 (updated)
open GeneralWhereOriginSingleCells318 (oldChild)
open GeneralWhereOriginSingleSource318 (sourceRegistry registry declaration)
open GeneralLiveCompoundRegistry316 (leaf)
open GeneralDeclarativeVersionedPhysical342 (current actual_children old_not_current same_id_not_occurrence new_registered)
open GeneralDeclarativeVersionedCurrent342 (current_parent)
open GeneralDeclarativeVersionedChildView342 (d actual_arguments)
open GeneralDeclarativeVersionedChildBody342 (expanded)
open GeneralDictionaryJournalRefinement228Source (root roles interpretation)
open GeneralNominalSaturationState (Alias)
open GeneralNominalCenteredHeadOutputs (requests)
open GeneralNominalCommonBridge (Assignment)
open GeneralWhereVersionInstall317 (Models)
open GeneralNominalVersionedEvidence231 (Frame Evidence)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalCenters (Site)
open GeneralDictionaryReadback (Payload erased_evidence_node)

theorem pre_not_after : plan.packet.context ≠ current.packet.context := by
  intro same
  have slots := congrArg (fun c : GeneralNominalCandidates.Context => c.state.base.slots) same
  change 7 = 8 at slots
  cases slots

theorem raw_sites :
    final.mixed.core.erased.current.sites = [sourceRoot.observed,oldChild.observed,newChild.observed] := by
  change updated.mixed.core.erased.current.sites ++ (GeneralWhereVersionInstall317.emitted plan).map Site.observed = _
  rw [GeneralWherePhysicalCurrentPick319.raw_sites,emission] <;> rfl

theorem identity_of_alias {x y : Nat} (linked : Alias final.mixed.core.erased.current x y) : x = y := by
  induction linked with
  | refl => rfl
  | edge there => change _ ∈ [] at there; cases there
  | symm _ h => exact h.symm
  | trans _ _ a b => exact a.trans b

theorem old_id : root.identity ≠ oldChild.occurrence.identity := by
  have less : root.identity < oldChild.occurrence.identity := by
    change root.identity < GeneralNominalIdentities.source _ (GeneralNominalAllocation.origin root.identity declaration.id 6 0 0)
    exact GeneralNominalIdentities.source_above_invocation
      GeneralWhereOriginSingleSource318.oldPlan.packet.context.state.seed
      (GeneralNominalAllocation.origin root.identity declaration.id 6 0 0)
  exact Nat.ne_of_lt less

theorem new_id : root.identity ≠ newChild.occurrence.identity := by
  intro h
  exact old_id (h.trans same_id_not_occurrence.1.symm)

theorem root_requests : requests final.mixed.core root = [⟨0,4⟩] := by
  classical
  unfold requests
  rw [raw_sites]
  have noOld : ¬ Alias final.mixed.core.erased.current root.identity oldChild.occurrence.identity :=
    fun a => old_id (identity_of_alias a)
  have noNew : ¬ Alias final.mixed.core.erased.current root.identity newChild.occurrence.identity :=
    fun a => new_id (identity_of_alias a)
  have own : Alias final.mixed.core.erased.current root.identity sourceRoot.observed.occurrence.identity := .refl _
  have empty : ([oldChild.observed,newChild.observed].filter fun site =>
    Alias final.mixed.core.erased.current root.identity site.occurrence.identity) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro site listed
    rcases List.mem_cons.mp listed with old | newer
    · subst site
      exact fun yes => noOld (of_decide_eq_true yes)
    · cases List.mem_singleton.mp newer
      exact fun yes => noNew (of_decide_eq_true yes)
  rw [List.filter_cons,decide_eq_true own]
  simp only [↓reduceIte,empty,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  rfl

theorem child_requests : requests final.mixed.core newChild.occurrence = [] := by
  unfold requests
  rw [raw_sites]
  have noRoot : ¬ Alias final.mixed.core.erased.current newChild.occurrence.identity sourceRoot.observed.occurrence.identity :=
    fun a => new_id (identity_of_alias a).symm
  have time : Alias final.mixed.core.erased.current newChild.occurrence.identity oldChild.observed.occurrence.identity := by
    rw [show oldChild.observed.occurrence.identity = oldChild.occurrence.identity from rfl,same_id_not_occurrence.1]
    exact .refl _
  have own : Alias final.mixed.core.erased.current newChild.occurrence.identity newChild.observed.occurrence.identity := .refl _
  simp [noRoot,time,own] <;> exact ⟨rfl,rfl⟩

theorem actual_place : GeneralDeclarativeStoppedPaired341.Placement final.mixed expanded newChild.occurrence d := by
  refine ⟨newChild,new_registered,rfl,?_⟩
  have demandEq : GeneralDeclarativeStoppedPaired341.activeDemand final.mixed newChild = d := by
    unfold GeneralDeclarativeStoppedPaired341.activeDemand
    rw [actual_arguments,child_requests] <;> rfl
  rw [demandEq]
  exact ⟨rfl,.cons ⟨GeneralDeclarativeLowerKnown321.alias_refl _,
    GeneralDeclarativeLowerKnown321.alias_refl _,GeneralDeclarativeLowerKnown321.alias_refl _⟩ .nil,rfl⟩

theorem actual_root_outputs (m : Assignment) (valid : Models final m) :
    ∀ out ∈ root.demand.outputs, GeneralDictionaryDefaultEvidence204.OutputWitness current m out := by
  intro out inside
  have frame := (current_parent m valid).1
  have ready := GeneralRebaseRetargetEffects275.ready (after := GeneralWherePhysicalActive319.ctx)
    plan GeneralWherePhysicalActive319.refines rfl final.mixed.core GeneralWherePhysicalEvidence319.ready
  apply GeneralDictionaryDefaultEvidence204Laws.output_of_class_effects ready
    ((GeneralNominalVersionedEffects231.class_effects_iff ..).mp (current_parent m valid).2.2)
  exact GeneralNominalCenteredHeadOutputs.request_retained current.packet.site frame.raw_recorded
    (by rw [frame.occurrence_eq]; exact .refl _) (frame.occurrence_eq.symm ▸ inside)

abbrev CurrentInstance (m : Assignment) : GeneralSourceDictionaries.LocalInstance roles :=
  fun focus key kids =>
    (focus = root ∧ key = declaration.id ∧ kids = GeneralWhereVersionCompiler317.children current ∧
      Frame registry final.mixed.core root declaration.id current ∧
      GeneralWhereVersionSemantics317.Holds current m ∧
      GeneralNominalVersionedEffects231.ClassEffects final.mixed.core root current m ∧
      (∀ out ∈ root.demand.outputs, GeneralDictionaryDefaultEvidence204.OutputWitness current m out) ∧
      ∀ kid ∈ GeneralWhereVersionCompiler317.children current,
        GeneralNominalSaturationState.Generated final.mixed.core.erased.current root kid) ∨
    GeneralNominalVersionedEvidence231.Instance registry final.mixed.core m focus key kids

/-- The actual current wrapper tree is built from the after-install
root Frame, not from the pre-install proof in the original C319
wrapper, and it recurses into the genuinely current generated child. -/
theorem modern_raw_tree (m : Assignment) (valid : Models final m) :
    GeneralSourceDictionaries.ErasedEvidence (CurrentInstance m) root (.node declaration.id [.node leaf.id []]) := by
  have parent : CurrentInstance m root declaration.id [newChild.occurrence] :=
    .inl ⟨rfl,rfl,actual_children.symm,(current_parent m valid).1,(current_parent m valid).2.1,
      (current_parent m valid).2.2,actual_root_outputs m valid,(old_not_current).2.2.2⟩
  have child : CurrentInstance m newChild.occurrence leaf.id [] :=
    .inr ⟨_,GeneralWherePhysicalChildCert319.certificate m valid⟩
  exact erased_evidence_node _ _ _ _ _ parent
    (.cons (erased_evidence_node _ _ _ _ _ child .nil) .nil)

end Yulang.GeneralDeclarativeVersionedTree342
