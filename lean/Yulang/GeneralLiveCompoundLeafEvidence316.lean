import Yulang.GeneralLiveCompoundLeafProof316

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 24000
set_option maxHeartbeats 24000000
namespace Yulang.GeneralLiveCompoundLeafEvidence316
open GeneralDictionaryJournalRefinement228Source (roles root snapshot lower_width width_two)
open GeneralLiveCompoundRegistry316 (registry sourceRegistry declaration leaf leaf_checked source checked)
open GeneralLiveCompoundUpperRefresh316 (upperState old_models)
open GeneralLiveCompoundUpperSnapshot316 (snap context)
open GeneralLiveCompoundChildSite316
open GeneralLiveCompoundLeafHead316 (packet plan bindings head ordinary projection_empty)
open GeneralLiveCompoundLeafProof316
open GeneralSourceDictionaries GeneralNominalCenters GeneralDeclarations
open GeneralNominalVersionedPlans231
open GeneralNominalVersionedCandidates231 (Prepared Survivor Unique inputs)
open GeneralNominalRecursiveInspection
open GeneralNominalVersionedJournal232 (Models)
open CommonNominalFullCarrier

theorem known : ¬ GeneralNominalState.RootPending snap (inputs child).demand := by
  exact GeneralMixedCompoundUpperChild307.known

theorem fresh : GeneralNominalVersionedAllocation231.Fresh snap registry child.identity
    packet.bindings := by
  rw [GeneralLiveCompoundLeafHead316.bindings]
  have disjoint : ∀ key ∈ GeneralNominalVersionedAllocation231.keys registry child.identity [(0,4,2)],
      GeneralNominalIdentities.source snap.seed key ∉ GeneralNominalState.sources snap := by decide +kernel
  intro key member found
  exact False.elim (disjoint key member found)

theorem prepared : Prepared registry context child leaf := by
  refine ⟨source.metadata,⟨?_,by intro output member; cases member⟩,[(5,6)],located,?_,?_,w,head w valid⟩
  · intro index
    have size : index.val < 1 := index.isLt
    have same : index = 0 := Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ size))
    subst index
    exact ⟨GeneralNominalAllocationSupport.slot_source snap (5 : Fin 8),
      GeneralNominalAllocationSupport.slot_source snap (6 : Fin 8)⟩
  · change GeneralNominalVersionedAllocation231.Fresh snap registry child.identity packet.bindings
    exact fresh
  · rw [leaf_report]
    exact ⟨rfl,rfl,rfl⟩

theorem frame : GeneralNominalVersionedEvidence231.Frame registry upperState.core child leaf.id plan := by
  refine ⟨rfl,rfl,rfl,rfl,?_,?_,List.mem_cons_of_mem _ (List.mem_singleton_self _),rfl,located,prepared⟩
  · rw [raw_sites]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  · rw [centers]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)

theorem terminal : GeneralNominalVersionedFrame231.children packet = [] := by
  unfold GeneralNominalVersionedFrame231.children GeneralDictionaryEmissionPlans.children
    GeneralCanonicalChildOrder.canonicalEmit GeneralCanonicalChildOrder.canonicalDeclaration
    GeneralCanonicalChildOrder.canonicalRequirements GeneralDeclarationDemands.emitAll
  simp [List.mergeSort_nil]

theorem survivor : Survivor registry context child leaf.id [] :=
  ⟨known,leaf,List.mem_cons_of_mem _ (List.mem_singleton_self _),
    leaf_checked,rfl,rfl,[(5,6)],located,prepared,terminal.symm⟩

theorem unique : Unique registry context child leaf.id [] := by
  refine ⟨survivor,?_⟩
  intro key kids other
  have copy := other
  obtain ⟨_,d,visible,_,idEq,role,_,_,_,_⟩ := copy
  rcases List.mem_cons.mp visible with h | h
  · subst d; cases role
  · cases List.mem_singleton.mp h
    subst key
    exact ⟨rfl,GeneralNominalVersionedCandidates231.survivor_children_functional checked other survivor⟩

theorem emitted : emittedSchema plan = ⟨[],false⟩ := by
  unfold emittedSchema emittedRequests GeneralNominalMaterialization.rootRequests
  simp [GeneralCanonicalChildOrder.canonicalEmit,GeneralCanonicalChildOrder.canonicalDeclaration,
    GeneralCanonicalChildOrder.canonicalRequirements]
  rfl

theorem binders_fit : ∀ name ∈ leaf.inputNames,
    GeneralNominalCaptureMerges.Fits w ((GeneralNominalVersionedFrame231.capture packet).inputs name)
      (w (GeneralNominalVersionedFrame231.binder plan name)).1 := by
  intro name named
  have eq : name = 0 := List.mem_singleton.mp named
  subst name
  rw [selected_bounds,binder_exact,binder_value]
  have low := lower_width w valid.1.2.1
  have width := width_two w valid.1.2.1
  exact ⟨subtype_trans low width.1,width.2⟩

theorem holds : Holds plan w := by
  refine ⟨valid.1.1,⟨ordinary w valid,projection_empty w,valid.1.2.2.2.1 childSite ?_,?_,schema,?_,?_⟩,?_⟩
  · rw [centers]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  · intro name member
    rcases member with named | ⟨clause,present,_⟩
    · exact binders_fit name named
    · cases present
  · rw [emitted]; intro _ absent; cases absent
  · intro _ absent; cases absent
  · unfold Outputs; rw [emitted]; intro _ absent; cases absent

theorem certificate : GeneralNominalVersionedEvidence231.Certificate registry upperState.core w child leaf.id [] plan :=
  ⟨frame,terminal.symm,holds,by intro _ absent; cases absent⟩

theorem evidence : GeneralNominalVersionedEvidence231.Evidence registry upperState.core w child (.node leaf.id []) :=
  GeneralNominalVersionedEvidence231.evidence_leaf ⟨plan,certificate⟩

theorem ordered : GeneralVersionedChildDemandCut315.ChildDemand sourceRegistry upperState w [child] :=
  ⟨[.node leaf.id []],valid,.cons evidence .nil⟩

end Yulang.GeneralLiveCompoundLeafEvidence316
