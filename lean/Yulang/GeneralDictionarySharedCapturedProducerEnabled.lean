import Yulang.GeneralDictionarySharedCapturedPreparation
import Yulang.GeneralDictionaryFeedbackEvidence

/-! Finite-rank K2 exclusion, unique producer selection, and current-journal
installation obligations for the captured-input producer. This module proves
enablement; the Shared guard and actual installation are separate. -/
namespace Yulang.GeneralDictionarySharedCapturedProducerEnabled
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalRecursiveInspection GeneralNominalRecursiveCandidates
open GeneralDictionarySharedOutputBinderScope GeneralDictionarySharedCapturedTargets
open GeneralDictionarySharedCapturedModel GeneralDictionarySharedCapturedRefresh
open GeneralDictionarySharedCapturedProducer GeneralDictionarySharedCapturedPreparation
open GeneralDeclarationExamples (roles)

def depth (i : Nat) : Nat := if i = lo ∨ i = hi then 1 else 2-i

theorem model_depth (i : Nat) : (model i).1 = GeneralNominalOutputGrowth.tower (depth i) := by
  simp only [model,depth]
  split <;> rfl

theorem no_feedback (identity : Nat) : ¬ GeneralNominalFeedbackK2.Cycle refreshed.current identity :=
  GeneralNominalOutputGrowthModels.feedback_acyclic refreshed.current model inhabited depth model_depth
    (by rintro _ _ ⟨_,_,⟨kind,_,_,_⟩,_,_⟩; exact Fin.elim0 kind) identity

theorem no_raw (slot : Fin snapshot.base.slots) : ¬ GeneralNominalCycleK2.Cycle snapshot slot := by
  have decreases : ∀ first last, GeneralNominalCycleK2.Edge snapshot first last →
      depth (snapshot.base.source last) < depth (snapshot.base.source first) := by
    intro first last edge
    rcases edge with ⟨kind,_,_,_,_⟩ | ⟨d,_,index,observed⟩
    · exact Fin.elim0 kind
    · obtain ⟨actual,seen,same⟩ := observed model inhabited.1
      exact GeneralNominalOutputGrowthModels.observation_decreases model depth model_depth
        _ _ d.declaration.name index actual seen same
  have paths : ∀ first last, GeneralNominalCycleK2.Path snapshot first last →
      depth (snapshot.base.source last) ≤ depth (snapshot.base.source first) := by
    intro first last path
    induction path with
    | nil => exact Nat.le_refl _
    | cons edge _ ih => exact Nat.le_trans ih (Nat.le_of_lt (decreases _ _ edge))
  rintro ⟨next,edge,path⟩
  have one := decreases _ _ edge
  have two := paths _ _ path
  omega

theorem no_root : ¬ GeneralNominalFeedbackK2.RootK2 refreshed.current producer := by
  rintro (⟨_,_,_,slot,_,cycle⟩ | ⟨_,_,_,cycle,_⟩)
  · exact no_raw slot (GeneralNominalCycleK2.recurs_cycle _ _ cycle)
  · exact no_feedback _ cycle

theorem no_candidate : ¬ GeneralNominalFeedbackK2.CandidateK2 registry refreshed.current producer := by
  rintro (⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩ | ⟨_,_,_,_,_,_,_,_,visited,_,cycle,_⟩)
  · exact no_raw visited.1 (GeneralNominalCycleK2.recurs_cycle _ _ cycle)
  · exact no_feedback _ cycle

theorem declaration_only (d : Declaration) (visible : d ∈ registry.declarations)
    (role : d.role = producer.demand.role) : d = declaration := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
  rcases visible with rfl | rfl
  · cases role
  · rfl

theorem selected : GeneralNominalFeedbackK2.Local registry refreshed.current producer
    (.selected declaration.id candidate.children) := by
  refine .selected ⟨producer_ready,no_root,no_candidate,?_⟩ ⟨survivor,?_⟩
  · rintro (pending | ⟨_,legacy⟩)
    · obtain ⟨_,d,visible,certified,role,failed,missing⟩ := pending
      have same := declaration_only d visible role
      subst d
      exact missing prepared
    · rcases legacy with ⟨⟨_,_,_,slot,_,cycle⟩,_⟩ | ⟨⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩,_⟩
      · obtain ⟨⟨kind,_,_⟩,_⟩ := cycle; exact Fin.elim0 kind
      · obtain ⟨⟨kind,_,_⟩,_⟩ := cycle; exact Fin.elim0 kind
  · intro key kids found
    have copy := found
    obtain ⟨_,d,visible,certified,identity,role,_⟩ := found
    have same := declaration_only d visible role
    subst d
    subst key
    exact ⟨rfl,survivor_children_functional registry registry_checked refreshedContext producer declaration.id kids candidate.children copy survivor⟩
theorem sites : refreshed.current.sites =
    [GeneralNominalDemandMerging.pointSite root,
      GeneralNominalSharedEmission.childSite packet producer,
      GeneralNominalSharedEmission.childSite packet consumer] := by
  change [GeneralNominalDemandMerging.pointSite root] ++
    packet.children.map (GeneralNominalSharedEmission.childSite packet) = _
  rw [GeneralDictionarySharedCapturedInstallation.children]
  rfl

theorem packets : refreshed.current.packets = [packet] := rfl

theorem alias_identity (related : Alias refreshed.current first last) : first = last := by
  induction related with
  | refl => rfl
  | edge member => cases member
  | symm _ ih => exact ih.symm
  | trans _ _ one two => exact one.trans two

theorem producer_ne_root : producer.identity ≠ root.identity := by
  have above := GeneralNominalIdentities.source_above_seed 2
    (GeneralNominalAllocation.origin root.identity capturedProposal.id 6 producerOnInput.id 0)
  change 2 < producer.identity at above
  change producer.identity ≠ 0
  omega

theorem producer_ne_consumer : producer.identity ≠ consumer.identity := by
  intro equal
  have same := (GeneralNominalAllocation.source_identity source registry root.identity _ _).mp equal
  have clause := congrArg (fun origin => origin.2.2.2.1) same
  cases clause

theorem site_identity (other : GeneralNominalDemandMerging.Site roles) (member : other ∈ refreshed.current.sites)
    (identity : other.occurrence.identity = producer.identity) : other = candidate.site := by
  rw [sites] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact False.elim (producer_ne_root identity.symm)
  · rfl
  · exact False.elim (producer_ne_consumer identity.symm)

theorem site_role (other : GeneralNominalDemandMerging.Site roles) (member : other ∈ refreshed.current.sites)
    (role : other.occurrence.demand.role = producer.demand.role) : other = candidate.site := by
  rw [sites] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · cases role
  · rfl
  · cases role

theorem prior_unrelated (prior : Packet roles) (member : prior ∈ refreshed.current.packets) :
    ¬ Alias refreshed.current producer.identity prior.site.occurrence.identity := by
  intro related
  rw [packets] at member
  cases List.mem_singleton.mp member
  exact producer_ne_root (alias_identity related)

theorem joint : GeneralNominalJointCandidates.Joint registry refreshed.current producer declaration.id := by
  have one : GeneralNominalJointCandidates.BranchAt registry refreshed.current producer declaration.id model :=
    ⟨declaration,by simp,GeneralDictionaryRecursiveObstruction.declaration_checked,rfl,rfl,prepared,
      [(⟨3,by decide +kernel⟩,⟨4,by decide +kernel⟩)],bounds,branch_models⟩
  refine ⟨?_,model,inhabited,one,?_⟩
  · intro prior member related
    exact False.elim (prior_unrelated prior member related)
  · intro other related
    have same := site_identity other related.1 (alias_identity related.2).symm
    subst other
    exact one

theorem merges_closed : GeneralNominalFeedbackSteps.MergesClosed refreshed.current candidate.site := by
  intro other member same
  have equal := site_role other member same.1.symm
  subst other
  exact .refl _

theorem legacy_merges_closed : GeneralNominalCycleSteps.MergesClosed refreshed.current candidate.site := by
  intro other member same
  exact merges_closed other member (GeneralDictionaryFeedbackEvidence.sameInputs_recovered refreshed.current candidate.site other same)

/-- The producer is enabled in the actual two-step Shared journal, not a hypothetical selected state. -/
theorem enabled : GeneralNominalFeedbackSteps.Installable registry refreshed.current candidate := by
  refine ⟨⟨rfl,rfl,?_,by simp,rfl,bounds,prepared,
    GeneralNominalFeedbackK2.selected_legacy selected,?_,legacy_merges_closed,
    ⟨model,inhabited,branch_models⟩,joint⟩,selected,merges_closed⟩
  · rw [sites]; simp
  · intro prior member related
    exact False.elim (prior_unrelated prior member related)

end Yulang.GeneralDictionarySharedCapturedProducerEnabled
