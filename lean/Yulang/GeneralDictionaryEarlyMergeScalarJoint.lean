import Yulang.GeneralDictionaryEarlyMergeScalarClassification
import Yulang.GeneralDictionaryUnrecordedAliasLeafJoint

/-! Two distinct unrecorded scalar children in a real merged alias class.
They obtain Joint in one unchanged current journal assignment. -/
namespace Yulang.GeneralDictionaryEarlyMergeScalarJoint
open GeneralDictionaryEarlyMergeScalarExample GeneralDictionaryEarlyMergeScalarClassification
open GeneralNominalExamples (context model displayRoot intDisplay int_display_checked)
open GeneralDeclarationExamples (roles)
open GeneralNominalSaturationState GeneralNominalJointCandidates

noncomputable abbrev rootSite := GeneralNominalDemandMerging.pointSite displayRoot

theorem sites_exact : finish.current.sites = [rootSite,site 10,site 11] := by
  change [rootSite] ++ packet.children.map (GeneralNominalFeedbackSites.childSite packet) = _
  change [rootSite] ++ children.map (GeneralNominalFeedbackSites.childSite packet) = _
  rw [children_exact]; rfl

def ChildIdentity (identity : Nat) : Prop := identity = (child 10).identity ∨ identity = (child 11).identity

theorem alias_class {first last : Nat} (alias : Alias finish.current first last) :
    ChildIdentity first ↔ ChildIdentity last := by
  induction alias with
  | refl => rfl
  | @edge first last member =>
    have same : (first,last) = ((child 10).identity,(child 11).identity) := List.mem_singleton.mp member
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj same
    exact ⟨fun _ => Or.inr rfl,fun _ => Or.inl rfl⟩
  | symm _ ih => exact ih.symm
  | trans _ _ left right => exact left.trans right

theorem root_outside : ¬ ChildIdentity displayRoot.identity := by
  unfold ChildIdentity
  decide +kernel

theorem related_children (n : Nat) (which : n = 10 ∨ n = 11)
    (s : GeneralNominalDemandMerging.Site roles) (related : Related finish.current (child n) s) :
    s.occurrence = child 10 ∨ s.occurrence = child 11 := by
  have focusInside : ChildIdentity (child n).identity := by
    rcases which with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  have inside := (alias_class related.2).mp focusInside
  have member := related.1
  rw [sites_exact] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact False.elim (root_outside inside)
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem covered (n : Nat) (which : n = 10 ∨ n = 11) :
    GeneralDictionaryUnrecordedAliasLeafJoint.Covered registry finish (child n) intDisplay := by
  intro s related
  rcases related_children n which s related with same | same
  · rw [same]; exact ⟨Or.inr ⟨shape 10⟩,3,[],supported_child 10⟩
  · rw [same]; exact ⟨Or.inr ⟨shape 11⟩,3,[],supported_child 11⟩

theorem packets_grow (p : Packet roles) (member : p ∈ finish.current.packets) :
    GeneralDictionaryOrdinaryTrace.Extension p.context finish.current.context := by
  have same : p = packet := List.mem_singleton.mp member
  subst p
  exact GeneralDictionaryOrdinaryTrace.extension_trans (GeneralDictionaryOrdinaryTrace.packet_extension packet)
    (GeneralDictionaryOrdinaryTrace.merge_extension before.current (site 10) (site 11))

theorem joint (n : Nat) (which : n = 10 ∨ n = 11)
    (assignment : GeneralNominalCommonBridge.Assignment) (valid : Models finish.current assignment) :
    Joint registry finish.current (child n) 3 :=
  GeneralDictionaryUnrecordedAliasLeafJoint.covered_joint registry displayRoot (child n) finish
    (GeneralNominalSupportBoundary.reachable_formed registry finish displayRoot reachable) packets_grow
    intDisplay (by simp) int_display_checked (Or.inr ⟨shape n⟩) 3 [] (supported_child n)
    (covered n which) assignment valid

/-- Explicitly retain the supplied assignment in every alias site's branch,
not merely separate existential witnesses for the two Joint conclusions. -/
theorem same_assignment (n : Nat) (which : n = 10 ∨ n = 11)
    (assignment : GeneralNominalCommonBridge.Assignment) (valid : Models finish.current assignment) :
    ∀ s, Related finish.current (child n) s → BranchAt registry finish.current s.occurrence 3 assignment := by
  intro s related
  obtain ⟨leaf,key,kids,selected⟩ := covered n which s related
  exact GeneralDictionaryAliasTreeLocality.leaf_branch registry finish s.occurrence intDisplay (by simp)
    int_display_checked leaf key kids selected assignment valid

theorem distinct_children : (child 10).identity ≠ (child 11).identity := by
  decide +kernel

theorem children_aliased : Alias finish.current (child 10).identity (child 11).identity :=
  .edge (List.mem_singleton_self _)

theorem unrecorded (n : Nat) (which : n = 10 ∨ n = 11) :
    ¬ ∃ p ∈ finish.current.packets, p.site.occurrence = child n := by
  rintro ⟨p,member,same⟩
  have identical : p = packet := List.mem_singleton.mp member
  subst p
  have identity := congrArg GeneralSourceDictionaries.Occurrence.identity same
  apply root_outside
  rcases which with rfl | rfl
  · exact Or.inl identity
  · exact Or.inr identity

/-- Both actual sites are simultaneously certified in the same model. This
is a genuine reachable alias-adding merge, not two copies of one occurrence. -/
theorem actual_two_unrecorded_joints :
    B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry displayRoot finish ∧
    Models finish.current model ∧
    (child 10).identity ≠ (child 11).identity ∧
    Alias finish.current (child 10).identity (child 11).identity ∧
    Joint registry finish.current (child 10) 3 ∧ Joint registry finish.current (child 11) 3 ∧
    (¬ ∃ p ∈ finish.current.packets, p.site.occurrence = child 10) ∧
    (¬ ∃ p ∈ finish.current.packets, p.site.occurrence = child 11) :=
  ⟨reachable,finish_model,distinct_children,children_aliased,joint 10 (Or.inl rfl) model finish_model,
    joint 11 (Or.inr rfl) model finish_model,unrecorded 10 (Or.inl rfl),unrecorded 11 (Or.inr rfl)⟩
end Yulang.GeneralDictionaryEarlyMergeScalarJoint
