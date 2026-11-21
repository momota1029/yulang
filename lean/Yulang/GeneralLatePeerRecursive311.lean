import Yulang.GeneralLatePeerTransfer311

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32000
set_option maxHeartbeats 21500000
namespace Yulang.GeneralLatePeerRecursive311
open GeneralLatePeerSource311 (compiled checked registry root)
open GeneralLatePeerRoot311 (direct branch)
open GeneralLatePeerRoutePlan311 (child)
open GeneralLatePeerRouteInstall311 (emitted)
open GeneralLatePeerMerge311 (final reached context_same center_sites)
open GeneralLatePeerCurrent311 (inhabited leaf_evidence clear)
open GeneralNominalVersionedEvidence231 (Frame Certificate Evidence)
open GeneralNominalVersionedInstallation231 (replayPlan replay_children)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary Local)
open GeneralNominalCommonBridge (Assignment)
open GeneralGeneratedNestedSource299 (model)
open GeneralSourceDictionaries (Occurrence)
open GeneralDeclarationExamples (roles)
open GeneralNominalCenteredHeadOutputs (requests)
open GeneralNominalSaturationState (Generated)
open CommonRoleOutermostResolver (Tree Resolves All₂)

abbrev plan := replayPlan GeneralLatePeerRouteInstall311.plan

theorem branch_frame : Frame compiled final.core branch.occurrence 3 plan := by
  have initialFrame : Frame compiled emitted.core branch.occurrence 3 plan :=
    GeneralNominalVersionedInstalledEvidence233.frame (effect := GeneralLatePeerRouteInstall311.effect)
      rfl GeneralLatePeerRouteInstall311.inhabited
  exact (GeneralNominalVersionedFrameTransport232.frame_forward
    (before := emitted.core) (after := final.core) context_same.symm
    (List.Subset.refl _) (List.Subset.refl _) initialFrame)

theorem branch_order : GeneralLatePeerGuard311.children plan = [child.occurrence] :=
  (replay_children GeneralLatePeerRouteInstall311.plan).trans GeneralLatePeerRouteInstall311.peer_list

theorem branch_holds (m : Assignment) (valid : Models final m) :
    GeneralNominalVersionedPlans231.Holds plan m :=
  GeneralNominalVersionedInstalledEvidence233.replay_holds (effect := GeneralLatePeerRouteInstall311.effect)
    ((GeneralLatePeerMerge311.models m).mp valid)

theorem branch_admin : GeneralNominalVersionedDiagnostic232.AdministrativeReady final branch.occurrence := by
  refine ⟨⟨branch,branch_frame.center_recorded,rfl⟩,?_⟩
  intro a one occ b two same
  change a ∈ emitted.core.sites at one
  change b ∈ emitted.core.sites at two
  rw [center_sites] at one two
  simp only [List.mem_cons,List.not_mem_nil,or_false] at one two
  have ident := congrArg Occurrence.identity occ
  rcases one with rfl|rfl|rfl|rfl
  · exact False.elim (GeneralLatePeerFresh311.branch_different ident.symm)
  · exact False.elim (GeneralLatePeerFresh311.distinct_child ident.symm)
  · rcases two with rfl|rfl|rfl|rfl
    · cases same.1
    · cases same.1
    · exact .refl _
    · cases same.1
  · exact False.elim (GeneralLatePeerMerge311.child_branch ident)

theorem branch_classes (m : Assignment) :
    GeneralNominalVersionedEffects231.ClassEffects final.core branch.occurrence plan m := by
  apply GeneralRebaseDisplayFrame276.classes_empty
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro out listed
  have old := (GeneralLatePeerMerge311.request_eq branch.occurrence
    (Ne.symm GeneralLatePeerMerge311.child_branch) out).mp listed
  exact GeneralLatePeerFresh311.distinct_child (GeneralLatePeerMerge311.old_request_identity _ _ old).2

theorem branch_known : GeneralLatePeerGuard311.Known final branch.occurrence := by
  rintro ⟨i,unknown⟩
  exact unknown ⟨(1 : Fin 3),(congrArg Prod.fst (GeneralLatePeerRoot311.route_args i)).symm,
    Or.inr ⟨GeneralGeneratedNestedSource299.listDescriptor 2,rfl⟩⟩

theorem branch_selected : Local registry final branch.occurrence (.selected 3 [child.occurrence]) := by
  have selected := GeneralLatePeerGuard311.select reached branch_frame branch_known rfl inhabited branch_admin
    (branch_holds model inhabited) (branch_classes model) (clear _)
  rw [branch_order] at selected
  exact selected

theorem peer_selected : Local registry final child.occurrence (.selected 2 []) := by
  have selected := GeneralLatePeerCurrent311.picked
  rw [show GeneralLatePeerGuard311.children GeneralLatePeerFinalPeerPlan311.plan = []
    from GeneralLatePeerFinalPeerPlan311.no_children] at selected
  exact selected

theorem branch_certificate (m : Assignment) (valid : Models final m) :
    Certificate compiled final.core m branch.occurrence 3 [child.occurrence] plan :=
  GeneralNominalVersionedEvidence231.certificate_of_semantics branch_frame branch_order.symm
    (branch_holds m valid) (GeneralNominalVersionedMixedReady235.ready ⟨rfl,checked⟩ reached branch_frame) (branch_classes m)

theorem full_branch (m : Assignment) (valid : Models final m) :
    Evidence compiled final.core m branch.occurrence (.node 3 [.node 2 []]) :=
  GeneralNominalVersionedEvidence231.evidence_node ⟨_,branch_certificate m valid⟩
    (.cons (leaf_evidence m valid) .nil)

theorem classifies :
    B4TargetV8.Classify (boundary roles) registry final branch.occurrence (.selected (.node 3 [.node 2 []])) :=
  .selected branch_selected (.cons (.selected peer_selected .nil) .nil)

theorem actual_recursive :
    B4TargetV8.Classify (boundary roles) registry final branch.occurrence (.selected (.node 3 [.node 2 []])) ∧
    (∃ m, Models final m) ∧
    ∀ m, Models final m → Evidence compiled final.core m child.occurrence (.node 2 []) ∧
      Evidence compiled final.core m branch.occurrence (.node 3 [.node 2 []]) :=
  ⟨classifies,⟨_,inhabited⟩,fun m valid => ⟨leaf_evidence m valid,full_branch m valid⟩⟩

end Yulang.GeneralLatePeerRecursive311
