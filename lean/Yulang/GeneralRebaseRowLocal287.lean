import Yulang.GeneralRebaseRowAfterSafety287

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 14500000
namespace Yulang.GeneralRebaseRowLocal287
open GeneralRebaseRowChildSource287
open GeneralRebaseRowParentPacket287 (child plan sole_child)
open GeneralRebaseRowParentFrame287 (after after_model at_role effect)
open GeneralRebaseRowGeneratedChild287 (known current current_args)
open GeneralRebaseRowAfterSafety287 (diag safe_of_prepared pending_root_no merged_clear blocked_local)
open GeneralRebaseRowParentEvidence287 (replay_frame requests_ready)
open GeneralNominalVersionedCandidates231 (Survivor Unique)
open GeneralNominalVersionedMixedBoundary234 (Local boundary)
open GeneralNominalVersionedInstallation231 (replayPlan replay_children)
open GeneralDeclarations (Declaration)

private abbrev witness := GeneralRebaseRowChildSource287.model Common.rowEmpty

theorem child_at_role (choice : Bool) (d : Declaration) (visible : d ∈ (registry choice).declarations)
    (hasRole : d.role = (child choice).demand.role) : d = childDecl choice := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
  rcases visible with rfl|rfl
  · cases hasRole
  · rfl

theorem parent_survivor (choice : Bool) : Survivor (registry choice) (current choice) root 0 [child choice] := by
  have p := replay_frame choice witness (after_model choice Common.rowEmpty)
  refine ⟨pending_root_no choice,parentDecl,List.mem_cons_self,parent_checked,rfl,rfl,
    [((1 : Fin 3),(1 : Fin 3))],p.located,p.prepared,?_⟩
  exact ((replay_children (plan choice)).trans (sole_child choice)).symm

theorem child_survivor : Survivor (registry true) (current true) (child true) 1 [] :=
  ⟨known true,opaqueChild,List.mem_cons_of_mem _ List.mem_cons_self,opaque_checked,rfl,rfl,
    [((0 : Fin 3),(0 : Fin 3))],current_args true,GeneralRebaseRowWholeChild287.prepared,
    GeneralRebaseRowWholeChild287.no_children.symm⟩

theorem parent_unique (choice : Bool) : Unique (registry choice) (current choice) root 0 [child choice] := by
  refine ⟨parent_survivor choice,?_⟩
  intro k cs p
  have keep := p
  obtain ⟨_,d,visible,_,key,role,_,_,_,_⟩ := p
  have eq : k = 0 := key.symm.trans (congrArg Declaration.id (at_role choice d visible role))
  have strict : Survivor (registry choice) (current choice) root 0 cs := eq ▸ keep
  exact ⟨eq,GeneralNominalVersionedCandidates231.survivor_children_functional
    (checked choice) strict (parent_survivor choice)⟩

theorem child_unique : Unique (registry true) (current true) (child true) 1 [] := by
  refine ⟨child_survivor,?_⟩
  intro k cs p
  have keep := p
  obtain ⟨_,d,visible,_,key,role,_,_,_,_⟩ := p
  have eq : k = 1 := key.symm.trans (congrArg Declaration.id (child_at_role true d visible role))
  have strict : Survivor (registry true) (current true) (child true) 1 cs := eq ▸ keep
  exact ⟨eq,GeneralNominalVersionedCandidates231.survivor_children_functional
    (checked true) strict child_survivor⟩

theorem parent_safe (choice : Bool) : B4TargetV8.SafeKnown diag (registry choice) (after choice) root := by
  apply safe_of_prepared choice (.inl rfl) (pending_root_no choice)
  intro d member role
  cases at_role choice d member role
  exact (replay_frame choice witness (after_model choice Common.rowEmpty)).prepared

theorem child_safe : B4TargetV8.SafeKnown diag (registry true) (after true) (child true) := by
  apply safe_of_prepared true (.inr rfl) (known true)
  intro d member role
  cases child_at_role true d member role
  exact GeneralRebaseRowWholeChild287.prepared

theorem selected_parent (choice : Bool) :
    Local (registry choice) (after choice) root (.selected 0 [child choice]) := by
  apply GeneralNominalVersionedMixedBoundary234.local_iff.mpr
  have m := after_model choice Common.rowEmpty
  exact GeneralNominalVersionedDiagnosticLaws232.selected_of_model
    (parent_safe choice) (parent_unique choice) m
    (replay_frame choice witness m) (requests_ready choice)
    (GeneralNominalVersionedInstalledEvidence233.replay_holds (effect := effect choice) m)
    (GeneralNominalVersionedInstalledEvidence233.class_effects (effect := effect choice) m)
    (merged_clear choice root)

theorem selected_child :
    Local (registry true) (after true) (child true) (.selected 1 []) := by
  apply GeneralNominalVersionedMixedBoundary234.local_iff.mpr
  have m := after_model true Common.rowEmpty
  exact GeneralNominalVersionedDiagnosticLaws232.selected_of_model child_safe child_unique m
    GeneralRebaseRowWholeChild287.child_frame GeneralRebaseRowWholeChild287.ready
    (GeneralRebaseRowWholeChild287.holds witness m)
    (GeneralRebaseRowWholeChild287.class_effects witness)
    (merged_clear true _)

theorem positive_tree : CommonRoleOutermostResolver.Resolves
    (Local (registry true) (after true)) root (.selected 0 [.selected 1 []]) :=
  .selected (selected_parent true) (.cons (.selected selected_child .nil) .nil)

theorem blocked_tree : CommonRoleOutermostResolver.Resolves
    (Local (registry false) (after false)) root (.selected 0 [.pending]) :=
  .selected (selected_parent false) (.cons (.pending blocked_local) .nil)

theorem positive_classification : B4TargetV8.Classify (boundary roles) (registry true) (after true)
    root (.selected (.node 0 [.node 1 []])) :=
  .selected (selected_parent true) (.cons (.selected selected_child .nil) .nil)

end Yulang.GeneralRebaseRowLocal287
