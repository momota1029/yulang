import Yulang.GeneralRebaseRowLeafWindow288
import Yulang.GeneralNominalVersionedMixedFrameSelection235

/-! V8 diagnostics as well as dictionary semantics are retained by every
certified refresh of this particular positive guarded fixture. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29500
set_option maxHeartbeats 19000000
namespace Yulang.GeneralRebaseRowRefreshDiagnostics288
open GeneralRebaseRowChildSource287
open GeneralRebaseRowParentPacket287 (child)
open GeneralRebaseRowParentFrame287 (after at_role)
open GeneralRebaseRowLedger288 (supplemented models_eq)
open GeneralRebaseRowRefreshPackets288
open GeneralRebaseRowRefreshEvidence288
open GeneralRebaseNonleafCommitted276 (result)
open GeneralNominalVersionedMixedObservations233 (Refresh refresh_models)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedDiagnostic232 (boundary Local AdministrativeReady)
open GeneralNominalVersionedCandidates231 (Prepared Unique Survivor)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedMixedKernel234 (Committed)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalCenters (Plan)
open GeneralDeclarations (Declaration)

variable {context : GeneralNominalCandidates.Context}

theorem model_predicate (cert : Refresh supplemented context) :
    Models (refresh supplemented context) = Models (after true) :=
  funext (fun m => propext ((refresh_models cert).trans (models_eq m)))

theorem no_semantic_recurrence (cert : Refresh supplemented context) (origin) :
    ¬ GeneralNominalVersionedCycles232.Cyclic (refresh supplemented context) origin := by
  intro recurs
  exact GeneralRebaseRowParentStep287.no_cycle_after true origin
    ((GeneralNominalVersionedCycles232.full_models_only (model_predicate cert)).mp recurs)

theorem no_raw_recurrence (cert : Refresh supplemented context) (slot : Fin context.state.base.slots) :
    ¬ GeneralNominalCycleK2.RecursAt context.state slot := by
  intro raw
  exact no_semantic_recurrence cert _
    (GeneralRebaseRawIntoFull271.recurs _ ⟨_,nonempty_models cert⟩ slot raw)

theorem administrative (_cert : Refresh supplemented context) {focus : Occurrence roles}
    (visible : focus = root ∨ focus = child true) : AdministrativeReady (refresh supplemented context) focus := by
  unfold AdministrativeReady
  refine ⟨(GeneralRebaseRowAfterSafety287.administrative true visible).1,?_⟩
  intro first a occurrence last b same
  change first ∈ (after true).core.sites at a
  change last ∈ (after true).core.sites at b
  rw [GeneralRebaseRowParentEvidence287.centers true] at a b
  simp only [List.mem_cons,List.not_mem_nil,or_false] at a b
  rcases a with rfl|rfl <;> rcases b with rfl|rfl
  · exact .refl _
  · exact (GeneralRebaseRowParentEvidence287.roles_distinct true same.1).elim
  · exact (GeneralRebaseRowParentEvidence287.roles_distinct true same.1.symm).elim
  · exact .refl _

theorem safe (cert : Refresh supplemented context) {focus : Occurrence roles}
    (visible : focus = root ∨ focus = child true) :
    B4TargetV8.SafeKnown (boundary roles) (registry true) (refresh supplemented context) focus := by
  refine ⟨?_,?_,?_,?_⟩
  · rintro ⟨i,unknown⟩
    rcases visible with rfl | rfl
    · exact unknown (cert.refines.known 1 (GeneralRebaseRowAdministrative287.already_known true 1 (by decide)))
    · exact unknown (cert.refines.known 0 (GeneralRebaseRowAdministrative287.already_known true 0 (by decide)))
  · rintro (raw | ⟨i,cycle⟩ | ⟨slot,found,atFocus,i,cycle⟩)
    · obtain ⟨_,_,i,s,source,cycle⟩ := raw
      exact no_raw_recurrence cert s cycle
    · exact no_semantic_recurrence cert _ cycle
    · exact no_semantic_recurrence cert _ cycle
  · rintro (raw | ⟨p,frame,t,seen,cycle⟩)
    · obtain ⟨_,d,member,checked,role,prepared,bounds,located,visited,inspected,cycle⟩ := raw
      exact no_raw_recurrence cert visited.1 cycle
    · exact no_semantic_recurrence cert _ cycle
  · rintro (⟨_,decl,member,role,_,notPrepared⟩ | failed)
    · rcases visible with rfl | rfl
      · rw [at_role true _ member role] at notPrepared
        exact notPrepared (root_transported cert).prepared
      · rw [GeneralRebaseRowLocal287.child_at_role true _ member role] at notPrepared
        exact notPrepared (child_transported cert).prepared
    · exact failed (administrative cert visible)

theorem unique_from_role (cert : Refresh supplemented context) {focus : Occurrence roles}
    {k : Nat} {p : Plan roles}
    (visible : focus = root ∨ focus = child true)
    (frame : Frame (registry true) (refresh supplemented context).core focus k p)
    (declUnique : ∀ d ∈ (registry true).declarations, d.role = focus.demand.role → d = p.packet.declaration) :
    Unique (registry true) context focus k (GeneralNominalVersionedFrame231.children p.packet) := by
  have candidate := GeneralNominalVersionedMixedFrameSelection235.frame_survivor frame (safe cert visible).1
  refine ⟨candidate,?_⟩
  intro other ks rival
  have retained := rival
  obtain ⟨_,d,member,_,key,role,_,_,_,_⟩ := rival
  have same : other = k := key.symm.trans ((congrArg Declaration.id (declUnique d member role)).trans frame.key_eq)
  have cast : Survivor (registry true) context focus k ks := same ▸ retained
  exact ⟨same,GeneralNominalVersionedCandidates231.survivor_children_functional (checked true) cast candidate⟩

theorem merged_clear (_cert : Refresh supplemented context) (focus : Occurrence roles) :
    ¬ GeneralNominalVersionedMergedConflict232.MergedOutputConflict (refresh supplemented context) focus := by
  rintro ⟨⟨a,b,member,_,_⟩,_⟩
  change (a,b) ∈ ([] : List (Nat × Nat)) at member
  cases member

theorem selected_parent (cert : Refresh supplemented context) :
    Local (registry true) (refresh supplemented context) root (.selected 0 [child true]) := by
  have unique := unique_from_role cert (Or.inl rfl) (root_transported cert) (at_role true)
  rw [parent_children cert] at unique
  have m := nonempty_models cert
  have held := (GeneralRebaseNonleafCommitted276.committed root_frame cert parent_observed root_committed).1 _ m
  exact GeneralNominalVersionedDiagnosticLaws232.selected_of_model (safe cert (Or.inl rfl)) unique m
    (root_transported cert) (parent_ready cert) held.1 held.2 (merged_clear cert _)

theorem selected_child (cert : Refresh supplemented context) :
    Local (registry true) (refresh supplemented context) (child true) (.selected 1 []) := by
  have unique := unique_from_role cert (Or.inr rfl) (child_transported cert) (GeneralRebaseRowLocal287.child_at_role true)
  rw [child_children cert] at unique
  have m := nonempty_models cert
  have held := (GeneralRebaseNonleafCommitted276.committed child_frame cert child_observed child_committed).1 _ m
  exact GeneralNominalVersionedDiagnosticLaws232.selected_of_model (safe cert (Or.inr rfl)) unique m
    (child_transported cert) (child_ready cert) held.1 held.2 (merged_clear cert _)

theorem fully_selected (cert : Refresh supplemented context) :
    CommonRoleOutermostResolver.Resolves (Local (registry true) (refresh supplemented context)) root
      (.selected 0 [.selected 1 []]) :=
  .selected (selected_parent cert) (.cons (.selected (selected_child cert) .nil) .nil)

theorem only_child_tree (cert : Refresh supplemented context) (t : CommonRoleOutermostResolver.Tree)
    (given : CommonRoleOutermostResolver.Resolves (Local (registry true) (refresh supplemented context))
      (child true) t) : t = .selected 1 [] := by
  cases given with
  | pending h => cases B4TargetV8.local_functional h (selected_child cert)
  | ambiguous h => cases B4TargetV8.local_functional h (selected_child cert)
  | rejected h => cases B4TargetV8.local_functional h (selected_child cert)
  | selected h children =>
    cases B4TargetV8.local_functional h (selected_child cert)
    cases children
    rfl

theorem only_root_tree (cert : Refresh supplemented context) (t : CommonRoleOutermostResolver.Tree)
    (given : CommonRoleOutermostResolver.Resolves (Local (registry true) (refresh supplemented context)) root t) :
    t = .selected 0 [.selected 1 []] := by
  cases given with
  | pending h => cases B4TargetV8.local_functional h (selected_parent cert)
  | ambiguous h => cases B4TargetV8.local_functional h (selected_parent cert)
  | rejected h => cases B4TargetV8.local_functional h (selected_parent cert)
  | selected h children =>
    cases B4TargetV8.local_functional h (selected_parent cert)
    cases children with
    | cons first tail =>
      cases tail
      rw [only_child_tree cert _ first]

theorem exact_tree (cert : Refresh supplemented context) (t : CommonRoleOutermostResolver.Tree) :
    CommonRoleOutermostResolver.Resolves (Local (registry true) (refresh supplemented context)) root t ↔
     t = .selected 0 [.selected 1 []] :=
  ⟨only_root_tree cert t,fun shape => shape.symm ▸ fully_selected cert⟩

end Yulang.GeneralRebaseRowRefreshDiagnostics288
