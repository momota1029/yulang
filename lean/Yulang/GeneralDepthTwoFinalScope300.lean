import Yulang.GeneralDepthTwoFinalSelection300

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 34000
set_option maxHeartbeats 14000000
namespace Yulang.GeneralDepthTwoFinalScope300
open GeneralGeneratedNestedSource299 (root snapshot model)
open GeneralGeneratedNestedPredictions299 (compiled middle terminal)
open GeneralDepthTwoSecondInstall300 (final final_requests leafSite)
open GeneralDepthTwoFinalNodes300
open GeneralDepthTwoTerminalFrame300 (final_model)
open GeneralNominalVersionedJournal232 (Models Effect)
open GeneralNominalVersionedMixedKernel234 (Installable Committed)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalSaturationState (Alias Generated)
open GeneralDeclarationExamples (roles)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalCenters (Plan)

theorem id_injective (a b : Node) (eq : (demand a).identity = (demand b).identity) : a = b := by
  cases a <;> cases b <;> first
    | rfl
    | exact False.elim ((by decide +kernel : ¬ (_ = _)) eq)

theorem demand_injective (a b : Node) (eq : demand a = demand b) : a = b :=
  id_injective a b (congrArg Occurrence.identity eq)

theorem alias_identity {a b : Nat} (same : Alias final.core.erased.current a b) : a = b := by
  induction same with
  | refl => rfl
  | edge member => cases member
  | symm _ ih => exact ih.symm
  | trans _ _ left right => exact left.trans right

theorem raw_enum : final.core.erased.current.sites =
    [(plan .outer).packet.site,(plan .inner).packet.site,(plan .leaf).packet.site] := by
  rw [GeneralDepthTwoTerminalFrame300.raw_sites]
  change [GeneralNominalDemandMerging.pointSite root,GeneralDepthTwoRootPlan300.child.observed,leafSite.observed] =
    [GeneralNominalDemandMerging.pointSite root,GeneralNominalDemandMerging.pointSite middle,leafSite.observed]
  rw [GeneralDepthTwoMiddleContext300.middle_raw_site]

theorem raw_hit (s : GeneralNominalDemandMerging.Site roles) (present : s ∈ final.core.erased.current.sites) :
    ∃ n : Node, s = (plan n).packet.site := by
  rw [raw_enum] at present
  simp only [List.mem_cons,List.not_mem_nil,or_false] at present
  rcases present with rfl|rfl|rfl
  · exact ⟨.outer,rfl⟩
  · exact ⟨.inner,rfl⟩
  · exact ⟨.leaf,rfl⟩

theorem site_focus (n : Node) : (plan n).packet.site.occurrence = demand n :=
  (frame n model final_model).occurrence_eq

theorem generated_only (d : Occurrence roles) (p : Generated final.core.erased.current root d) :
    ∃ n : Node, d = demand n := by
  induction p with
  | root => exact ⟨.outer,rfl⟩
  | child _ member _ =>
    rw [GeneralDepthTwoEvidence300.final_edges] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with eq|eq
    · exact ⟨.inner,(Prod.mk.inj eq).2⟩
    · exact ⟨.leaf,(Prod.mk.inj eq).2⟩
  | alias _ first last _ _ =>
    obtain ⟨n,eq⟩ := raw_hit _ last
    exact ⟨n,(congrArg (fun s => s.occurrence) eq).trans (site_focus n)⟩

theorem paired_frame (n : Node) (p : Plan roles) (key : Nat)
    (candidate : Frame compiled final.core (demand n) key p) : p = plan n := by
  apply GeneralRebaseScopedFrame276.same_frame candidate (frame n model final_model)
  · rcases GeneralDepthTwoFinalSelection300.options n candidate.visible candidate.role_eq with good|bad
    · exact good.trans (declaration n).symm
    · exact False.elim (GeneralDepthTwoFinalSelection300.wrong_unprepared n (bad ▸ candidate.prepared))
  · obtain ⟨a,matched⟩ := raw_hit _ candidate.raw_recorded
    have same : demand n = demand a :=
      candidate.occurrence_eq.symm.trans ((congrArg (fun s => s.occurrence) matched).trans (site_focus a))
    cases demand_injective n a same
    exact matched
  · obtain ⟨a,matched⟩ := center_hit _ candidate.center_recorded
    have eq1 := p.input_exact.trans candidate.occurrence_eq
    have eq2 := (plan a).input_exact.trans (site_focus a)
    have same : demand n = demand a :=
      eq1.symm.trans ((congrArg (fun s => s.occurrence) matched).trans eq2)
    cases demand_injective n a same
    exact matched

theorem no_raw_install (e : Effect roles) (enabled : Installable compiled final e)
    (there : Generated final.core.erased.current root e.plan.packet.site.occurrence) :
    Committed final e.plan := by
  obtain ⟨n,eq⟩ := generated_only _ there
  have localFrame := e.frame
  rw [enabled.registry_eq,enabled.snapshot_eq,eq] at localFrame
  have same := paired_frame n e.plan _ localFrame
  rw [same]
  constructor
  · intro m held
    exact ⟨plan_holds n m held,GeneralRebaseDisplayFrame276.classes_empty (final_requests _) (plan n) m⟩
  · intro child member
    rw [site_focus n,GeneralDepthTwoEvidence300.final_edges]
    cases n
    · change child ∈ GeneralNominalVersionedFrame231.children GeneralDepthTwoFinalParents300.rootNow.packet at member
      rw [GeneralDepthTwoFinalParents300.root_children] at member
      cases List.mem_singleton.mp member
      exact List.mem_cons_self ..
    · change child ∈ GeneralNominalVersionedFrame231.children GeneralDepthTwoFinalParents300.middleNow.packet at member
      rw [GeneralDepthTwoFinalParents300.middle_children] at member
      cases List.mem_singleton.mp member
      exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
    · change child ∈ GeneralNominalVersionedFrame231.children GeneralDepthTwoTerminalPlan300.packet at member
      rw [GeneralDepthTwoTerminalPlan300.children_empty] at member
      cases member

theorem point_closed : GeneralNominalReobservationSteps.PointClosed final.core.erased.current.context.state := by
  intro slot descriptor recorded
  change (if slot = (0 : Fin 3) then some (GeneralGeneratedNestedSource299.listDescriptor 1)
    else if slot = (1 : Fin 3) then some (GeneralGeneratedNestedSource299.listDescriptor 2)
    else none) = some descriptor at recorded
  split at recorded
  · cases Option.some.inj recorded
    intro parameter member
    change parameter ∈ [GeneralNominalState.Parameter.type ((1 : Fin 3),(1 : Fin 3))] at member
    cases List.mem_singleton.mp member
    rfl
  · split at recorded
    · cases Option.some.inj recorded
      intro parameter member
      change parameter ∈ [GeneralNominalState.Parameter.type ((2 : Fin 3),(2 : Fin 3))] at member
      cases List.mem_singleton.mp member
      rfl
    · cases recorded

end Yulang.GeneralDepthTwoFinalScope300
