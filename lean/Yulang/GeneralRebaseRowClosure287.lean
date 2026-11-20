import Yulang.GeneralRebaseRowAdministrative287

/-! Fixture-specific raw closure. In the row-pattern branch, absence of a
kernel Step coexists with a pending child; only the whole-type branch has a
completed dictionary. This is not a general stopping theorem. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29200
set_option maxHeartbeats 15200000
namespace Yulang.GeneralRebaseRowClosure287
open GeneralRebaseRowChildSource287
open GeneralRebaseRowParentPacket287 (child center plan sole_child)
open GeneralRebaseRowParentFrame287 (after after_model effect)
open GeneralRebaseRowParentEvidence287 (raw_sites centers roles_distinct only_root_plan)
open GeneralRebaseRowGeneratedChild287 (not_prepared)
open GeneralRebaseRowAdministrative287 (equality_is_reflexive point_closed no_refresh)
open GeneralRebaseRowLocal287 (child_at_role)
open GeneralNominalVersionedMixedKernel234 (Step Stable)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalCenters (Plan)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalSaturationState (Generated)

theorem edges (choice : Bool) : (after choice).core.erased.current.edges = [(root,child choice)] := by
  change [] ++ GeneralNominalVersionedChildren232.edges (plan choice) = _
  unfold GeneralNominalVersionedChildren232.edges
  rw [sole_child]
  rfl

theorem scope (choice : Bool) {focus : Occurrence roles}
    (reached : Generated (after choice).core.erased.current root focus) : focus = root ∨ focus = child choice := by
  induction reached with
  | root => exact Or.inl rfl
  | child _ member _ =>
    rw [edges] at member
    exact Or.inr (congrArg Prod.snd (List.mem_singleton.mp member))
  | alias _ _ present _ _ =>
    rw [raw_sites] at present
    rcases List.mem_cons.mp present with e|e
    · cases e
      exact Or.inl rfl
    · cases List.mem_singleton.mp e
      exact Or.inr rfl

theorem only_child_plan {p : Plan roles} {key} (one : Frame (registry true) (after true).core (child true) key p) :
    p = GeneralRebaseRowWholeChild287.plan := by
  have sameD := child_at_role true _ one.visible one.role_eq
  have rawSame : p.packet.site = (center true).observed := by
    have seen := one.raw_recorded
    rw [raw_sites] at seen
    rcases List.mem_cons.mp seen with e|e
    · have impossible : root = child true :=
        (congrArg GeneralNominalDemandMerging.Site.occurrence e).symm.trans one.occurrence_eq
      exact (roles_distinct true (congrArg (fun o : Occurrence roles => o.demand.role) impossible)).elim
    · exact List.mem_singleton.mp e
  have centerSame : p.input = center true := by
    have seen := one.center_recorded
    rw [centers] at seen
    rcases List.mem_cons.mp seen with e|e
    · have atChild := p.input_exact.trans one.occurrence_eq
      have impossible : root = child true :=
        (congrArg GeneralNominalCenters.Site.occurrence e).symm.trans atChild
      exact (roles_distinct true (congrArg (fun o : Occurrence roles => o.demand.role) impossible)).elim
    · exact List.mem_singleton.mp e
  exact GeneralRebaseScopedFrame276.same_frame one GeneralRebaseRowWholeChild287.child_frame sameD rawSame centerSame

theorem no_step (choice : Bool) (next : State roles) : ¬ Step (registry choice) root (after choice) next := by
  intro step
  obtain ⟨focus,generated,chosen⟩ := step
  have visible := scope choice generated
  cases chosen with
  | administrative rule =>
    cases rule with
    | enqueue _ absent =>
      rcases visible with rfl|rfl
      · exact absent _ ((raw_sites choice).symm ▸ List.mem_cons_self) rfl
      · exact absent _ (GeneralRebaseRowGeneratedChild287.raw_child choice) rfl
    | refresh ctx cert n _ old new => exact no_refresh choice cert n old new
    | equate n k _ _ same novel =>
      have same := equality_is_reflexive choice n k same
      subst k
      exact novel (fun m _ => ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩)
    | reobserve revision _ better =>
      exact GeneralNominalReobservationSteps.pointClosed_no_revision (point_closed choice) revision better
  | refresh _ ctx cert n _ old new => exact no_refresh choice cert n old new
  | install candidate cert novel =>
    have frame := candidate.frame
    rw [cert.registry_eq,cert.snapshot_eq] at frame
    rcases visible with atRoot|atChild
    · rw [atRoot] at frame
      have exactPlan := only_root_plan choice _ (after_model choice Common.rowEmpty) frame
      rw [exactPlan] at novel
      exact novel (GeneralNominalVersionedCommitted232.replay_committed before (effect choice))
    · rw [atChild] at frame
      cases choice with
      | true =>
        rw [only_child_plan frame] at novel
        exact novel GeneralRebaseRowWholeChild287.already_committed
      | false =>
        have wrong := frame.prepared
        rw [child_at_role false _ frame.visible frame.role_eq] at wrong
        exact not_prepared wrong
  | merge a b one two same novel =>
    rw [centers] at one two
    simp only [List.mem_cons,List.not_mem_nil,or_false] at one two
    rcases one with rfl|rfl <;> rcases two with rfl|rfl
    · exact novel (.refl _)
    · exact roles_distinct choice same.1
    · exact roles_distinct choice same.1.symm
    · exact novel (.refl _)

theorem stable (choice : Bool) :
    Stable (registry choice) (after choice) root ∧ Stable (registry choice) (after choice) (child choice) := by
  have closure := GeneralNominalVersionedMixedKernel234.closure (no_step choice)
  exact ⟨closure.1,closure.2 _ (GeneralRebaseRowParentStep287.generated choice)⟩

end Yulang.GeneralRebaseRowClosure287
