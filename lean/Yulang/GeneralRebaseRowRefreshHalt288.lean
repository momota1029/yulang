import Yulang.GeneralRebaseRowRefreshPackets288

/-! For the guarded supplemental fixture, all maximal traces have exactly
one old refresh. The original raw source still never reaches this ledger. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29000
set_option maxHeartbeats 18000000
namespace Yulang.GeneralRebaseRowRefreshHalt288
open GeneralRebaseRowChildSource287
open GeneralRebaseRowParentPacket287 (child plan)
open GeneralRebaseRowParentFrame287 (after)
open GeneralRebaseRowParentEvidence287 (raw_sites centers roles_distinct)
open GeneralRebaseRowAdministrative287 (equality_is_reflexive)
open GeneralRebaseRowLedger288 (supplemented models_eq unknown_output)
open GeneralRebaseRowLedgerStep288 (refreshed real_refresh_at_hypothetical_state)
open GeneralRebaseRowLedgerFirst288 (IsOutputRefresh only_output_refresh)
open GeneralRebaseRowRefreshClosed288 (no_more_refresh point_closed)
open GeneralRebaseRowRefreshPackets288 (scope prepared_is_committed)
open GeneralNominalVersionedMixedObservations233 (Refresh refresh_models)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralNominalState (Known)

variable {context : GeneralNominalCandidates.Context}

theorem no_step (certificate : Refresh supplemented context) (known : Known context.state 2)
    (next : State roles) : ¬ Step (registry true) root (refresh supplemented context) next := by
  rintro ⟨focus,generated,action⟩
  have visible := scope generated
  cases action with
  | administrative transition =>
    cases transition with
    | enqueue _ absent =>
      rcases visible with rfl | rfl
      · exact absent _ ((raw_sites true).symm ▸ List.mem_cons_self) rfl
      · exact absent _ (GeneralRebaseRowGeneratedChild287.raw_child true) rfl
    | refresh target nextCert n _ old new =>
      exact no_more_refresh certificate known nextCert n old new
    | equate n k _ _ same novel =>
      have sameId := equality_is_reflexive true n k (fun m valid =>
        same m ((refresh_models certificate).mpr ((models_eq m).mpr valid)))
      subst k
      exact novel (fun m _ => ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩)
    | reobserve revision _ improvement =>
      exact GeneralNominalReobservationSteps.pointClosed_no_revision
        (point_closed certificate known) revision improvement
  | refresh _ target nextCert n _ old new =>
    exact no_more_refresh certificate known nextCert n old new
  | install candidate enabling novel =>
    have frame := candidate.frame
    rw [enabling.registry_eq,enabling.snapshot_eq] at frame
    exact novel (prepared_is_committed certificate visible frame)
  | merge first last one two same novel =>
    change first ∈ (after true).core.sites at one
    change last ∈ (after true).core.sites at two
    rw [centers true] at one two
    simp only [List.mem_cons,List.not_mem_nil,or_false] at one two
    rcases one with rfl|rfl <;> rcases two with rfl|rfl
    · exact novel (.refl _)
    · exact roles_distinct true same.1
    · exact roles_distinct true same.1.symm
    · exact novel (.refl _)

theorem next_halts {s : State roles} (edge : Step (registry true) root supplemented s) :
    ∀ t, ¬ Step (registry true) root s t := by
  obtain ⟨_,⟨cert⟩,known,rfl⟩ := (only_output_refresh s).mp edge
  exact no_step cert known

theorem every_path_one_or_zero (s : State roles)
    (path : B4Target.Steps (Step (registry true) root) supplemented s) :
    s = supplemented ∨ Step (registry true) root supplemented s := by
  induction path with
  | refl => exact .inl rfl
  | tail _ edge ih =>
    rcases ih with same | first
    · exact .inr (same ▸ edge)
    · exact (next_halts first _ edge).elim

theorem maximal_iff (s : State roles) :
    (B4Target.Steps (Step (registry true) root) supplemented s ∧
      (∀ t, ¬ Step (registry true) root s t)) ↔ IsOutputRefresh s := by
  constructor
  · rintro ⟨path,halt⟩
    rcases every_path_one_or_zero s path with rfl | edge
    · exact (halt refreshed real_refresh_at_hypothetical_state).elim
    · exact (only_output_refresh s).mp edge
  · intro terminal
    have edge := (only_output_refresh s).mpr terminal
    exact ⟨.tail .refl edge,next_halts edge⟩

theorem scoped_accessible : Acc (fun next current => Step (registry true) root current next) supplemented := by
  constructor
  intro s edge
  constructor
  intro t impossible
  exact (next_halts edge t impossible).elim

end Yulang.GeneralRebaseRowRefreshHalt288
