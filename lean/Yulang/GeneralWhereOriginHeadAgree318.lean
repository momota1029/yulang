import Yulang.GeneralWhereOriginSingleCommon318

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 24500
set_option maxHeartbeats 16000000
namespace Yulang.GeneralWhereOriginHeadAgree318
open GeneralNominalCenters (Plan)
open GeneralNominalIdentities (Origin source)
open GeneralNominalState (sources)
open GeneralNominalVersionedPlans231 (HeadModels)
open GeneralNominalVersionedPacketFrame236 (headSources head_models_iff)
open GeneralNominalCenteredFrame179 (Agree)
open GeneralNominalCommonBridge (Assignment)
open GeneralWhereOriginDelta318 (High)

theorem head_not_written {p : Plan rs} {target : Nat}
    (visible : p.packet.declaration ∈ p.packet.registry.declarations)
    (high : High p.packet.context.state target) (fresh : target ∉ sources p.packet.context.state) :
    target ∉ headSources p.packet := by
  intro found
  rcases List.mem_append.mp found with privatePart|report
  · have rawPrivate := GeneralNominalSemanticRawFrame236.contained _ privatePart
    let pack := p.packet
    have domain (n : Nat) (item : n ∈ sources (GeneralNominalVersionedPlans231.privateState pack)) :
        n ∈ GeneralVersionedInstallDomain313.pool pack := by
      apply GeneralNominalAllocationSupport.extend_sources _ [] _ ?_ (by intro _ no; cases no) ?_ item
      · refine GeneralNominalAllocationSupport.extend_sources pack.context.state
          (GeneralVersionedInstallDomain313.reserve pack) _ (fun _ h => List.mem_append_left _ h)
          (fun _ h => List.mem_append_right _ h) ?_
        intro atom present
        rcases List.mem_append.mp present with cross|merges
        · exact GeneralNominalAllocationSupport.cross_sources
            (GeneralVersionedInstallDomain313.extension_endpoints pack) atom cross
        · exact GeneralVersionedInstallDomain313.merge_atom pack visible atom merges
      · exact fun atom member => GeneralNominalAllocationSupport.checks_sources _ _
          (fun _ h => List.mem_append_left _ h) atom member
    rcases List.mem_append.mp (domain target rawPrivate) with legacy|reserve
    · exact fresh legacy
    · obtain ⟨k,mode,eq⟩ := high
      rw [eq] at reserve
      have low := GeneralVersionedInstallDomain313.reserve_purpose p.packet reserve
      omega
  · exact fresh (GeneralNominalSemanticRawFrame236.contained _
      (GeneralNominalSemanticRawFrame236.report_sources_subset _ _ _ report))

open GeneralWhereOriginSingleSource318
open GeneralWhereOriginSingleModel318
open GeneralWhereOriginSingleCommon318 (result retains_rows current_rows)
open GeneralWhereOriginSingleCells318 (loOld loNow hi)
open GeneralNominalVersionedPlans231 (variables)

theorem scopes (m : Assignment) {p : Plan GeneralDictionaryJournalRefinement228Source.roles}
    (seen : p.packet.declaration ∈ p.packet.registry.declarations)
    (pastHigh : High p.packet.context.state loOld) (upperHigh : High p.packet.context.state hi)
    (nextHigh : High p.packet.context.state loNow)
    (past : loOld ∉ sources p.packet.context.state) (upper : hi ∉ sources p.packet.context.state)
    (next : loNow ∉ sources p.packet.context.state) :
    Agree (headSources p.packet) m (result m) := by
  intro n support
  have exclude target (h : High p.packet.context.state target)
      (raw : target ∉ sources p.packet.context.state) : target ≠ n := by
    intro equal
    exact head_not_written seen h raw (equal.symm ▸ support)
  exact (previous_outside m n (exclude _ pastHigh past) (exclude _ upperHigh upper)).trans
    (patched_outside (previous m) n (exclude _ nextHigh next))

theorem preserve_heads (m : Assignment) (old : HeadModels older m) (now : HeadModels newer m) :
    HeadModels older (result m) ∧ HeadModels newer (result m) := by
  have scanOld : Agree (headSources older) m (result m) :=
    scopes m (p := oldPlan) List.mem_cons_self (previousLo.high rfl) (previousHi.high rfl) (presentLo.high rfl)
      (older_absent _ (previousLo.high rfl)) (older_absent _ (previousHi.high rfl)) (older_absent _ (presentLo.high rfl))
  have scanNew : Agree (headSources newer) m (result m) :=
    scopes m (p := newPlan) List.mem_cons_self (previousLo.high rfl) (previousHi.high rfl) (presentLo.high rfl)
      (newer_absent _ (previousLo.high rfl)) (newer_absent _ (previousHi.high rfl)) (newer_absent _ (presentLo.high rfl))
  exact ⟨(head_models_iff older scanOld).mp old,(head_models_iff newer scanNew).mp now⟩

/-- Both actual split-capture observer heads and all compiler input rows
are realized together. This is stronger than raw satisfiability alone,
but does not assert a physical mixed insertion trace. -/
theorem exact_observations :
    ∃ m, HeadModels older m ∧ HeadModels newer m ∧
      previousLo.row.Holds (variables oldPlan m) m ∧ previousHi.row.Holds (variables oldPlan m) m ∧
      presentLo.row.Holds (variables newPlan m) m ∧ presentHi.row.Holds (variables newPlan m) m := by
  let w := GeneralLiveCompoundLeafProof316.w
  have old := GeneralLiveCompoundLeafProof316.valid.2.1 GeneralLiveCompoundRoot316.plan List.mem_cons_self
  have readyOld := GeneralWhereOriginSingleHead318.old_head w (GeneralNominalVersionedPlans231.head_models old)
  have readyNow : HeadModels GeneralLiveCompoundCurrentRoot316.packet w :=
    ⟨(GeneralNominalVersionedPlans231.private_models_iff ..).mpr
      ⟨GeneralLiveCompoundLeafProof316.valid.1.1,GeneralLiveCompoundPostRootHead316.ordinary_pre⟩,
      GeneralLiveCompoundPostRootHead316.projection_pre⟩
  have both := preserve_heads w readyOld (GeneralWhereOriginSingleHead318.new_head w readyNow)
  have held := retains_rows w
  have here := current_rows w
  exact ⟨result w,both.1,both.2,held.1,held.2,here.1,here.2⟩

end Yulang.GeneralWhereOriginHeadAgree318
