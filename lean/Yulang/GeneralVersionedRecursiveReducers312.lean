import Yulang.GeneralVersionedHistoricalJoint312

set_option backward.isDefEq.respectTransparency false
/-! The whole I55 recursive evidence skeleton compiled from the narrower
residual interfaces. None of the open hypotheses assumes selected evidence
or a completed packet. Proof recursion is on the supplied dictionary only. -/
namespace Yulang.GeneralVersionedRecursiveReducers312
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Models Effect)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary Local)
open GeneralVersionedRecursiveBridge310 (PendingCase CurrentCandidate ChoiceBridge JointBridge)
open GeneralNominalVersionedDiagnostic232 (HeadEquations)
open GeneralNominalVersionedModelSupport237 (Support)
open GeneralNominalVersionedTraceSiteSupport237 (Covered)
open GeneralNominalVersionedMixedSeedLedger237 (IdCovered)
open GeneralNominalSaturationState (Packet Alias)
open GeneralVersionedHistoricalJoint312 (HeadTableReady)
open GeneralVersionedSelectedJointWrites312 (InternalReady)

def ChoiceCoverage (roles : Roles.RoleDecls) : Prop :=
  ∀ registry state (root focus : Occurrence roles) key kids effect,
    PendingCase registry state root focus key kids →
    CurrentCandidate registry state focus key kids effect →
    ∀ prior ∈ state.core.erased.current.packets,
      Alias state.core.erased.current focus.identity prior.site.occurrence.identity →
      GeneralVersionedSemanticPeer312.Coverage registry state focus prior.declaration

def InitialHead (s : State roles) (effect : Effect roles) (names : List Nat) : Prop :=
  (∃ m, Models s m ∧ HeadEquations effect.plan m) ∨
  ∃ old ∈ s.plans, Alias s.core.erased.current effect.plan.packet.site.occurrence.identity old.packet.site.occurrence.identity ∧
    HeadTableReady s effect.plan old names

def TargetChecks (roles : Roles.RoleDecls) : Prop :=
  ∀ registry state (root focus : Occurrence roles) key kids effect,
    PendingCase registry state root focus key kids →
    CurrentCandidate registry state focus key kids effect →
    ∃ names, Support state names ∧ Covered state names ∧
      IdCovered (GeneralNominalVersionedSupportedCompletion237.pool names state effect.plan) state effect.plan.packet ∧
      InitialHead state effect names ∧ InternalReady state effect names

theorem choice_of_coverage {roles : Roles.RoleDecls} (coverage : ChoiceCoverage roles) : ChoiceBridge roles := by
  intro registry state root focus key kids effect pending candidate
  have obligations := pending
  obtain ⟨checked,path,_,_,chosen,inhabited,_⟩ := pending
  have picked : Local registry state effect.plan.packet.site.occurrence (.selected effect.plan.packet.declaration.id kids) := by
    rw [candidate.2.2.1,candidate.2.2.2.1]
    exact chosen
  apply GeneralVersionedSemanticPeer312.choice checked path picked inhabited
  intro prior stored alias
  rw [candidate.2.2.1] at alias ⊢
  exact coverage registry state root focus key kids effect obligations candidate prior stored alias

theorem joint_of_checks {roles : Roles.RoleDecls} (checks : TargetChecks roles) : JointBridge roles := by
  intro registry state root focus key kids effect pending candidate choice
  obtain ⟨names,support,sites,ledger,first,internal⟩ := checks registry state root focus key kids effect pending candidate
  obtain ⟨checked,path,_,_,chosen,inhabited,_⟩ := pending
  have picked : Local registry state effect.plan.packet.site.occurrence (.selected effect.plan.packet.declaration.id kids) := by
    rw [candidate.2.2.1,candidate.2.2.2.1]
    exact chosen
  rcases first with head|⟨old,stored,alias,binders⟩
  · exact GeneralVersionedSelectedJointWrites312.joint_from_internal checked path picked candidate.1 candidate.2.1
      support sites ledger head internal
  have seen : old.packet ∈ state.core.erased.current.packets := by
    rw [(GeneralNominalVersionedMixedChoiceHistory236.reachable path).2]
    exact List.mem_map.mpr ⟨old,stored,rfl⟩
  have visible := GeneralNominalVersionedMixedChoiceHistory236.visible path seen
  have effectVisible := candidate.1 ▸ effect.frame.visible
  have same := GeneralDictionaryEmissionPlans.declaration_key_unique _
    (GeneralNominalVersionedMixedSourceBoundary234.checked_compiled checked).2 _ _
    effectVisible visible (choice old.packet seen alias)
  exact GeneralVersionedHistoricalJoint312.joint checked path picked candidate.1 candidate.2.1 stored alias
    same inhabited support sites ledger binders internal

/-- Conditional general dictionary soundness bridge. Availability of the two
residual certificate families is a distinct source/compiler obligation. -/
theorem evidenceNode {roles : Roles.RoleDecls} (coverage : ChoiceCoverage roles) (checks : TargetChecks roles) :
    B4SkeletonV8.EvidenceNode (boundary roles) :=
  GeneralVersionedRecursiveBridge310.evidenceNode (choice_of_coverage coverage) (joint_of_checks checks)

end Yulang.GeneralVersionedRecursiveReducers312
