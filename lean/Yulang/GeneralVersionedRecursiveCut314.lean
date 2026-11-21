import Yulang.GeneralVersionedEndpointReduction314
import Yulang.GeneralVersionedRecursiveBridge310

set_option backward.isDefEq.respectTransparency false
/-! I-55 dictionary soundness from two explicit residual families. The
actual recursive B4 EvidenceNode is rebuilt, not assumed, and no upper
bound or termination fact is supplied. -/
namespace Yulang.GeneralVersionedRecursiveCut314
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedMixedSourceBoundary234 (boundary Local)
open GeneralVersionedRecursiveBridge310 (PendingCase CurrentCandidate ChoiceBridge JointBridge)
open GeneralVersionedRemainingWrites314 (ForeignChoice)
open GeneralVersionedEndpointReduction314 (Readback)

def ForeignKeys (roles : Roles.RoleDecls) : Prop :=
  ∀ registry state (root focus : Occurrence roles) key kids effect,
    PendingCase registry state root focus key kids →
    CurrentCandidate registry state focus key kids effect →
    ForeignChoice state effect.plan.packet

def EndpointReads (roles : Roles.RoleDecls) : Prop :=
  ∀ registry state (root focus : Occurrence roles) key kids effect,
    PendingCase registry state root focus key kids →
    CurrentCandidate registry state focus key kids effect →
    Readback state effect

theorem choice {roles : Roles.RoleDecls} (sources : ForeignKeys roles) : ChoiceBridge roles := by
  intro registry state root focus key kids effect pending candidate
  have foreign := sources registry state root focus key kids effect pending candidate
  obtain ⟨checked,path,_,_,selected,⟨m,valid⟩,_⟩ := pending
  have picked : Local registry state effect.plan.packet.site.occurrence (.selected effect.plan.packet.declaration.id kids) := by
    rw [candidate.2.2.1,candidate.2.2.2.1]
    exact selected
  exact (GeneralVersionedRemainingWrites314.choice checked path picked valid).mpr foreign

theorem joint {roles : Roles.RoleDecls} (sources : EndpointReads roles) : JointBridge roles := by
  intro registry state root focus key kids effect pending candidate _
  have read := sources registry state root focus key kids effect pending candidate
  obtain ⟨checked,path,_,_,selected,inhabited,_⟩ := pending
  have picked : Local registry state effect.plan.packet.site.occurrence (.selected effect.plan.packet.declaration.id kids) := by
    rw [candidate.2.2.1,candidate.2.2.2.1]
    exact selected
  exact GeneralVersionedRemainingWrites314.joint checked path picked candidate.1 candidate.2.1 inhabited
    (GeneralVersionedEndpointReduction314.reused checked path picked (candidate.1 ▸ candidate.2.1 ▸ effect.frame) read)

theorem evidenceNode {roles : Roles.RoleDecls} (aliases : ForeignKeys roles) (whereEndpoints : EndpointReads roles) :
    B4SkeletonV8.EvidenceNode (boundary roles) :=
  GeneralVersionedRecursiveBridge310.evidenceNode (choice aliases) (joint whereEndpoints)

end Yulang.GeneralVersionedRecursiveCut314
