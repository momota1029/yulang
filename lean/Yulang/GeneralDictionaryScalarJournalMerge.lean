import Yulang.GeneralDictionaryScalarMerge

/-! Historical packet materialization can establish merge output equalities
without falsely treating that packet as a current-context BranchAt witness. -/
namespace Yulang.GeneralDictionaryScalarJournalMerge
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalDemandMerging (Site outputAtoms)
open GeneralNominalCommonBridge (Assignment)
variable {roles : Roles.RoleDecls}

/-- Scalar requests are read in the packet's ORIGINAL context and registry. -/
def Requests (packet : Packet roles) (site : Site roles) (scalars : Nat → Inference.Base) : Prop :=
  ∀ output ∈ site.occurrence.demand.outputs,
    (.source output.target,.scalar (scalars output.name)) ∈
      (GeneralNominalRecursiveCandidates.generated packet.registry packet.context packet.site.occurrence
        packet.declaration packet.checked packet.bounds).tests

/-- The two packets may coincide (e.g. one parent generated both output sites).
No historical-to-current candidate transport is assumed. -/
theorem outputs_from_packets (state : State roles) (first last : Site roles)
    (leftPacket rightPacket : Packet roles)
    (one : leftPacket ∈ state.packets) (two : rightPacket ∈ state.packets)
    (scalars : Nat → Inference.Base)
    (left : Requests leftPacket first scalars) (right : Requests rightPacket last scalars)
    (model : Assignment) (valid : Models state model) :
    PresenceNormalForm.All CommonNominalFullCarrier.model model (outputAtoms first last) := by
  apply (GeneralNominalDemandMerging.output_atoms_exact first last model).mpr
  intro a ha b hb same
  have leftBranch := valid.2.1 leftPacket one
  have rightBranch := valid.2.1 rightPacket two
  have x := GeneralDictionaryRecursiveEvidence.generated_scalar_equation leftPacket.registry leftPacket.context
    leftPacket.site.occurrence leftPacket.declaration leftPacket.checked leftPacket.bounds model leftBranch
    a.target (scalars a.name) (left a ha)
  have y := GeneralDictionaryRecursiveEvidence.generated_scalar_equation rightPacket.registry rightPacket.context
    rightPacket.site.occurrence rightPacket.declaration rightPacket.checked rightPacket.bounds model rightBranch
    b.target (scalars b.name) (right b hb)
  rw [← same] at y
  exact ⟨CommonNominalFullCarrier.subtype_trans x.1 y.2,
    CommonNominalFullCarrier.subtype_trans y.1 x.2⟩

/-- These scalar constraints add no semantic restriction to an existing
journal whose materialized packets already impose them. -/
theorem models_merge_iff (state : State roles) (first last : Site roles)
    (leftPacket rightPacket : Packet roles)
    (one : leftPacket ∈ state.packets) (two : rightPacket ∈ state.packets)
    (scalars : Nat → Inference.Base)
    (left : Requests leftPacket first scalars) (right : Requests rightPacket last scalars)
    (model : Assignment) : Models (merge state first last) model ↔ Models state model := by
  rw [merge_models]
  exact ⟨fun given => given.1,fun given => ⟨given,
    outputs_from_packets state first last leftPacket rightPacket one two scalars left right model given⟩⟩

/-- At every current journal model, full recursive dictionary meaning is
unchanged by this scalar-output merge, not only at one chosen witness. -/
theorem evidence_merge_iff (registry : Registry) (state : State roles) (first last : Site roles)
    (leftPacket rightPacket : Packet roles)
    (one : leftPacket ∈ state.packets) (two : rightPacket ∈ state.packets)
    (scalars : Nat → Inference.Base)
    (left : Requests leftPacket first scalars) (right : Requests rightPacket last scalars)
    (model : Assignment) (valid : Models state model)
    (root : Occurrence roles) (payload : GeneralDictionaryReadback.Payload) :
    GeneralDictionaryRecursiveEvidence.Evidence registry (merge state first last).context model root payload ↔
    GeneralDictionaryRecursiveEvidence.Evidence registry state.context model root payload := by
  rw [GeneralDictionaryJointMerge.evidence_merge_iff]
  exact ⟨fun given => given.1,fun given => ⟨given,
    outputs_from_packets state first last leftPacket rightPacket one two scalars left right model valid⟩⟩
end Yulang.GeneralDictionaryScalarJournalMerge
