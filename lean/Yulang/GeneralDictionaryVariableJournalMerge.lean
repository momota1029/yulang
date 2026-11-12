import Yulang.GeneralDictionaryJointMerge

/-! Non-scalar merge equations from repeated actual-mode variable requests in
one historical materialized packet. The packet need not be a current candidate.
The assignment values may be arbitrary structural/nominal types. -/
namespace Yulang.GeneralDictionaryVariableJournalMerge
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalDemandMerging (Site outputAtoms)
open GeneralNominalCommonBridge (Assignment)
variable {roles : Roles.RoleDecls}

/-- The mapping records the shared parent binder for each requested name. It
is checked against the historical generated schema, not asserted as meaning. -/
def Requests (packet : Packet roles) (site : Site roles) (names : Nat → Nat) : Prop :=
  ∀ output ∈ site.occurrence.demand.outputs,
    (⟨names output.name,.source output.target,.actual⟩ : GeneralNominalMaterialization.Use) ∈
      (GeneralNominalRecursiveCandidates.generated packet.registry packet.context packet.site.occurrence
        packet.declaration packet.checked packet.bounds).variables

/-- Both outputs occur as the same actual variable in one recorded schema.
Materialization coherence supplies the equality; no scalar bound is needed. -/
theorem outputs_from_packet (state : State roles) (first last : Site roles)
    (packet : Packet roles) (recorded : packet ∈ state.packets)
    (names : Nat → Nat) (left : Requests packet first names) (right : Requests packet last names)
    (model : Assignment) (valid : Models state model) :
    PresenceNormalForm.All CommonNominalFullCarrier.model model (outputAtoms first last) := by
  apply (GeneralNominalDemandMerging.output_atoms_exact first last model).mpr
  intro a ha b hb same
  have material := (valid.2.1 packet recorded).2.2
  exact material.2.2.1 _ (left a ha) _ (right b hb)
    (congrArg names same) rfl rfl _ _ (.source a.target) (.source b.target)

/-- The real merge preserves all journal assignments under these historical
variable requests. It does not prove arbitrary distinct packets cohere. -/
theorem models_merge_iff (state : State roles) (first last : Site roles)
    (packet : Packet roles) (recorded : packet ∈ state.packets)
    (names : Nat → Nat) (left : Requests packet first names) (right : Requests packet last names)
    (model : Assignment) : Models (merge state first last) model ↔ Models state model := by
  rw [merge_models]
  exact ⟨fun given => given.1,fun given => ⟨given,
    outputs_from_packet state first last packet recorded names left right model given⟩⟩

/-- FULL recursive dictionary evidence, at the same assignment and payload,
is invariant under this actual non-scalar-output merge. -/
theorem evidence_merge_iff (registry : Registry) (state : State roles) (first last : Site roles)
    (packet : Packet roles) (recorded : packet ∈ state.packets)
    (names : Nat → Nat) (left : Requests packet first names) (right : Requests packet last names)
    (model : Assignment) (valid : Models state model)
    (root : Occurrence roles) (payload : GeneralDictionaryReadback.Payload) :
    GeneralDictionaryRecursiveEvidence.Evidence registry (merge state first last).context model root payload ↔
      GeneralDictionaryRecursiveEvidence.Evidence registry state.context model root payload := by
  rw [GeneralDictionaryJointMerge.evidence_merge_iff]
  exact ⟨fun given => given.1,fun given => ⟨given,
    outputs_from_packet state first last packet recorded names left right model valid⟩⟩
end Yulang.GeneralDictionaryVariableJournalMerge
