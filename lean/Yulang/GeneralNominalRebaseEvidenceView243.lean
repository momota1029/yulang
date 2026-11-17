import Yulang.GeneralNominalRebasePacketView243
import Yulang.GeneralNominalVersionedEvidence231
set_option backward.isDefEq.respectTransparency false
/-! Exact recursive certificate readback through one common expression mapping.
All child evidence uses the same interpreted assignment. No per-child internal
witness is introduced. Operational construction of certificates is separate. -/
namespace Yulang.GeneralNominalRebaseEvidenceView243
open Core.PresenceGeneration (CompTerm)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRebaseRawView243 (read)
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralDictionaryReadback (Payload)
open CommonRoleOutermostResolver (All₂)

structure Certificate (registry : Registry) (state : GeneralNominalCenteredSteps.State roles)
 (mapping : Nat → CompTerm Nat) (model : Assignment) (root : Occurrence roles) (key : Nat)
 (children : List (Occurrence roles)) (plan : Plan roles) : Prop where
 frame : GeneralNominalVersionedEvidence231.Frame registry state root key plan
 children_eq : children = GeneralNominalVersionedFrame231.children plan.packet
 packet : (GeneralNominalRebasePacketView243.compile plan mapping).Holds model
 outputs : ∀ output ∈ root.demand.outputs, GeneralNominalRebaseEffectView243.OutputWitness plan mapping model output

theorem certificate_exact (registry : Registry) (state : GeneralNominalCenteredSteps.State roles)
 (mapping : Nat → CompTerm Nat) (model : Assignment) (root : Occurrence roles) (key : Nat)
 (children : List (Occurrence roles)) (plan : Plan roles) :
 Certificate registry state mapping model root key children plan ↔
 GeneralNominalVersionedEvidence231.Certificate registry state (read mapping model) root key children plan := by
 constructor
 · intro source
   exact ⟨source.frame,source.children_eq,(GeneralNominalRebasePacketView243.compile_exact plan mapping model).mp source.packet,
     fun output member => (GeneralNominalRebaseEffectView243.output_exact plan mapping model output).mp (source.outputs output member)⟩
 · intro source
   exact ⟨source.frame,source.children_eq,(GeneralNominalRebasePacketView243.compile_exact plan mapping model).mpr source.packet,
     fun output member => (GeneralNominalRebaseEffectView243.output_exact plan mapping model output).mpr (source.outputs output member)⟩

def Instance (registry : Registry) (state : GeneralNominalCenteredSteps.State roles)
 (mapping : Nat → CompTerm Nat) (model : Assignment) : LocalInstance roles :=
 fun root key children => ∃ plan, Certificate registry state mapping model root key children plan

theorem instance_exact (registry : Registry) (state : GeneralNominalCenteredSteps.State roles)
 (mapping : Nat → CompTerm Nat) (model : Assignment) :
 Instance registry state mapping model = GeneralNominalVersionedEvidence231.Instance registry state (read mapping model) := by
 funext root key children
 apply propext
 exact exists_congr (fun plan => certificate_exact registry state mapping model root key children plan)

def Evidence (registry : Registry) (state : GeneralNominalCenteredSteps.State roles)
 (mapping : Nat → CompTerm Nat) (model : Assignment) (root : Occurrence roles) (payload : Payload) : Prop :=
 ErasedEvidence (Instance registry state mapping model) root payload

theorem evidence_exact (registry : Registry) (state : GeneralNominalCenteredSteps.State roles)
 (mapping : Nat → CompTerm Nat) (model : Assignment) (root : Occurrence roles) (payload : Payload) :
 Evidence registry state mapping model root payload ↔
 GeneralNominalVersionedEvidence231.Evidence registry state (read mapping model) root payload := by
 unfold Evidence GeneralNominalVersionedEvidence231.Evidence
 rw [instance_exact]

theorem node (registry : Registry) (state : GeneralNominalCenteredSteps.State roles)
 (mapping : Nat → CompTerm Nat) (model : Assignment) (root : Occurrence roles) (key : Nat)
 (children : List (Occurrence roles)) (dictionaries : List Payload)
 (source : Instance registry state mapping model root key children)
 (given : All₂ (Evidence registry state mapping model) children dictionaries) :
 Evidence registry state mapping model root (.node key dictionaries) :=
 GeneralDictionaryReadback.erased_evidence_node _ _ _ _ _ source given

/-- One executable finite lookup supplies the same old interpretation to the
whole tree; it is not an existential choice for each child. -/
theorem inline_exact (registry : Registry) (state : GeneralNominalCenteredSteps.State roles)
 (entries : List GeneralNominalFiniteEquationRealization236.Entry)
 (coherent : GeneralNominalRebaseEscapedProjection242.Coherent entries) (model : Assignment)
 (root : Occurrence roles) (payload : Payload) :
 Evidence registry state (GeneralNominalRebaseLookup242.substitution entries) model root payload ↔
 GeneralNominalVersionedEvidence231.Evidence registry state (GeneralNominalFiniteEquationRealization236.patch entries model) root payload := by
 rw [evidence_exact]
 change GeneralNominalVersionedEvidence231.Evidence registry state (GeneralNominalRebaseLookup242.patch entries model) root payload ↔ _
 rw [GeneralNominalRebaseLookup242.patch_exact entries coherent model]
end Yulang.GeneralNominalRebaseEvidenceView243
