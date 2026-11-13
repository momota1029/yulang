import Yulang.GeneralDictionaryRecorded168Relocation
import Yulang.GeneralDictionaryScalarLeaf
import Yulang.GeneralDictionarySpineLeaf

/-! Mixed finite Shared certificates: historical nodes with structural
relocation witnesses, and packet-free current scalar or finite-spine leaves.
No constructor assumes Instance, BranchModels, Evidence, or selection. This
syntax is a sufficient certificate, not a new classifier or execution rule. -/
namespace Yulang.GeneralDictionaryMixed168Tree
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport
open GeneralDictionaryReadback (Payload)
open CommonRoleOutermostResolver (All₂)
open GeneralDictionaryRecorded168Relocation (Relocates RelocatedTree)
variable {roles : Roles.RoleDecls}

inductive MixedTree (registry : Registry) (state : Tracked roles) : Occurrence roles → Payload → Prop
  | recorded (packet : Packet roles) (member : packet ∈ state.current.packets)
      (relocation : Relocates registry state packet) (payloads : List Payload)
      (children : All₂ (MixedTree registry state) packet.children payloads) :
      MixedTree registry state packet.site.occurrence (.node packet.declaration.id payloads)
  | scalar (occurrence : Occurrence roles) (declaration : Declaration)
      (visible : declaration ∈ registry.declarations)
      (checked : DeclarationChecked registry.constructors roles declaration)
      (shape : GeneralDictionaryScalarLeaf.ScalarLeafShape state.current.context occurrence declaration) :
      MixedTree registry state occurrence (.node declaration.id [])
  | spine (occurrence : Occurrence roles) (declaration : Declaration)
      (visible : declaration ∈ registry.declarations)
      (checked : DeclarationChecked registry.constructors roles declaration)
      (shape : GeneralDictionarySpineLeaf.SpineLeafShape state.current.context occurrence declaration) :
      MixedTree registry state occurrence (.node declaration.id [])

theorem current_evidence {registry : Registry} {root : Occurrence roles} {state : Tracked roles}
    (formed : GeneralNominalSharedSteps.SourceFormed registry root state)
    (tree : MixedTree registry state occurrence payload)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    GeneralDictionaryRecursiveEvidence.Evidence registry state.current.context model occurrence payload := by
  have metadata := GeneralDictionarySharedMetadata.formed_metadata formed
  induction tree using MixedTree.rec
    (motive_2 := fun sites payloads _ => All₂
      (GeneralDictionaryRecursiveEvidence.Evidence registry state.current.context model) sites payloads) with
  | recorded packet member relocation payloads children ih =>
    exact GeneralDictionaryRecursiveEvidence.evidence_node _ _ _ _ _ _ _
      (GeneralDictionaryRecorded168Relocation.current_instance formed packet member relocation model valid) ih
  | scalar occurrence declaration visible checked shape =>
    exact GeneralDictionaryRecursiveEvidence.evidence_node _ _ _ _ _ _ _
      (GeneralDictionaryScalarLeaf.instance_of_shape _ _ _ _ visible checked shape metadata model valid.1) .nil
  | spine occurrence declaration visible checked shape =>
    exact GeneralDictionaryRecursiveEvidence.evidence_node _ _ _ _ _ _ _
      (GeneralDictionarySpineLeaf.instance_of_shape _ _ _ _ visible checked shape metadata model valid.1) .nil
  | nil => exact .nil
  | cons one rest ihOne ihRest => exact .cons ihOne ihRest

theorem of_relocated_tree (tree : RelocatedTree registry state occurrence payload) :
    MixedTree registry state occurrence payload := by
  induction tree using RelocatedTree.rec
    (motive_2 := fun sites payloads _ => All₂ (MixedTree registry state) sites payloads) with
  | node packet member relocation payloads children ih => exact .recorded packet member relocation payloads ih
  | nil => exact .nil
  | cons one rest ihOne ihRest => exact .cons ihOne ihRest

end Yulang.GeneralDictionaryMixed168Tree
