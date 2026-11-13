import Yulang.GeneralDictionary169NamedTree
import Yulang.GeneralDictionary170NamedSpine

/-! Additive recursive dictionaries with finite nominal input spines and
observed named outputs. Structural certificates contain no semantic evidence. -/
namespace Yulang.GeneralDictionary171SpineTree
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralDictionaryReadback
open CommonRoleOutermostResolver (All₂)
variable {roles : Roles.RoleDecls}

inductive Tree (registry : Registry) (state : Tracked roles) : Occurrence roles → Payload → Prop
  | old (tree : GeneralDictionary169NamedTree.NamedTree registry state occurrence payload) :
      Tree registry state occurrence payload
  | recorded (packet : Packet roles) (member : packet ∈ state.current.packets)
      (relocation : GeneralDictionaryRecorded168Relocation.Relocates registry state packet)
      (payloads : List Payload)
      (children : All₂ (Tree registry state) packet.children payloads) :
      Tree registry state packet.site.occurrence (.node packet.declaration.id payloads)
  | namedSpine (occurrence : Occurrence roles) (declaration : Declaration)
      (visible : declaration ∈ registry.declarations)
      (checked : DeclarationChecked registry.constructors roles declaration)
      (shape : GeneralDictionary170NamedSpine.Shape registry state.current.context occurrence declaration checked) :
      Tree registry state occurrence (.node declaration.id [])

theorem current_evidence {registry : Registry} {root : Occurrence roles} {state : Tracked roles}
    (formed : GeneralNominalSharedSteps.SourceFormed registry root state)
    (tree : Tree registry state occurrence payload)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    GeneralDictionaryRecursiveEvidence.Evidence registry state.current.context model occurrence payload := by
  have metadata := GeneralDictionarySharedMetadata.formed_metadata formed
  induction tree using Tree.rec
    (motive_2 := fun sites payloads _ => All₂
      (GeneralDictionaryRecursiveEvidence.Evidence registry state.current.context model) sites payloads) with
  | old previous => exact GeneralDictionary169NamedTree.current_evidence formed previous model valid
  | recorded packet member relocation payloads children ih =>
    exact GeneralDictionaryRecursiveEvidence.evidence_node _ _ _ _ _ _ _
      (GeneralDictionaryRecorded168Relocation.current_instance formed packet member relocation model valid) ih
  | namedSpine occurrence declaration visible checked shape =>
    exact GeneralDictionary170NamedSpine.evidence_of_shape _ _ _ _ visible checked shape metadata model valid.1
  | nil => exact .nil
  | cons one rest ihOne ihRest => exact .cons ihOne ihRest
end Yulang.GeneralDictionary171SpineTree
