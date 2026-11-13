import Yulang.GeneralDictionary169NamedLeaf
import Yulang.GeneralDictionary169NamedGap

/-! Additive structural coverage for actual observed named-output leaves.
Recorded parents may recursively mix the old certificates and these new leaves.
No semantic Evidence is stored in the certificate. -/
namespace Yulang.GeneralDictionary169NamedTree
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralDictionaryReadback
open CommonRoleOutermostResolver (All₂)
variable {roles : Roles.RoleDecls}

inductive NamedTree (registry : Registry) (state : Tracked roles) : Occurrence roles → Payload → Prop
  | mixed (old : GeneralDictionaryMixed168Tree.MixedTree registry state occurrence payload) :
      NamedTree registry state occurrence payload
  | recorded (packet : Packet roles) (member : packet ∈ state.current.packets)
      (relocation : GeneralDictionaryRecorded168Relocation.Relocates registry state packet)
      (payloads : List Payload)
      (children : All₂ (NamedTree registry state) packet.children payloads) :
      NamedTree registry state packet.site.occurrence (.node packet.declaration.id payloads)
  | named (occurrence : Occurrence roles) (declaration : Declaration)
      (visible : declaration ∈ registry.declarations)
      (checked : DeclarationChecked registry.constructors roles declaration)
      (shape : GeneralDictionary169NamedLeaf.LeafShape registry state.current.context occurrence declaration checked) :
      NamedTree registry state occurrence (.node declaration.id [])

theorem current_evidence {registry : Registry} {root : Occurrence roles} {state : Tracked roles}
    (formed : GeneralNominalSharedSteps.SourceFormed registry root state)
    (tree : NamedTree registry state occurrence payload)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    GeneralDictionaryRecursiveEvidence.Evidence registry state.current.context model occurrence payload := by
  have metadata := GeneralDictionarySharedMetadata.formed_metadata formed
  induction tree using NamedTree.rec
    (motive_2 := fun sites payloads _ => All₂
      (GeneralDictionaryRecursiveEvidence.Evidence registry state.current.context model) sites payloads) with
  | mixed old => exact GeneralDictionaryMixed168Tree.current_evidence formed old model valid
  | recorded packet member relocation payloads children ih =>
    exact GeneralDictionaryRecursiveEvidence.evidence_node _ _ _ _ _ _ _
      (GeneralDictionaryRecorded168Relocation.current_instance formed packet member relocation model valid) ih
  | named occurrence declaration visible checked shape =>
    exact GeneralDictionary169NamedLeaf.evidence_of_shape _ _ _ _ visible checked shape metadata model valid.1
  | nil => exact .nil
  | cons one rest ihOne ihRest => exact .cons ihOne ihRest

open GeneralDictionaryFiniteObservedExample

theorem actual_tree : NamedTree registry start root (.node declaration.id []) :=
  .named root declaration (by simp) checked GeneralDictionary169NamedLeaf.actual_shape

theorem strict_coverage :
    NamedTree registry start root (.node declaration.id []) ∧
    ∀ payload, ¬ GeneralDictionaryMixed168Tree.MixedTree registry start root payload :=
  ⟨actual_tree,GeneralDictionary169NamedGap.actual_not_mixed⟩

theorem stable_named_interpretation :
    GeneralNominalSharedSteps.SourceFormed registry root start ∧
    GeneralNominalSharedSteps.Stable registry start root ∧
    NamedTree registry start root (.node declaration.id []) ∧
    Models start.current model ∧
    (∀ assignment, Models start.current assignment →
      GeneralDictionaryRecursiveEvidence.Evidence registry start.current.context assignment root (.node declaration.id [])) ∧
    ∀ payload, ¬ GeneralDictionaryMixed168Tree.MixedTree registry start root payload :=
  ⟨GeneralDictionary169SharedStable.actual_formed,GeneralDictionary169SharedStable.actual_stable,actual_tree,
    (initial_models ..).mpr state_models,
    fun assignment valid => current_evidence GeneralDictionary169SharedStable.actual_formed actual_tree assignment valid,
    GeneralDictionary169NamedGap.actual_not_mixed⟩
end Yulang.GeneralDictionary169NamedTree
