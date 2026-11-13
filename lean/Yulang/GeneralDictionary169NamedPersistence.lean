import Yulang.GeneralDictionary169NamedTree
import Yulang.GeneralDictionary169MixedPersistence

/-! Structural named-output certificates survive ordinary Shared continuations.
Descriptor refresh is excluded; no initial Evidence or Instance is assumed. -/
namespace Yulang.GeneralDictionary169NamedPersistence
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalRecursiveCandidates
open GeneralDictionaryOrdinaryTransport GeneralDictionaryObservedFiniteRequests
open GeneralNominalSaturationState GeneralNominalSupport
open GeneralDictionary169NamedTree (NamedTree)
open GeneralDictionaryReadback (Payload)
open CommonRoleOutermostResolver (All₂)
variable {roles : Roles.RoleDecls}

def tree (state : GeneralNominalState.State) (reserved atoms allocated)
    {slot query} (shape : Tree state slot query) :
    Tree (extendState state reserved atoms allocated) slot query :=
  match shape with
  | .scalar slot base head => Tree.scalar (state := extendState state reserved atoms allocated) slot base head
  | .nominal slot descriptor recorded slots queries parameters branches =>
      Tree.nominal (state := extendState state reserved atoms allocated) slot descriptor recorded slots queries parameters
        (fun index => tree state reserved atoms allocated (branches index))

theorem observed (state : GeneralNominalState.State) (reserved atoms allocated)
    (interpretation : GeneralNominalInspection.Interpretation) (requests)
    (shapes : Observed state interpretation requests) :
    Observed (extendState state reserved atoms allocated) interpretation requests := by
  intro request member
  obtain ⟨slot,same,⟨shape⟩⟩ := shapes request member
  exact ⟨slot,same,⟨tree state reserved atoms allocated shape⟩⟩

def leaf (registry : Registry) (context : Context) (reserved atoms allocated)
    {root : Occurrence roles} {declaration : Declaration}
    {checked : DeclarationChecked registry.constructors roles declaration}
    (shape : GeneralDictionary169NamedLeaf.LeafShape registry context root declaration checked) :
    GeneralDictionary169NamedLeaf.LeafShape registry (extend context reserved atoms allocated) root declaration checked where
  terminal := shape.terminal
  role := shape.role
  slot := shape.slot
  base := shape.base
  noNominal := shape.noNominal
  head := shape.head
  inputs := shape.inputs
  query := shape.query
  located := shape.located
  defined := shape.defined
  observed := by
    rw [candidate_report_extended,bindings_report]
    exact observed context.state reserved atoms allocated context.interpretation _ shape.observed

theorem extension {registry : Registry} {before after : Tracked roles}
    (members : ∀ packet ∈ before.current.packets, packet ∈ after.current.packets)
    (growth : GeneralDictionaryOrdinaryTrace.Extension before.current.context after.current.context)
    (certificate : NamedTree registry before occurrence payload) :
    NamedTree registry after occurrence payload := by
  induction certificate using NamedTree.rec
    (motive_2 := fun sites payloads _ => All₂ (NamedTree registry after) sites payloads) with
  | mixed old => exact .mixed (GeneralDictionary169MixedPersistence.extension members growth old)
  | recorded packet member relocation payloads children ih =>
    exact .recorded packet (members packet member)
      (GeneralDictionary169RelocationComposition.packet_extension registry before after packet relocation growth) payloads ih
  | named occurrence declaration visible checked shape =>
    obtain ⟨reserved,atoms,allocated,equal⟩ := growth
    apply NamedTree.named occurrence declaration visible checked
    rw [equal]
    exact leaf registry before.current.context reserved atoms allocated shape
  | nil => exact .nil
  | cons one rest ihOne ihRest => exact .cons ihOne ihRest

theorem ordinary_steps {registry : Registry} {root : Occurrence roles} {before after : Tracked roles}
    (path : B4Target.Steps (GeneralDictionarySharedEvidenceTrace.OrdinaryStep registry root) before after)
    (certificate : NamedTree registry before occurrence payload) :
    NamedTree registry after occurrence payload :=
  extension (GeneralDictionary169MixedPersistence.packets_steps
      (GeneralDictionarySharedEvidenceTrace.ordinary_trace_real _ _ _ _ path))
    (GeneralDictionarySharedEvidenceTrace.ordinary_trace_extension _ _ _ _ path) certificate

theorem current_evidence {registry : Registry} {root : Occurrence roles} {before after : Tracked roles}
    (path : B4Target.Steps (GeneralDictionarySharedEvidenceTrace.OrdinaryStep registry root) before after)
    (formed : GeneralNominalSharedSteps.SourceFormed registry root after)
    (certificate : NamedTree registry before occurrence payload)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models after.current model) :
    GeneralDictionaryRecursiveEvidence.Evidence registry after.current.context model occurrence payload :=
  GeneralDictionary169NamedTree.current_evidence formed (ordinary_steps path certificate) model valid
end Yulang.GeneralDictionary169NamedPersistence
