import Yulang.GeneralNominalRebaseDefinitionSupport244
import Yulang.GeneralNominalRebaseEvidenceView243
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalRebaseEvidenceSupport244
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredFrame179 (Agree)
open GeneralNominalRebaseEvidenceView243
open GeneralNominalCenters (Plan)
open GeneralSourceDictionaries (Occurrence Dictionary)
open Core.PresenceGeneration (CompTerm)
def Supported (predicate : Assignment → Prop) (model : Assignment) : Prop :=
 ∃ names : List Nat, ∀ next, Agree names next model → predicate next
theorem supported_list (items : List α) (predicate : α → Assignment → Prop) (model : Assignment)
 (given : ∀ item ∈ items, Supported (predicate item) model) :
 Supported (fun next => ∀ item ∈ items, predicate item next) model := by
 induction items with
 | nil => exact ⟨[],by simp⟩
 | cons first rest ih =>
   obtain ⟨front,frontValid⟩ := given first (by simp)
   obtain ⟨back,backValid⟩ := ih (fun item member => given item (List.mem_cons_of_mem _ member))
   refine ⟨front ++ back,?_⟩
   intro next same item member
   rcases List.mem_cons.mp member with rfl | member
   · exact frontValid next (fun name present => same name (List.mem_append_left _ present))
   · exact backValid next (fun name present => same name (List.mem_append_right _ present)) item member
theorem output_supported (plan : Plan roles) (mapping : Nat → CompTerm Nat)
 (model : Assignment) (output : GeneralSourceState.Output)
 (valid : GeneralNominalRebaseEffectView243.OutputWitness plan mapping model output) :
 Supported (fun next => GeneralNominalRebaseEffectView243.OutputWitness plan mapping next output) model := by
 obtain ⟨body,provenance,equation,compiled,holds⟩ := valid
 refine ⟨GeneralNominalRebaseEffectActivation243.equationSources equation,?_⟩
 intro next same
 exact ⟨body,provenance,equation,compiled,
   (GeneralNominalRebaseEffectActivation243.equation_iff equation same).mpr holds⟩
theorem certificate_supported (registry : GeneralDeclarations.Registry)
 (state : GeneralNominalCenteredSteps.State roles) (mapping : Nat → CompTerm Nat)
 (model : Assignment) (root : Occurrence roles) (key : Nat) (children : List (Occurrence roles))
 (plan : Plan roles) (valid : Certificate registry state mapping model root key children plan) :
 Supported (fun next => Certificate registry state mapping next root key children plan) model := by
 obtain ⟨names,outputs⟩ := supported_list root.demand.outputs
   (fun output next => GeneralNominalRebaseEffectView243.OutputWitness plan mapping next output) model
   (fun output member => output_supported plan mapping model output (valid.outputs output member))
 refine ⟨GeneralNominalRebasePacketSupport243.sources (GeneralNominalRebasePacketView243.compile plan mapping) ++ names,?_⟩
 intro next same
 exact ⟨valid.frame,valid.children_eq,
   (GeneralNominalRebasePacketSupport243.models_iff _
     (fun name present => same name (List.mem_append_left _ present))).mpr valid.packet,
   outputs next (fun name present => same name (List.mem_append_right _ present))⟩
theorem instance_supported (registry : GeneralDeclarations.Registry)
 (state : GeneralNominalCenteredSteps.State roles) (mapping : Nat → CompTerm Nat)
 (model : Assignment) (root : Occurrence roles) (key : Nat) (children : List (Occurrence roles))
 (valid : Instance registry state mapping model root key children) :
 Supported (fun next => Instance registry state mapping next root key children) model := by
 obtain ⟨plan,valid⟩ := valid
 obtain ⟨names,kept⟩ := certificate_supported registry state mapping model root key children plan valid
 exact ⟨names,fun next same => ⟨plan,kept next same⟩⟩
theorem indexed_supported (registry : GeneralDeclarations.Registry)
 (state : GeneralNominalCenteredSteps.State roles) (mapping : Nat → CompTerm Nat)
 (model : Assignment) (tree : Dictionary roles)
 (valid : GeneralSourceDictionaries.Evidence (Instance registry state mapping model) tree) :
 Supported (fun next => GeneralSourceDictionaries.Evidence (Instance registry state mapping next) tree) model := by
 induction valid with
 | @node root key children nodeRule allChildren ih =>
   obtain ⟨front,localValid⟩ := instance_supported registry state mapping model root key _ nodeRule
   obtain ⟨back,childrenValid⟩ := supported_list children
     (fun child next => GeneralSourceDictionaries.Evidence (Instance registry state mapping next) child) model ih
   refine ⟨front ++ back,?_⟩
   intro next same
   exact .node (localValid next (fun name present => same name (List.mem_append_left _ present)))
     (childrenValid next (fun name present => same name (List.mem_append_right _ present)))
theorem evidence_supported (registry : GeneralDeclarations.Registry)
 (state : GeneralNominalCenteredSteps.State roles) (mapping : Nat → CompTerm Nat)
 (model : Assignment) (root : Occurrence roles) (payload : GeneralDictionaryReadback.Payload)
 (valid : Evidence registry state mapping model root payload) :
 Supported (fun next => Evidence registry state mapping next root payload) model := by
 obtain ⟨tree,readback,valid⟩ := valid
 obtain ⟨names,kept⟩ := indexed_supported registry state mapping model tree valid
 exact ⟨names,fun next same => ⟨tree,readback,kept next same⟩⟩
end Yulang.GeneralNominalRebaseEvidenceSupport244
