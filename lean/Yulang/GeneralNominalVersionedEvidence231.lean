import Yulang.GeneralNominalVersionedCandidates231
import Yulang.GeneralNominalVersionedEffects231

/-! Prospective I44 certificate: exact current frame, all ordered children,
total versioned packet, and unchanged explicit/default output provenance.
This defines the successor's evidence component only. It is NOT a completed
SourceBoundary, operational reachability proof, or EvidenceNode theorem. -/
namespace Yulang.GeneralNominalVersionedEvidence231
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)
open CommonRoleOutermostResolver (All₂)
variable {roles : Roles.RoleDecls}

structure Frame (registry : Registry) (state : GeneralNominalCenteredSteps.State roles)
    (root : Occurrence roles) (key : Nat) (plan : Plan roles) : Prop where
  registry_eq : plan.packet.registry = registry
  context_eq : plan.packet.context = state.erased.current.context
  occurrence_eq : plan.packet.site.occurrence = root
  key_eq : plan.packet.declaration.id = key
  raw_recorded : plan.packet.site ∈ state.erased.current.sites
  center_recorded : plan.input ∈ state.sites
  visible : plan.packet.declaration ∈ registry.declarations
  role_eq : plan.packet.declaration.role = root.demand.role
  located : GeneralNominalRecursiveCandidates.arguments plan.packet.context
    (GeneralNominalVersionedCandidates231.inputs root) = some plan.packet.bounds
  prepared : GeneralNominalVersionedCandidates231.Prepared registry state.erased.current.context root plan.packet.declaration

structure Certificate (registry : Registry) (state : GeneralNominalCenteredSteps.State roles)
    (model : Assignment) (root : Occurrence roles) (key : Nat)
    (children : List (Occurrence roles)) (plan : Plan roles) : Prop where
  frame : Frame registry state root key plan
  children_eq : children = GeneralNominalVersionedFrame231.children plan.packet
  packet : GeneralNominalVersionedPlans231.Holds plan model
  outputs : ∀ output ∈ root.demand.outputs, GeneralDictionaryDefaultEvidence204.OutputWitness plan model output

def Instance (registry : Registry) (state : GeneralNominalCenteredSteps.State roles)
    (model : Assignment) : LocalInstance roles :=
  fun root key children => ∃ plan, Certificate registry state model root key children plan

def Evidence (registry : Registry) (state : GeneralNominalCenteredSteps.State roles)
    (model : Assignment) (root : Occurrence roles) (payload : Payload) : Prop :=
  ErasedEvidence (Instance registry state model) root payload

variable {registry : Registry} {state : GeneralNominalCenteredSteps.State roles}
  {model : Assignment} {root : Occurrence roles} {key : Nat}
  {children : List (Occurrence roles)} {plan : Plan roles}

theorem certificate_of_semantics (frame : Frame registry state root key plan)
    (children_eq : children = GeneralNominalVersionedFrame231.children plan.packet)
    (packet : GeneralNominalVersionedPlans231.Holds plan model)
    (ready : GeneralNominalCenteredHeadMatEffects.Ready state root plan)
    (effects : GeneralNominalVersionedEffects231.ClassEffects state root plan model) :
    Certificate registry state model root key children plan := by
  refine ⟨frame,children_eq,packet,?_⟩
  intro output member
  apply GeneralDictionaryDefaultEvidence204Laws.output_of_class_effects ready
    ((GeneralNominalVersionedEffects231.class_effects_iff ..).mp effects)
  exact GeneralNominalCenteredHeadOutputs.request_retained plan.packet.site frame.raw_recorded
    (by rw [frame.occurrence_eq]; exact .refl _)
    (frame.occurrence_eq.symm ▸ member)

theorem finished (source : Certificate registry state model root key children plan) :
    GeneralNominalRecursiveInspection.Finished
      (GeneralNominalRecursiveCandidates.report plan.packet.context plan.packet.declaration plan.packet.bounds) := by
  have prepared : GeneralNominalVersionedCandidates231.Prepared registry plan.packet.context root plan.packet.declaration :=
    source.frame.context_eq.symm ▸ source.frame.prepared
  obtain ⟨_,_,bounds,located,_,done,_⟩ := prepared
  have same : bounds = plan.packet.bounds := Option.some.inj (located.symm.trans source.frame.located)
  subst bounds
  exact done

theorem metadata (source : Certificate registry state model root key children plan) :
    GeneralNominalRecursiveCandidates.Metadata registry state.erased.current.context :=
  source.frame.prepared.1

theorem center_holds (source : Certificate registry state model root key children plan) :
    plan.input.Holds model := source.packet.2.1.2.2.1

theorem instance_models (source : Instance registry state model root key children) :
    GeneralNominalState.Models state.erased.current.context.state model := by
  obtain ⟨plan,source⟩ := source
  simpa only [source.frame.context_eq] using source.packet.1

theorem evidence_node (source : Instance registry state model root key children)
    (given : All₂ (Evidence registry state model) children dictionaries) :
    Evidence registry state model root (.node key dictionaries) :=
  GeneralDictionaryReadback.erased_evidence_node _ _ _ _ _ source given

theorem evidence_leaf (source : Instance registry state model root key []) :
    Evidence registry state model root (.node key []) := evidence_node source .nil
end Yulang.GeneralNominalVersionedEvidence231
