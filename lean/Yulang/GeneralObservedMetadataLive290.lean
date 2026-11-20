import Yulang.GeneralObservedMetadataBodies290

/-! Use the actual current alias-class requests, not a caller-supplied
body list. Compare compilation in a plan's historical environment
against proposed tables for that exact set of requested bodies. -/
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralObservedMetadataLive290
open GeneralDeclarationPatterns (Constructors)
open GeneralNominalInspection (Interpretation)
open GeneralNominalCenters (Plan)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalCenteredSteps (State)
open GeneralDictionaryAssociatedProvenance (Body lookup)
open GeneralNominalCenteredHeadOutputs (requests EqualOutputs)
open GeneralNominalCenteredHeadMatEffects (ClassEffects bodyVariables)
open GeneralNominalCommonBridge (Assignment)
open GeneralObservedMetadataBodies290 (bodyKeys bodySchemaFrom bodySchema_eq bodyHolds_iff)
open GeneralObservedMetadataEntry290 (LocalEqual)
open GeneralObservedMetadataScope290 (certify good_exact)

def liveBodies (s : State roles) (root : Occurrence roles) (plan : Plan roles) : List Body :=
  (GeneralRebaseExecutableRequests262.requests s root).filterMap fun out =>
    lookup roles plan.packet.declaration out.name

def liveKeys (s : State roles) (root : Occurrence roles) (plan : Plan roles) : List Nat :=
  (liveBodies s root plan).flatMap bodyKeys

theorem live_body {s : State roles} {root : Occurrence roles} {plan : Plan roles}
    {out : GeneralSourceState.Output} {body : Body} (requested : out ∈ requests s root)
    (supplied : lookup roles plan.packet.declaration out.name = some body) :
    body ∈ liveBodies s root plan := by
  apply List.mem_filterMap.mpr
  rw [GeneralRebaseExecutableRequests262.requests_eq]
  exact ⟨out,requested,supplied⟩

theorem live_key {s : State roles} {root : Occurrence roles} {plan : Plan roles}
    {out : GeneralSourceState.Output} {body : Body} (requested : out ∈ requests s root)
    (supplied : lookup roles plan.packet.declaration out.name = some body)
    {key : Nat} (seen : key ∈ bodyKeys body) : key ∈ liveKeys s root plan :=
  List.mem_flatMap.mpr ⟨body,live_body requested supplied,seen⟩

def ProposedModels (s : State roles) (root : Occurrence roles) (plan : Plan roles) (c : Constructors)
    (i : Interpretation) (m : Assignment) : Prop :=
  (∀ out ∈ requests s root, ∀ b, lookup roles plan.packet.declaration out.name = some b →
    (bodySchemaFrom c i out.target b).Holds (bodyVariables plan m b) m) ∧ EqualOutputs s root m

theorem models_iff {s : State roles} {root : Occurrence roles} {plan : Plan roles}
    {c : Constructors} {i : Interpretation}
    (h : LocalEqual (liveKeys s root plan) plan.packet.registry.constructors plan.packet.context.interpretation c i)
    (m : Assignment) : ProposedModels s root plan c i m ↔ ClassEffects s root plan m := by
  refine ⟨fun fact => ⟨?_,fact.2⟩,fun fact => ⟨?_,fact.2⟩⟩
  · intro o ro b sb
    exact (bodyHolds_iff plan c i o.target b m
      (h.restrict (fun _ read => live_key ro sb read))).mp (fact.1 o ro b sb)
  · intro o ro b sb
    exact (bodyHolds_iff plan c i o.target b m
      (h.restrict (fun _ read => live_key ro sb read))).mpr (fact.1 o ro b sb)

theorem accepted_live_models {s : State roles} {root : Occurrence roles} {plan : Plan roles}
    {c : Constructors} {i : Interpretation}
    (verified : certify (liveKeys s root plan) plan.packet.registry.constructors plan.packet.context.interpretation c i =
        .good) (m : Assignment) : ProposedModels s root plan c i m ↔ ClassEffects s root plan m :=
  models_iff ((good_exact ..).mp verified).1 m

end Yulang.GeneralObservedMetadataLive290
