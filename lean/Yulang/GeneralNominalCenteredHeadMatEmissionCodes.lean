import Yulang.GeneralNominalCenteredHeadMatSemanticCodes

/-! Center identities are determined by packet data. Enumerating the emitted
sites therefore needs no inductive bound on the values of center names. -/
namespace Yulang.GeneralNominalCenteredHeadMatEmissionCodes
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatSemanticCodes
variable {roles : Roles.RoleDecls} {plan : Plan roles}

def canonicalInput (plan : Plan roles) : Plan roles :=
  ⟨plan.packet,rootSite 0 plan.packet.site.occurrence,rfl⟩

theorem canonical_emitted (plan : Plan roles) : (canonicalInput plan).emitted = plan.emitted := rfl

noncomputable def emissions (context : GeneralNominalCandidates.Context) (code : Code roles) : List (Site roles) := by
  classical
  exact if available : ∃ plan, Config context plan ∧ encode plan = code then
    (Classical.choose available).emitted else []

theorem encode_emitted (configured : Config context plan) (member : site ∈ plan.emitted) :
    site ∈ emissions context (encode plan) := by
  classical
  have available : ∃ other, Config context other ∧ encode other = encode plan := ⟨plan,configured,rfl⟩
  unfold emissions
  rw [dite_eq_left available]
  have spec := Classical.choose_spec available
  exact (GeneralNominalCenteredHeadMatPlanData.emitted_mem
    (same _ _ spec.1 configured spec.2) site).mpr member

noncomputable def pool (context : GeneralNominalCandidates.Context) (registry : Registry)
    (parents : List (Occurrence roles)) (sources : List Nat) : List (Site roles) :=
  (codes context registry (parents.map (rootSite 0)) sources).flatMap (emissions context)

theorem emitted_mem (configured : Config context plan) (registry_eq : plan.packet.registry = registry)
    (parent : plan.packet.site.occurrence ∈ parents) (visible : plan.packet.declaration ∈ registry.declarations)
    (located : GeneralNominalRecursiveCandidates.arguments plan.packet.context plan.packet.site.occurrence = some plan.packet.bounds)
    (supported : ∀ slot, plan.packet.context.state.base.source slot ∈ sources) (member : site ∈ plan.emitted) :
    site ∈ pool context registry parents sources := by
  have listed : encode (canonicalInput plan) ∈ codes context registry (parents.map (rootSite 0)) sources :=
    encode_mem configured registry_eq (List.mem_map.mpr ⟨_,parent,rfl⟩) visible located supported
  exact List.mem_flatMap.mpr ⟨_,listed,encode_emitted configured (canonical_emitted plan ▸ member)⟩

end Yulang.GeneralNominalCenteredHeadMatEmissionCodes
