import Yulang.GeneralNominalVersionedPlans231
import Yulang.GeneralNominalVersionedTransport231
set_option backward.isDefEq.respectTransparency false

/-! Complete canonical child-site emission for the versioned packet. These
are construction and model-support lemmas, not a successor boundary or a
claim that every emitted child is already selected or recursively evidenced. -/
namespace Yulang.GeneralNominalVersionedChildren232
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedFrame231 (childSite children)

/-- Actual requirement order is canonicalized exactly as in `children`. -/
def emitted (plan : Plan roles) : List (Site roles) :=
  (GeneralCanonicalChildOrder.canonicalRequirements plan.packet.declaration.requirements).attach.map fun clause =>
    childSite plan clause.val (plan.packet.checked.signature.2.2.2 clause.val
      ((GeneralCanonicalChildOrder.canonicalRequirements_perm _).mem_iff.mpr clause.property))

def rawSites (plan : Plan roles) : List (GeneralNominalDemandMerging.Site roles) :=
  (emitted plan).map Site.observed

def edges (plan : Plan roles) : List (Occurrence roles × Occurrence roles) :=
  (children plan.packet).map fun child => (plan.packet.site.occurrence,child)

theorem emitted_occurrences (plan : Plan roles) :
    (emitted plan).map Site.occurrence = children plan.packet := by
  unfold emitted children GeneralDictionaryEmissionPlans.children
    GeneralCanonicalChildOrder.canonicalEmit GeneralDeclarationDemands.emitAll
  simp only [List.map_map]
  rfl

theorem emitted_holds (valid : GeneralNominalVersionedPlans231.Holds plan model)
    (member : site ∈ emitted plan) : site.Holds model := by
  obtain ⟨clause,_,rfl⟩ := List.mem_map.mp member
  exact (valid.2.1.2.2.2.2.2.2 clause.val
    ((GeneralCanonicalChildOrder.canonicalRequirements_perm _).mem_iff.mpr clause.property) _).1

theorem raw_holds (valid : GeneralNominalVersionedPlans231.Holds plan model)
    (member : site ∈ rawSites plan) : GeneralNominalSaturationState.SiteHolds site model := by
  obtain ⟨center,present,rfl⟩ := List.mem_map.mp member
  exact observed_holds center model (emitted_holds valid present)

theorem emitted_child_iff : child ∈ children plan.packet ↔
    ∃ site ∈ emitted plan, site.occurrence = child := by
  rw [← emitted_occurrences]
  exact List.mem_map

theorem edge_iff : edge ∈ edges plan ↔
    ∃ child ∈ children plan.packet, (plan.packet.site.occurrence,child) = edge :=
  List.mem_map

theorem child_edge (member : child ∈ children plan.packet) :
    (plan.packet.site.occurrence,child) ∈ edges plan :=
  List.mem_map.mpr ⟨child,member,rfl⟩

theorem edge_site (member : (root,child) ∈ edges plan) :
    root = plan.packet.site.occurrence ∧ ∃ site ∈ emitted plan, site.occurrence = child := by
  obtain ⟨next,present,equal⟩ := edge_iff.mp member
  have same := Prod.mk.inj equal
  exact ⟨same.1.symm,emitted_child_iff.mp (same.2 ▸ present)⟩

theorem appended_sites_holds
    (old : ∀ site ∈ prior, Site.Holds site model)
    (valid : GeneralNominalVersionedPlans231.Holds plan model) :
    ∀ site ∈ prior ++ emitted plan, Site.Holds site model := by
  intro site member
  exact (List.mem_append.mp member).elim (old site) (emitted_holds valid)

theorem appended_raw_holds
    (old : ∀ site ∈ prior, GeneralNominalSaturationState.SiteHolds site model)
    (valid : GeneralNominalVersionedPlans231.Holds plan model) :
    ∀ site ∈ prior ++ rawSites plan, GeneralNominalSaturationState.SiteHolds site model := by
  intro site member
  exact (List.mem_append.mp member).elim (old site) (raw_holds valid)

theorem appended_child_edge (member : child ∈ children plan.packet) :
    (plan.packet.site.occurrence,child) ∈ prior ++ edges plan :=
  List.mem_append_right _ (child_edge member)

theorem emitted_length (plan : Plan roles) :
    (emitted plan).length = plan.packet.declaration.requirements.length := by
  simp only [emitted,List.length_map,List.length_attach]
  exact (GeneralCanonicalChildOrder.canonicalRequirements_perm _).length_eq.symm

/-- Every complete canonical child has a recorded raw observation of its
actual centers, not a recovered observation from aggregate endpoints. -/
theorem child_raw_site (member : child ∈ children plan.packet) :
    ∃ site ∈ rawSites plan, site.occurrence = child := by
  obtain ⟨site,present,same⟩ := emitted_child_iff.mp member
  exact ⟨site.observed,List.mem_map.mpr ⟨site,present,rfl⟩,same⟩

/-- An installed complete edge list extends actual Generated paths. The
caller must supply that the parent is generated in the resulting state. -/
theorem generated_child (after : GeneralNominalSaturationState.State roles)
    (installed : edges plan ⊆ after.edges)
    (parent : GeneralNominalSaturationState.Generated after root plan.packet.site.occurrence)
    (member : child ∈ children plan.packet) :
    GeneralNominalSaturationState.Generated after root child :=
  .child parent (installed (child_edge member))

theorem appended_edge_iff : edge ∈ prior ++ edges plan ↔
    edge ∈ prior ∨ ∃ child ∈ children plan.packet, (plan.packet.site.occurrence,child) = edge := by
  rw [List.mem_append,edge_iff]

end Yulang.GeneralNominalVersionedChildren232
