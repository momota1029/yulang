import Yulang.GeneralNominalPatersonLineage

/-! Packet height of an actual settlement proof. Alias transport consumes no
packet level and needs equality of the finite input sizes. -/
namespace Yulang.GeneralNominalSettlementHeight
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalPatersonLineage

inductive Within (state : State roles) : Nat → Occurrence roles → Prop
  | packet (packet : Packet roles) : packet ∈ state.packets →
      (∀ child ∈ packet.children, Within state depth child) →
      Within state (depth+1) packet.site.occurrence
  | alias (first last : GeneralNominalDemandMerging.Site roles) :
      first ∈ state.sites → last ∈ state.sites → Alias state first.occurrence.identity last.occurrence.identity →
      Within state depth first.occurrence → Within state depth last.occurrence

theorem within_mono (proof : Within state first occurrence) (bound : first ≤ last) :
    Within state last occurrence := by
  induction proof generalizing last with
  | @packet depth packet member children ih =>
    cases last with
    | zero => omega
    | succ last => exact .packet packet member (fun child present => ih child present (by omega))
  | alias a b one two same proof ih => exact .alias a b one two same (ih bound)

theorem within_discharged (proof : Within state depth occurrence) : Discharged state occurrence := by
  induction proof with
  | packet packet member children ih => exact .packet packet member ih
  | alias first last one two same proof ih => exact .alias first last one two same ih

def AliasMass (state : State roles) (labels : Occurrence roles → List GeneralDeclarationPatterns.Pattern) : Prop :=
  ∀ first ∈ state.sites, ∀ last ∈ state.sites,
    Alias state first.occurrence.identity last.occurrence.identity →
    mass (labels first.occurrence) = mass (labels last.occurrence)

theorem discharged_height {roles : Roles.RoleDecls} {state : State roles} {occurrence : Occurrence roles}
    {labels : Occurrence roles → List GeneralDeclarationPatterns.Pattern}
    (realized : ∀ packet ∈ state.packets, Nonempty (Instantiation labels packet))
    (aliases : AliasMass state labels) (done : Discharged state occurrence) :
    Within state (mass (labels occurrence)+1) occurrence := by
  induction done with
  | packet packet member children ih =>
    obtain ⟨instantiation⟩ := realized packet member
    apply Within.packet packet member
    intro child present
    exact within_mono (ih child present) (by have strict := instantiated_child instantiation present; omega)
  | alias first last one two same done ih =>
    rw [← aliases first one last two same]
    exact .alias first last one two same ih

theorem packet_height {roles : Roles.RoleDecls} {state : State roles} {packet : Packet roles}
    {labels : Occurrence roles → List GeneralDeclarationPatterns.Pattern}
    (realized : ∀ packet ∈ state.packets, Nonempty (Instantiation labels packet))
    (aliases : AliasMass state labels)
    (done : GeneralNominalSettledSupport.PacketSettled state packet) :
    ∀ child ∈ packet.children, Within state (mass (labels packet.site.occurrence)) child := by
  obtain ⟨instantiation⟩ := realized packet done.1
  intro child present
  exact within_mono (discharged_height realized aliases (done.2 child present))
    (by have strict := instantiated_child instantiation present; omega)

end Yulang.GeneralNominalSettlementHeight
