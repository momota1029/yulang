import Yulang.GeneralVersionedBinderTargets312

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralVersionedBinderTable312
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralVersionedHistoryEvidence310 (Compiled)
open GeneralNominalVersionedFrame231 (binder)
open GeneralNominalCommonBridge (Assignment)
open GeneralVersionedAliasHeadWrites312 (rows pool)
open GeneralVersionedBinderTargets312 (actualName cases_binder point_in_pool point_agrees same_fresh_name)
open GeneralFiniteTypedWrites312 (Coherent Protected Holds transitive symmetric reflexive)
open CommonNominalFullCarrier (Equivalent)
variable {roles : Roles.RoleDecls}

def PrivateAgrees (now past : Plan roles) (names : List Nat) (m : Assignment) : Prop :=
  ∀ use ∈ now.headSchema.variables,
    binder now use.name = actualName now use.name →
    actualName now use.name ∈ pool now names →
    Equivalent (m (actualName now use.name)).1 (m (past.binder use.name)).1

theorem table {registry : Registry} {root : Occurrence roles} {s : State roles} {now past : Plan roles}
    (checked : (boundary roles).Checked registry)
    (path : B4TargetV8.Reachable (boundary roles) registry root s)
    (frame : Frame (Compiled registry) s.core focus key now) (stored : past ∈ s.plans)
    (alias : GeneralNominalSaturationState.Alias s.core.erased.current
      now.packet.site.occurrence.identity past.packet.site.occurrence.identity)
    (sameRule : now.packet.declaration = past.packet.declaration)
    (m : Assignment) (valid : Models s m) (old : PrivateAgrees now past names m) :
    Coherent (rows now past m) ∧ Protected (rows now past m) (pool now names) m := by
  have fixed : Protected (rows now past m) (pool now names) m := by
    intro row placed hit
    obtain ⟨use,present,rfl⟩ := List.mem_map.mp placed
    have input := GeneralNominalHeadSchemaNames186.head_input now use present
    unfold Holds
    change Equivalent (m (binder now use.name)).1 (m (past.binder use.name)).1
    rcases cases_binder now use.name input with ⟨point,read,found⟩|fresh
    · rw [found]
      exact point_agrees checked path frame stored alias sameRule m valid use.name point read
    · rw [fresh]
      exact old use present fresh (fresh ▸ hit)
  refine ⟨?_,fixed⟩
  intro a aMember b bMember same
  by_cases inside : a.1 ∈ pool now names
  · have one := fixed a aMember inside
    have two := fixed b bMember (same ▸ inside)
    unfold Holds at one two
    rw [same] at one
    exact transitive (symmetric one) two
  · obtain ⟨first,left,rfl⟩ := List.mem_map.mp aMember
    obtain ⟨last,right,rfl⟩ := List.mem_map.mp bMember
    have firstNew : binder now first.name = actualName now first.name := by
      rcases cases_binder now first.name (GeneralNominalHeadSchemaNames186.head_input now first left) with ⟨point,read,eq⟩|fresh
      · exact False.elim (inside (eq.symm ▸ point_in_pool now names first.name point read))
      · exact fresh
    have lastNew : binder now last.name = actualName now last.name := by
      rcases cases_binder now last.name (GeneralNominalHeadSchemaNames186.head_input now last right) with ⟨point,read,eq⟩|fresh
      · exact False.elim (inside (same.symm ▸ eq.symm ▸ point_in_pool now names last.name point read))
      · exact fresh
    have name := same_fresh_name now (firstNew.symm.trans (same.trans lastNew))
    change Equivalent (m (past.binder first.name)).1 (m (past.binder last.name)).1
    rw [name]
    exact reflexive _

theorem certified {registry : Registry} {root : Occurrence roles} {s : State roles} {now past : Plan roles}
    (checked : (boundary roles).Checked registry)
    (path : B4TargetV8.Reachable (boundary roles) registry root s)
    (frame : Frame (Compiled registry) s.core now.packet.site.occurrence now.packet.declaration.id now)
    (stored : past ∈ s.plans)
    (alias : GeneralNominalSaturationState.Alias s.core.erased.current
      now.packet.site.occurrence.identity past.packet.site.occurrence.identity)
    (sameRule : now.packet.declaration = past.packet.declaration)
    (old : ∀ m, Models s m → PrivateAgrees now past names m) :
    GeneralVersionedHistoricalJoint312.HeadTableReady s now past names := by
  intro m valid _
  exact table checked path frame stored alias sameRule m valid (old m valid)

end Yulang.GeneralVersionedBinderTable312
