import Yulang.GeneralVersionedBinderTable312

set_option backward.isDefEq.respectTransparency false
/-! A protected private actual binder is justified by an actual old owner,
not by name reservation. The same assignment reuses the owner's reading
and the distinct aliased historical head's reading. -/
namespace Yulang.GeneralVersionedBinderReuse312
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralVersionedHistoryEvidence310 (Compiled)
open GeneralNominalVersionedFrame231 (binder)
open GeneralVersionedAliasHeadWrites312 (pool)
open GeneralVersionedBinderTargets312 (actualName)
open GeneralNominalSaturationState (Alias)
variable {roles : Roles.RoleDecls}

def Owned (s : State roles) (now : Plan roles) (names : List Nat) : Prop :=
  ∀ use ∈ now.headSchema.variables, binder now use.name = actualName now use.name →
    actualName now use.name ∈ pool now names →
    ∃ producer ∈ s.plans,
      producer.packet.site.occurrence.identity = now.packet.site.occurrence.identity ∧
      producer.packet.declaration = now.packet.declaration ∧
      producer.binder use.name = actualName now use.name

theorem reused {registry : Registry} {s : State roles} {root : Occurrence roles} {now past : Plan roles}
    (checked : (boundary roles).Checked registry)
    (path : B4TargetV8.Reachable (boundary roles) registry root s)
    (stored : past ∈ s.plans)
    (alias : Alias s.core.erased.current now.packet.site.occurrence.identity past.packet.site.occurrence.identity)
    (sameRule : now.packet.declaration = past.packet.declaration)
    (owned : Owned s now names) :
    ∀ m, Models s m → GeneralVersionedBinderTable312.PrivateAgrees now past names m := by
  intro m valid use listed fallback protectedTarget
  obtain ⟨pastOwner,inside,atOwner,rule,oldBinder⟩ := owned use listed fallback protectedTarget
  obtain ⟨ctx,data⟩ := GeneralVersionedSiteOrigins312.reached path
  have relation : Alias s.core.erased.current pastOwner.input.occurrence.identity past.input.occurrence.identity := by
    rw [pastOwner.input_exact,past.input_exact,atOwner]
    exact alias
  have centers := GeneralVersionedAliasCenters312.same_alias checked path valid
    (data.input pastOwner inside) (data.input past stored) relation
  have named : use.name ∈ pastOwner.packet.declaration.inputNames := by
    rw [rule]
    exact GeneralNominalHeadSchemaNames186.head_input now use listed
  have equal := GeneralVersionedIdentityCenters312.binders_same path data pastOwner past inside stored
    (rule.trans sameRule) centers valid use.name named
  rw [oldBinder] at equal
  exact equal.2.2 _ _ (.source _) (.source _)

theorem head_table {registry : Registry} {s : State roles} {root : Occurrence roles} {now past : Plan roles}
    (checked : (boundary roles).Checked registry)
    (path : B4TargetV8.Reachable (boundary roles) registry root s)
    (frame : Frame (Compiled registry) s.core now.packet.site.occurrence now.packet.declaration.id now)
    (stored : past ∈ s.plans)
    (alias : Alias s.core.erased.current now.packet.site.occurrence.identity past.packet.site.occurrence.identity)
    (sameRule : now.packet.declaration = past.packet.declaration)
    (owned : Owned s now names) :
    GeneralVersionedHistoricalJoint312.HeadTableReady s now past names :=
  GeneralVersionedBinderTable312.certified checked path frame stored alias sameRule
    (reused checked path stored alias sameRule owned)

end Yulang.GeneralVersionedBinderReuse312
