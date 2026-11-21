import Yulang.GeneralVersionedRawReportDomain313
import Yulang.GeneralVersionedUnseenOwnerCenters313

set_option backward.isDefEq.respectTransparency false
/-! For a never-installed numerical owner, a private binder cannot be
protected by its prospective head inspection or actual origins. Only
membership in the chosen live-model support can still protect it. -/
namespace Yulang.GeneralVersionedUnseenBinder313
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedTraceSupport237 (Reachable)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralVersionedTraceDomain313 (seed context raw)
open GeneralVersionedBinderTargets312 (actualName)
open GeneralVersionedAliasHeadWrites312 (pool)
open GeneralVersionedHeadFromSharing313 (origins)
open GeneralNominalVersionedResidualFrame237 (headSources)
open GeneralVersionedInstallDomain313 (reserve_purpose)
open GeneralNominalIdentities (source)

def Unseen (s : State roles) (p : Plan roles) : Prop :=
  ∀ prior ∈ s.plans, prior.packet.site.occurrence.identity ≠ p.packet.site.occurrence.identity

theorem raw_absent {s : State roles} {p : Plan roles}
    (actual : Reachable registry root s) (aligned : p.packet.context = context s)
    (absent : Unseen s p) (name : Nat) :
    actualName p name ∉ GeneralNominalState.sources p.packet.context.state := by
  let key := GeneralNominalAllocation.origin p.packet.site.occurrence.identity p.packet.declaration.id 8 name 0
  have id : actualName p name = source (seed s) key := by
    change source p.packet.context.state.seed key = _
    rw [aligned]
  intro member
  rw [aligned,id] at member
  exact GeneralVersionedTraceDomain313.no_owner (k := key) actual absent (List.mem_append_left _ member)

theorem head_absent {s : State roles} {p : Plan roles}
    (actual : Reachable registry root s) (aligned : p.packet.context = context s)
    (visible : p.packet.declaration ∈ p.packet.registry.declarations)
    (absent : Unseen s p) (name : Nat) :
    actualName p name ∉ headSources p.packet := by
  intro member
  rcases List.mem_append.mp member with old|report
  · rcases List.mem_append.mp (GeneralVersionedInstallDomain313.head_sources p.packet visible old) with live|reserved
    · exact raw_absent actual aligned absent name live
    · have tag := reserve_purpose p.packet reserved
      change 8 ≤ 6 at tag
      omega
  · exact raw_absent actual aligned absent name (GeneralVersionedRawReportDomain313.raw_membership _ report)

theorem origins_absent {s : State roles} {p : Plan roles}
    (actual : Reachable registry root s) (aligned : p.packet.context = context s)
    (registered : p.input ∈ s.core.sites) (absent : Unseen s p) (name : Nat) :
    actualName p name ∉ origins p := by
  let key := GeneralNominalAllocation.origin p.packet.site.occurrence.identity p.packet.declaration.id 8 name 0
  have id : actualName p name = source (seed s) key := by
    change source p.packet.context.state.seed key = _
    rw [aligned]
  rw [id]
  exact GeneralVersionedUnseenOwnerCenters313.head_origins_unowned actual absent registered

theorem protected_iff {s : State roles} {p : Plan roles}
    (actual : Reachable registry root s) (frame : Frame compiled s.core focus key p)
    (absent : Unseen s p) (names : List Nat) (name : Nat) :
    actualName p name ∈ pool p names ↔ actualName p name ∈ names := by
  have visible : p.packet.declaration ∈ p.packet.registry.declarations := frame.registry_eq ▸ frame.visible
  simp only [pool,List.mem_append]
  constructor
  · rintro (((semantic|head)|test)|origin)
    · exact semantic
    · exact False.elim (head_absent actual frame.context_eq visible absent name head)
    · exact False.elim (origins_absent actual frame.context_eq frame.center_recorded absent name (List.mem_append_left _ test))
    · exact False.elim (origins_absent actual frame.context_eq frame.center_recorded absent name (List.mem_append_right _ origin))
  · exact fun h => .inl (.inl (.inl h))

end Yulang.GeneralVersionedUnseenBinder313
