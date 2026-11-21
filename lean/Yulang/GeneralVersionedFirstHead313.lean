import Yulang.GeneralVersionedBeforeFirstInstall313
import Yulang.GeneralVersionedSchemaOrigins313

set_option backward.isDefEq.respectTransparency false
/-! Automatic aggregate and private-binder certificates before the first
installation, for all arities and capture multiplicities. Requires the actual
constructor tests, not an assumed complete head assignment. -/
namespace Yulang.GeneralVersionedFirstHead313
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary Local)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralVersionedHistoryEvidence310 (Compiled)
open GeneralNominalVersionedTraceSupport237 (Reachable)
open GeneralNominalVersionedDiagnostic232 (HeadEquations)
open GeneralNominalVersionedPlans231 (HeadModels)
open GeneralNominalVersionedAggregateLedger236 (packetEntries)
open GeneralVersionedTraceDomain313 (seed)
open GeneralVersionedBeforeFirstInstall313 (source)
open GeneralVersionedHeadFromSharing313 (origins supportWithOrigins Equations BinderAfter)
open GeneralVersionedSharingBinderRows313 (Tests)
open GeneralVersionedAliasHeadWrites312 (pool)
open GeneralVersionedBinderTargets312 (actualName)
open GeneralVersionedInstallDomain313 (reserve reserve_purpose)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalState (sources)

abbrev names (s : State roles) : List Nat := sources (source s).state

theorem raw_small {s : State roles} {p : Plan roles} {id : Nat}
    (actual : Reachable registry root s) (noPlans : s.plans = [])
    (frame : Frame (Compiled registry) s.core focus key p)
    (member : id ∈ sources p.packet.context.state) : id ≤ seed s := by
  rw [frame.context_eq] at member
  exact GeneralVersionedBeforeFirstInstall313.source_slot_clean actual noPlans (List.mem_append_left _ member)

theorem origins_small {s : State roles} {p : Plan roles}
    (actual : Reachable registry root s) (noPlans : s.plans = [])
    (frame : Frame (Compiled registry) s.core focus key p) :
    ∀ n ∈ origins p, n ≤ seed s :=
  GeneralVersionedSchemaOrigins313.centers p (· ≤ seed s) (Nat.zero_le _)
    (fun i => GeneralVersionedBeforeFirstInstall313.center_small actual noPlans frame.center_recorded i)

theorem aggregate {s : State roles} {p : Plan roles}
    (actual : Reachable registry root s) (noPlans : s.plans = [])
    (frame : Frame (Compiled registry) s.core focus key p) (m : Assignment) :
    Equations p (names s) m := by
  intro entry member protectedName
  have small : entry.1 ≤ seed s := by
    rcases List.mem_append.mp protectedName with support|report
    · rcases List.mem_append.mp support with sourceName|origin
      · exact GeneralVersionedBeforeFirstInstall313.source_small actual sourceName
      · exact origins_small actual noPlans frame _ origin
    · exact raw_small actual noPlans frame (GeneralVersionedRawReportDomain313.raw_membership _ report)
  obtain ⟨name,_,_,lower|upper⟩ := (GeneralNominalVersionedAggregateRealization236.member_iff ..).mp member
  · rw [lower] at small
    have above := GeneralNominalAggregateVersion231.above_seed p.packet.context.state.seed
      p.packet.site.occurrence.identity p.packet.declaration.id 0 name p.packet.bindings
    rw [show seed s = p.packet.context.state.seed from (congrArg (fun c : GeneralNominalCandidates.Context => c.state.seed) frame.context_eq).symm] at small
    exact False.elim (Nat.not_lt_of_ge small above)
  · rw [upper] at small
    have above := GeneralNominalAggregateVersion231.above_seed p.packet.context.state.seed
      p.packet.site.occurrence.identity p.packet.declaration.id 1 name p.packet.bindings
    rw [show seed s = p.packet.context.state.seed from (congrArg (fun c : GeneralNominalCandidates.Context => c.state.seed) frame.context_eq).symm] at small
    exact False.elim (Nat.not_lt_of_ge small above)

theorem binder_outside {s : State roles} {p : Plan roles}
    (actual : Reachable registry root s) (noPlans : s.plans = [])
    (frame : Frame (Compiled registry) s.core focus key p) (name : Nat) :
    actualName p name ∉ pool p (names s) := by
  have large : seed s < actualName p name := by
    have seedEq : p.packet.context.state.seed = seed s := congrArg (fun x : GeneralNominalCandidates.Context => x.state.seed) frame.context_eq
    rw [← seedEq]
    exact GeneralNominalIdentities.source_above_seed _ _
  intro present
  have notSmall (small : actualName p name ≤ seed s) : False := Nat.not_lt_of_ge small large
  simp only [pool,List.mem_append] at present
  rcases present with ((sourceName|head)|tests)|vars
  · exact notSmall (GeneralVersionedBeforeFirstInstall313.source_small actual sourceName)
  · rcases List.mem_append.mp head with atom|report
    · have visible : p.packet.declaration ∈ p.packet.registry.declarations := by
        rw [frame.registry_eq]; exact frame.visible
      rcases List.mem_append.mp (GeneralVersionedInstallDomain313.head_sources p.packet visible atom) with old|added
      · exact notSmall (raw_small actual noPlans frame old)
      · have po := reserve_purpose p.packet added
        change 8 ≤ 6 at po
        omega
    · exact notSmall (raw_small actual noPlans frame (GeneralVersionedRawReportDomain313.raw_membership _ report))
  · exact notSmall (origins_small actual noPlans frame _ (List.mem_append_left _ tests))
  · exact notSmall (origins_small actual noPlans frame _ (List.mem_append_right _ vars))

theorem initial_head {s : State roles} {p : Plan roles}
    (checked : (boundary roles).Checked registry)
    (actual : Reachable registry root s) (noPlans : s.plans = [])
    (picked : Local registry s focus (.selected key kids))
    (frame : Frame (Compiled registry) s.core focus key p)
    (nonempty : ∃ m, Models s m)
    (tests : ∀ m, Models s m → GeneralDictionaryHeadSharing220.Holds p m → Tests p m) :
    ∃ m, Models s m ∧ HeadEquations p m := by
  apply GeneralVersionedHeadFromSharing313.selected_head checked actual picked frame nonempty
    (GeneralVersionedBeforeFirstInstall313.support_initial actual noPlans)
  intro m valid shared
  refine ⟨tests m valid shared,aggregate actual noPlans frame m,?_⟩
  intro _ use present eq protectedBinder
  exact False.elim (binder_outside actual noPlans frame use.name protectedBinder)

theorem structural_free {s : State roles} {p : Plan roles}
    (checked : (boundary roles).Checked registry)
    (actual : Reachable registry root s) (noPlans : s.plans = [])
    (picked : Local registry s focus (.selected key kids))
    (frame : Frame (Compiled registry) s.core focus key p) (nonempty : ∃ m, Models s m)
    (noTests : p.headSchema.tests = []) :
    ∃ m, Models s m ∧ HeadEquations p m := by
  refine initial_head checked actual noPlans picked frame nonempty ?_
  intro m _ _ test present
  rw [noTests] at present
  cases present

end Yulang.GeneralVersionedFirstHead313
