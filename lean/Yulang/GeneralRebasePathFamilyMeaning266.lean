import Yulang.GeneralRebasePathFamilyRules266
import Yulang.GeneralRebaseLiveMeaning264

namespace Yulang.GeneralRebasePathFamilyMeaning266
open GeneralRebaseStep258
open GeneralRebaseCertifiedPath266 (Path)
open GeneralRebaseLiveProjection264 (SourceState project)
open GeneralRebasePathFamily266 (table)
open GeneralRebaseLiveMeaning264 (Remainder)
open GeneralNominalCenters (Plan)
open GeneralNominalCommonBridge (Assignment)
open GeneralRebaseMultiSelection263 (ofPlan)
open GeneralSourceState (Output)
abbrev Boundary (roles : Roles.RoleDecls) := GeneralNominalVersionedMixedSourceBoundary234.boundary roles
abbrev Encoded (registry : GeneralDeclarations.Registry) := GeneralNominalCenteredHeadAllocEncoding.registry registry

/-- One source-derived basis suffices for every certified family starting at
this actual initial source. Exact model readback retains the final journal
remainder and explicitly assumes owner-representative compatibility there. -/
theorem source_family_meaning (registry : GeneralDeclarations.Registry)
 (root : GeneralSourceDictionaries.Occurrence roles) (start : SourceState roles)
 (initial : (Boundary roles).Initial registry root start) :
 ∃ owners : List Nat, ∃ pool : List Output, ∀ last,
 ∀ paths : List (Path (Encoded registry) root start last), (∃ path, path ∈ paths) →
 ∀ representative : Nat → Plan roles,
 (∀ assignment, Remainder last assignment → ∀ plan ∈ last.plans,
   GeneralRebaseNormalizedBody263.Compatible (representative (ofPlan plan).owner) plan assignment) →
 ∃ result,
 GeneralRebaseSettle259.settle (GeneralRebaseCertifiedObserver266.observe owners pool (table paths))
    (project owners pool start) = .ok result ∧
 GeneralRebaseSettle259.settle (GeneralRebasePositiveRules266.observe (GeneralRebaseEdgeRules266.rules owners pool (table paths)))
    (project owners pool start) = .ok result ∧
 (∀ assignment : Assignment, GeneralRebaseUniversalMeaning263.Models (Remainder last) owners representative
     result assignment ↔ GeneralNominalVersionedJournal232.Models last assignment) := by
 obtain ⟨owners,pool,bounds⟩ := GeneralRebaseMultiSource263.source_bounds registry root start initial
 refine ⟨owners,pool,?_⟩
 intro last paths nonempty representative compatible
 obtain ⟨path,member⟩ := nonempty
 have steps : B4Target.Steps ((Boundary roles).Step registry root) start last :=
   GeneralRebaseCertifiedSteps266.to_steps path
 have reachable : B4TargetV8.Reachable (Boundary roles) registry root last := ⟨start,initial,steps⟩
 have synced := (GeneralNominalVersionedMixedPlanLedger235.reachable reachable).1
 have listed : ∀ plan ∈ last.plans, (ofPlan plan).owner ∈ owners := by
   intro plan inPlans
   exact (bounds last steps).1 (ofPlan plan) (List.mem_map.mpr ⟨plan,inPlans,rfl⟩)
 refine ⟨project owners pool last,GeneralRebasePathFamily266.settles owners pool paths ⟨path,member⟩,
   GeneralRebasePathFamilyRules266.settles owners pool paths ⟨path,member⟩,?_⟩
 exact GeneralRebaseLiveMeaning264.project_journal owners representative pool last synced
   listed (bounds last steps).2 compatible

end Yulang.GeneralRebasePathFamilyMeaning266
