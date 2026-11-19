import Yulang.GeneralRebaseProjectedFamily266
import Yulang.GeneralRebasePathFamilyMeaning266

namespace Yulang.GeneralRebaseProjectedFamilyMeaning266
open GeneralRebaseStep258
open GeneralRebaseCertifiedObserver266 (Edge)
open GeneralRebaseProjectedFamily266 (Route CommonTarget table provenance included)
open GeneralRebaseLiveProjection264 (SourceState project liveFacts)
open GeneralRebaseEdgeRules266 (rules)
open GeneralRebasePositiveMeaning266 (Saturated)
open GeneralRebasePathFamilyMeaning266 (Boundary Encoded)
open GeneralRebaseLiveMeaning264 (Remainder)
open GeneralNominalCenters (Plan)
open GeneralNominalCommonBridge (Assignment)
open GeneralRebaseMultiSelection263 (ofPlan)
open GeneralSourceState (Output)
variable {registry : GeneralDeclarations.Registry} {root : GeneralSourceDictionaries.Occurrence roles}

theorem final_saturated (owners : List Nat) (pool : List Output)
 (routes : List (Route registry root first)) {target : State (GeneralRebaseCompression266.Basis owners pool)}
 (common : CommonTarget owners pool routes target) : Saturated (rules owners pool (table routes)) target := by
 intro rule listed _ _
 obtain ⟨edge,member,fact,produced,rfl⟩ :=
   (GeneralRebaseEdgeRules266.member owners pool (table routes) rule).mp listed
 obtain ⟨route,there,onRoute⟩ := provenance routes edge member
 rw [←common route there]
 rw [GeneralRebaseSourceProjection264.steps_square owners pool
      (GeneralRebaseCertifiedSteps266.edge_suffix route.2 edge onRoute)]
 exact (GeneralRebaseFactSemantics259.present_write _ _ fact).mpr (Or.inl produced)

theorem rules_settle (owners : List Nat) (pool : List Output) (routes : List (Route registry root first))
 (nonempty : ∃ route, route ∈ routes) {target : State (GeneralRebaseCompression266.Basis owners pool)}
 (common : CommonTarget owners pool routes target) :
 GeneralRebaseSettle259.settle (GeneralRebasePositiveRules266.observe (rules owners pool (table routes)))
   (project owners pool first) = .ok target := by
 obtain ⟨route,listed⟩ := nonempty
 have sat := final_saturated owners pool routes common
 rw [←common route listed] at sat ⊢
 exact GeneralRebasePathRules266.settles_covered owners pool (table routes) route.2
   (included routes route listed) sat

theorem of_live_agreement (owners : List Nat) (pool : List Output)
 (routes : List (Route registry root first)) (anchor : SourceState roles)
 (agrees : ∀ route ∈ routes, ∀ fact, fact ∈ liveFacts route.1 ↔ fact ∈ liveFacts anchor) :
 CommonTarget owners pool routes (project owners pool anchor) :=
 fun route listed => GeneralRebaseLiveProjection264.project_same owners pool _ _ (agrees route listed)

/-- Both finite schedulers produce the same projected terminal value when
the supplied concrete paths have equal projected ends. The full model iff
is separate for each route and keeps its own concrete remainder explicitly.
Equal terminal projections are not asserted to imply equal full models. -/
theorem source_models (registry : GeneralDeclarations.Registry)
 (root : GeneralSourceDictionaries.Occurrence roles) (start : SourceState roles)
 (initial : (Boundary roles).Initial registry root start) :
 ∃ owners : List Nat, ∃ pool : List Output,
 ∀ (routes : List (Route (Encoded registry) root start)) (target : State (GeneralRebaseCompression266.Basis owners pool)),
 (∃ route, route ∈ routes) → CommonTarget owners pool routes target →
 GeneralRebaseSettle259.settle (GeneralRebaseCertifiedObserver266.observe owners pool (table routes))
    (project owners pool start) = .ok target ∧
 GeneralRebaseSettle259.settle (GeneralRebasePositiveRules266.observe (rules owners pool (table routes)))
    (project owners pool start) = .ok target ∧
 (∀ route ∈ routes, ∀ representative : Nat → Plan roles,
   (∀ assignment, Remainder route.1 assignment → ∀ plan ∈ route.1.plans,
     GeneralRebaseNormalizedBody263.Compatible (representative (ofPlan plan).owner) plan assignment) →
   ∀ assignment : Assignment, GeneralRebaseUniversalMeaning263.Models (Remainder route.1) owners representative
      target assignment ↔ GeneralNominalVersionedJournal232.Models route.1 assignment) := by
 obtain ⟨owners,pool,bounds⟩ := GeneralRebaseMultiSource263.source_bounds registry root start initial
 refine ⟨owners,pool,?_⟩
 intro routes target nonempty common
 refine ⟨GeneralRebaseProjectedFamily266.settles owners pool routes nonempty common,
   rules_settle owners pool routes nonempty common,?_⟩
 intro route member representative compatible assignment
 have steps : B4Target.Steps ((Boundary roles).Step registry root) start route.1 :=
   GeneralRebaseCertifiedSteps266.to_steps route.2
 have reachable : B4TargetV8.Reachable (Boundary roles) registry root route.1 := ⟨start,initial,steps⟩
 have synced := (GeneralNominalVersionedMixedPlanLedger235.reachable reachable).1
 have listed : ∀ plan ∈ route.1.plans, (ofPlan plan).owner ∈ owners := by
   intro plan inPlans
   exact (bounds route.1 steps).1 (ofPlan plan) (List.mem_map.mpr ⟨plan,inPlans,rfl⟩)
 rw [←common route member]
 exact GeneralRebaseLiveMeaning264.project_journal owners representative pool route.1 synced
   listed (bounds route.1 steps).2 compatible assignment

end Yulang.GeneralRebaseProjectedFamilyMeaning266
