import Yulang.GeneralRebaseCompactAvailability279
import Yulang.GeneralRebaseCompiledEvidenceAt277

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 9800000
namespace Yulang.GeneralRebaseCompactEvidenceAt279
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralRebaseCompactEdgeInstall279
open GeneralRebaseCompactAvailability279 (SameEdges stable_iff)
open GeneralRebaseInstallNovelty279 (Edge)
open GeneralNominalCenteredHeadAllocEncoding (registry)
open B4SkeletonV8 (EvidenceAt)

variable {roles : Roles.RoleDecls} {state : State roles} {new : List (Edge roles)}
variable {r : Registry} {root : Occurrence roles}

private theorem all₂_mono {α β : Type} {p q : α → β → Prop}
    (imp : ∀ a b, p a b → q a b) {xs ys} (h : CommonRoleOutermostResolver.All₂ p xs ys) :
    CommonRoleOutermostResolver.All₂ q xs ys := by
  induction h with
  | nil => exact .nil
  | cons one _ ih => exact .cons (imp _ _ one) ih

theorem iff_of_membership (same : SameEdges state new) :
    EvidenceAt (boundary roles) r (replaceEdges state new) root ↔
      EvidenceAt (boundary roles) r state root := by
  have stable (goal : Occurrence roles) :
      (boundary roles).Stable r (replaceEdges state new) goal ↔
        (boundary roles).Stable r state goal := stable_iff same
  have evidence m (goal : Occurrence roles) data :
      (boundary roles).Evidence r (replaceEdges state new) m goal data ↔
        (boundary roles).Evidence r state m goal data :=
    evidence_exact state new (registry r) goal m data
  have reached (d : Occurrence roles) :
      (boundary roles).Generated r (replaceEdges state new) root d ↔
        (boundary roles).Generated r state root d := generated_exact state new same root d
  constructor
  · intro holds model valid goal key children payload linked stableGoal stableKids selected kids
    apply (evidence model goal _).mp
    apply holds model ((models_exact state new model).mpr valid) goal key children payload
    · exact linked.imp id (reached goal).mpr
    · exact (stable goal).mpr stableGoal
    · exact fun child member => (stable child).mpr (stableKids child member)
    · exact (GeneralRebaseCompactLocal279.adapter _).mpr selected
    · exact all₂_mono (fun c p h => (evidence model c p).mpr h) kids
  · intro holds model valid goal key children payload linked stableGoal stableKids selected kids
    apply (evidence model goal _).mpr
    apply holds model ((models_exact state new model).mp valid) goal key children payload
    · exact linked.imp id (reached goal).mp
    · exact (stable goal).mp stableGoal
    · exact fun child member => (stable child).mp (stableKids child member)
    · exact (GeneralRebaseCompactLocal279.adapter _).mp selected
    · exact all₂_mono (fun c p h => (evidence model c p).mp h) kids

theorem reduced_iff (start : State roles) (effect : GeneralNominalVersionedJournal232.Effect roles) :
    EvidenceAt (boundary roles) r (reduced start effect) root ↔
      EvidenceAt (boundary roles) r (GeneralNominalVersionedInstall232.install start effect) root :=
  iff_of_membership (reduced_membership start effect)

theorem compiled_display :
    EvidenceAt (boundary GeneralDeclarationExamples.roles) GeneralNominalExamples.registry
      (reduced GeneralRebaseDisplayFrame276.before GeneralRebaseCompiledDisplay277.effect)
      GeneralNominalExamples.displayRoot :=
  (reduced_iff _ _).mpr GeneralRebaseCompiledEvidenceAt277.evidenceAt

end Yulang.GeneralRebaseCompactEvidenceAt279
