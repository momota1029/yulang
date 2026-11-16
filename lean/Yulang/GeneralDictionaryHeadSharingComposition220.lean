import Yulang.GeneralDictionaryHeadSharingSoundness220
import Yulang.GeneralDictionaryHeadSharingLaws220

set_option backward.isDefEq.respectTransparency false
/-! The unchanged full B4 Statement is conditional only on EvidenceNode.
General GeneratedChildren and FreshCompletion are not required by this route. -/
namespace Yulang.GeneralDictionaryHeadSharingComposition220
open GeneralDeclarations GeneralSourceDictionaries CommonRoleOutermostResolver
open GeneralNominalCenteredHeadMatStepJournal (State)
open B4TargetV8
open B4SkeletonV8 (steps_models)
open B4TargetV3 (same_diagnostic_refl)
variable {roles : Roles.RoleDecls}

theorem composition
    (node : B4SkeletonV8.EvidenceNode (GeneralDictionaryHeadSharingBoundary220.boundary roles)) :
    B4TargetV8.Statement (GeneralDictionaryHeadSharingBoundary220.boundary roles)
      (GeneralDictionaryHeadSharingExecutor220.executor roles) := by
  let b := GeneralDictionaryHeadSharingBoundary220.boundary roles
  let e := GeneralDictionaryHeadSharingExecutor220.executor roles
  let frontiers := GeneralDictionaryHeadSharingExecutor220.frontiers roles
  have laws := GeneralDictionaryHeadSharingLaws220.twelveLaws roles

  have exact (r : Registry) (checked : b.Checked r) (s : State roles)
      (root : Occurrence roles) (reachable : Reachable b r root s) :
      FrontierExact (frontiers r s) := by
    intro d f
    rw [laws.localIdentity r s root reachable]
    exact laws.frontierLocal r checked s root reachable d f
  have accessible (r : Registry) (checked : b.Checked r) (s : State roles)
      (root : Occurrence roles) (reachable : Reachable b r root s) :
      Acc (Child (frontiers r s).Local) root := by
    rw [laws.localIdentity r s root reachable]
    exact laws.whereAccessible r checked s root reachable
  have finalReach (r : Registry) (checked : b.Checked r) (s : State roles)
      (d : Occurrence roles) (reachable : Reachable b r d s) : Reachable b r d (e.run r s d).1 :=
    B4TargetV5.reachable_steps (prior b) reachable (laws.execution r checked s d reachable)
  have exactTree : Exact b e := by
    intro r checked s d tree initial
    have reachable := B4TargetV5.reachable_initial (prior b) initial
    have final := finalReach r checked s d reachable
    rw [laws.treeExecution r checked s d reachable
      (exact r checked _ d final) (accessible r checked _ d final)]
    have rule := resolve_tree_exact_of_frontier_exact (frontiers r (e.run r s d).1)
      (exact r checked _ d final) d (accessible r checked _ d final) tree
    simpa only [frontiers,e,b,laws.localIdentity r _ d final] using rule
  refine ⟨?_, exactTree, ?_, ?_, ?_⟩
  · intro r checked s d initial
    have reachable := B4TargetV5.reachable_initial (prior b) initial
    obtain ⟨stable, generated⟩ := laws.closure r checked _ d
      (finalReach r checked s d reachable) (laws.halted r checked s d reachable)
    exact ⟨laws.progress r checked s d reachable, laws.execution r checked s d reachable,
      stable, generated, steps_models b r d (laws.stepModels r checked d)
        reachable (laws.execution r checked s d reachable)⟩
  · intro r r' checked checked' order s d initial
    have initial' := laws.initialReorders r r' order d s initial
    have resolved := (exactTree r checked s d _ initial).mp rfl
    have transported := B4Skeleton.resolves_transport
      (fun q f h => (laws.canonicalLocalOrder r r' checked checked' order s d
        (B4TargetV5.reachable_initial (prior b) initial) (B4TargetV5.reachable_initial (prior b) initial') q f).mp h) resolved
    have same := (exactTree r' checked' s d _ initial').mpr transported
    rw [same]
    exact same_diagnostic_refl (base b) laws.dictionaryRefl _
  · exact GeneralDictionaryHeadSharingSoundness220.dictionarySound node
  · intro r checked s d initial returned
    have resolved := (exactTree r checked s d .rejected initial).mp returned
    cases resolved with
    | rejected localRule => exact (B4TargetV8.rejected_iff.mp localRule)

end Yulang.GeneralDictionaryHeadSharingComposition220
