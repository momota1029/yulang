import Yulang.GeneralDeclarativeHybridTrace345
import Yulang.GeneralDeclarativePhysicalReplay344
import Yulang.GeneralDeclarativeRevalidate344

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 26000
set_option maxHeartbeats 24000000
namespace Yulang.GeneralDeclarativeHybridPhysical345
open GeneralDictionaryJournalRefinement228Source (roles root context labels snapshot ground root_point initial_source)
open GeneralWhereOriginSingleSource318 (sourceRegistry oldPlan boundary_checked)
open GeneralWherePhysicalOldHead319 (start before)
open GeneralWherePhysicalOldInstall319 (installed)
open GeneralWherePhysicalPast319 (looseCtx)
open GeneralWherePhysicalReobserve319 (updated)
open GeneralWherePhysicalActive319 (ctx)
open GeneralWherePhysicalCurrentRead319 (plan)
open GeneralWherePhysicalCommit319 (final physical_mixed_run)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalCenteredHeadMatStepJournal (initial)
open GeneralDeclarativeHybridTrace345 (Walk from_reach along)
open GeneralNominalCenteredHeadMatEffects (Ready)
open GeneralNominalCenteredHeadDefaultSchemas (RequestsDeclared)
open GeneralWhereOriginSupport318 (journalSources)
open GeneralDeclarativeCommitPackage344 (Witness)

theorem covered : GeneralNominalCenteredHeadWFSource.Coverage sourceRegistry context.interpretation := by
  constructor
  · intro d member
    rcases List.mem_cons.mp member with h|rest
    · cases h
      simp [GeneralNominalCenteredHeadWFSource.DeclarationCovered,
        GeneralNominalCenteredHeadWFSource.PatternsCovered,GeneralNominalCenteredHeadWFSource.PatternCovered,
        GeneralNominalCenteredHeadWFSource.ConstructorUse,GeneralDictionaryJournalRefinement228Source.interpretation,
        GeneralDictionaryJournalRefinement228Source.constructors,GeneralDictionaryOptionalExpression229.pattern]
      exact ⟨rfl,rfl,rfl⟩
    · cases List.mem_singleton.mp rest
      exact GeneralLiveCompoundRegistry316.coverage.1 _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · exact GeneralDictionaryCompoundSource238.coverage.2

theorem reached : B4TargetV8.Reachable (boundary roles) sourceRegistry root before.mixed := by
  refine ⟨start,⟨initial context root,⟨context,labels,initial_source sourceRegistry rfl rfl,root_point,ground,covered,rfl⟩,rfl⟩,.refl⟩

theorem both_ready :
    RequestsDeclared installed.mixed.core root oldPlan ∧ Ready installed.mixed.core root oldPlan ∧
    RequestsDeclared final.mixed.core root plan ∧ Ready final.mixed.core root plan := by
  obtain ⟨stepA,reobserve,stepB,_⟩ := physical_mixed_run
  have base := from_reach boundary_checked reached
  have route : Walk sourceRegistry root before updated := .native (.isolated .refl stepA) reobserve
  have tracked := along boundary_checked base route
  obtain ⟨declA,readyA⟩ := GeneralDeclarativeCurrentReady345.after_ready base.origin base.coverage
    stepA (by rfl : installed.versionedWhere[before.versionedWhere.length]? = some oldPlan)
  obtain ⟨declB,readyB⟩ := GeneralDeclarativeCurrentReady345.after_ready tracked.origin tracked.coverage
    stepB (by rfl : final.versionedWhere[updated.versionedWhere.length]? = some plan)
  exact ⟨declA,readyA,declB,readyB⟩

theorem replay_one_model :
    ∃ prepA viewA portsA whereA rootA m mid prepB viewB portsB whereB rootB n,
      Witness installed oldPlan m n (journalSources final ++ [4]) prepA viewA portsA whereA rootA ∧
      Witness final plan mid n ((journalSources installed ++ GeneralDeclarativeFootprint321.stateNames viewA) ++ [4])
        prepB viewB portsB whereB rootB ∧ n 4 = m 4 := by
  obtain ⟨stepA,_,stepB,modelA,_,modelB,_,_⟩ := physical_mixed_run
  obtain ⟨prepA,viewA,portsA,whereA,rootA,mid,prepB,viewB,portsB,whereB,rootB,n,a,b,kept⟩ :=
    GeneralDeclarativeRevalidate344.together sourceRegistry before updated looseCtx ctx oldPlan plan
      stepA stepB _ modelA modelB both_ready.2.1 both_ready.2.2.2 [4]
  exact ⟨prepA,viewA,portsA,whereA,rootA,_,mid,prepB,viewB,portsB,whereB,rootB,n,a,b,kept _ List.mem_cons_self⟩

end Yulang.GeneralDeclarativeHybridPhysical345
