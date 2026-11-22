import Yulang.GeneralDeclarativeCurrentGuard345

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000
set_option maxHeartbeats 12000000
namespace Yulang.GeneralDeclarativeCurrentCandidate345
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalCenters (Plan)
open GeneralNominalVersionedJournal232 (State Effect Models)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalCenteredHeadAllocEncoding (registry)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedCandidates231 (Unique)
open GeneralNominalVersionedMixedKernel234 (Installable)
open GeneralNominalCenteredHeadMatEffects (Ready)
open GeneralNominalVersionedFrame231 (children)
open GeneralNominalCommonBridge (Assignment)

def proposal {r : Registry} {root : Occurrence rs} {state : State rs} {p : Plan rs}
    (checked : (boundary rs).Checked r)
    (reached : B4TargetV8.Reachable (boundary rs) r root state)
    (frame : Frame (registry r) state.core p.packet.site.occurrence p.packet.declaration.id p)
    (unique : Unique (registry r) state.core.erased.current.context
      p.packet.site.occurrence p.packet.declaration.id (children p.packet)) : Effect rs :=
  ⟨registry r,state.core,p,frame,unique,GeneralNominalVersionedMixedReady235.ready checked reached frame⟩

/-- A checked reached frame already permits a real proposal record,
without consulting the old declarative classifier. This establishes
neither its actual raw installability nor an independent latest
witness-backed selection. -/
theorem exact_proposal {r : Registry} {root : Occurrence rs} {state : State rs} {p : Plan rs}
    (checked : (boundary rs).Checked r)
    (reached : B4TargetV8.Reachable (boundary rs) r root state)
    (frame : Frame (registry r) state.core p.packet.site.occurrence p.packet.declaration.id p)
    (unique : Unique (registry r) state.core.erased.current.context
      p.packet.site.occurrence p.packet.declaration.id (children p.packet)) :
    ∃ e : Effect rs, e.plan = p ∧ e.snapshot = state.core ∧ e.registry = registry r ∧
      Ready state.core p.packet.site.occurrence p := by
  exact ⟨proposal checked reached frame unique,rfl,rfl,rfl,
    GeneralNominalVersionedMixedReady235.ready checked reached frame⟩

open GeneralDictionaryJournalRefinement228Source (roles root)
open GeneralLiveCompoundRegistry316 (sourceRegistry boundary_checked)
open GeneralLiveCompoundLeafInstall316 (after reachable)
open GeneralLiveCompoundPostFrames316 (rootPlan)
open GeneralLiveCompoundPostRootHead316 (frame unique root_children)
open GeneralLiveCompoundLeafProof316 (w)
open GeneralLiveCompoundPostRootSelect316 (classes)

noncomputable def rejectedPacket : Effect roles :=
  proposal boundary_checked reachable (frame.occurrence_eq.symm ▸ frame)
    (by
      rw [frame.occurrence_eq,root_children,frame.key_eq]
      exact unique)

theorem actual_cut :
    rejectedPacket.plan = rootPlan ∧
    Ready after.core root rootPlan ∧
    GeneralNominalCycleSteps.ChoiceCompatible after.core.erased.current rootPlan.packet ∧
    GeneralNominalVersionedEffects231.ClassEffects after.core root rootPlan w ∧
    ¬ Installable (registry sourceRegistry) after rejectedPacket := by
  exact ⟨rfl,GeneralDeclarativeCurrentBarrier345.ready.2,
    GeneralLiveCompoundProposedRepair316.choice_compatible,classes,
    GeneralDeclarativeCurrentGuard345.no_installable (by rfl)⟩

end Yulang.GeneralDeclarativeCurrentCandidate345
