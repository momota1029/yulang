import Yulang.GeneralMixedCompoundPointRoot307

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 19000
set_option maxHeartbeats 9500000
namespace Yulang.GeneralMixedCompoundPointChild307
open GeneralDictionaryJournalRefinement228Source (roles)
open GeneralDictionaryCompoundSource238 (registry declaration)
open GeneralDictionaryCompoundSites238 (childSite)
open GeneralDictionaryCompoundBase239 (lo hi)
open GeneralMixedCompoundPointSpine307 (spine nominal_location)
open GeneralMixedCompoundRefreshBound307 (Run)
open GeneralNominalVersionedJournal232 (State Effect)
open GeneralNominalVersionedMixedKernel234 (Installable)
open GeneralNominalVersionedCandidates231 (Prepared inputs)
open GeneralNominalCenters (Plan)
open GeneralNominalRecursiveCandidates (arguments report Context)
open GeneralNominalRecursiveInspection
open GeneralNominalState (Known RootPending)
open GeneralDictionaryBinderLocations (sourceSlot sourceSlot_exact)

variable {s : State roles}

theorem no_nominal (p : Run n s) (i : Fin s.core.erased.current.context.state.base.slots)
    (atLo : s.core.erased.current.context.state.base.source i = lo) :
    s.core.erased.current.context.state.nominals i = none := by
  cases h : s.core.erased.current.context.state.nominals i with
  | none => rfl
  | some d =>
    have kindAt := nominal_location p i d h
    rw [atLo] at kindAt
    exact False.elim ((by decide +kernel : ¬ (lo = 0 ∨ lo = 1)) kindAt)

theorem known_of_enabled (e : Effect roles) (enable : Installable registry s e)
    (focus : e.plan.packet.site.occurrence = childSite.occurrence) :
    Known s.core.erased.current.context.state lo := by
  classical
  apply Classical.byContradiction
  intro unknown
  have safe := enable.safe.1
  rw [focus] at safe
  apply safe
  refine ⟨(0 : Fin 1),?_⟩
  change ¬ Known s.core.erased.current.context.state lo
  exact unknown

theorem no_prepared (p : Run n s) :
    ¬ Prepared registry s.core.erased.current.context childSite.occurrence declaration := by
  obtain ⟨coords⟩ := spine p
  let ctx := s.core.erased.current.context
  rintro ⟨_,_,bounds,located,_,done,_⟩
  change GeneralCandidateBoundaryParts.locate ctx.state.base [(lo,hi)] = some bounds at located
  rw [GeneralDictionaryRefinedLocations.locate_cons] at located
  cases low : sourceSlot ctx.state.base lo with
  | none => simp [low] at located
  | some i =>
    cases high : sourceSlot ctx.state.base hi with
    | none => simp [low,high] at located
    | some j =>
      have atLo := (sourceSlot_exact ctx.state.base lo i).mp low
      have withoutNominal := no_nominal p i atLo
      change ctx.state.nominals i = none at withoutNominal
      have boundsEq : bounds = [(i,j)] := by
        simpa [low,high,GeneralCandidateBoundaryParts.locate] using located.symm
      subst bounds
      change Finished (report ctx declaration [(i,j)]) at done
      unfold report at done
      rw [GeneralMixedCompoundPointRoot307.query ctx coords] at done
      cases seen : ctx.state.view.heads i with
      | scalar base =>
        have bad := done.2.1
        simp [inspectMany,inspect,Report.append,Report.visit,withoutNominal,seen] at bad
      | structural kind children =>
        have bad := done.2.1
        simp [inspectMany,inspect,Report.append,Report.visit,withoutNominal,seen] at bad
      | deferred why =>
        have bad := done.1
        simp [inspectMany,inspect,Report.append,Report.visit,withoutNominal,seen,block] at bad

theorem no_frame (p : Run n s) (plan : Plan roles) :
    ¬ GeneralNominalVersionedEvidence231.Frame registry s.core childSite.occurrence key plan := by
  intro f
  have decl : plan.packet.declaration = declaration := List.mem_singleton.mp f.visible
  have prep := f.prepared
  rw [decl] at prep
  exact no_prepared p prep

theorem no_install (p : Run n s) (e : Effect roles) (enabled : Installable registry s e)
    (childFocus : e.plan.packet.site.occurrence = childSite.occurrence) : False := by
  have frame := e.frame
  rw [enabled.registry_eq,enabled.snapshot_eq,childFocus] at frame
  exact no_frame p e.plan frame

end Yulang.GeneralMixedCompoundPointChild307
