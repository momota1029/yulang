import Yulang.GeneralMixedCompoundPointCommit308

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 22000
set_option maxHeartbeats 13500000
namespace Yulang.GeneralMixedCompoundPointSteps308
open GeneralDictionaryJournalRefinement228Source (roles root)
open GeneralDictionaryCompoundSource238 (registry)
open GeneralDictionaryCompoundSites238 (childSite)
open GeneralMixedCompoundPointView308 (snap)
open GeneralMixedCompoundPointViewTrust308 (observed)
open GeneralMixedCompoundPointSites308 (raw_sites)
open GeneralMixedCompoundPointAdmin308 (merge_already)
open GeneralMixedCompoundPointCommit308 (no_install reached_cases)
open GeneralNominalVersionedMixedKernel234 (Step Equal)
open GeneralNominalVersionedMixedObservations233 (Refresh)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralNominalVersionedAdministrative232 (equate)
open GeneralNominalState (Known sources)
open GeneralNominalFeedbackSteps (RawEqual)
open GeneralNominalVersionedJournal232 (State)

theorem point_closed : GeneralNominalReobservationSteps.PointClosed snap := by
  intro idx d recorded
  have same : d = GeneralMixedCompoundUpperSnapshot307.desc := by
    change (if idx = 0 ∨ idx = 1 then some GeneralMixedCompoundUpperSnapshot307.desc else none) = some d at recorded
    split at recorded
    · exact (Option.some.inj recorded).symm
    · cases recorded
  subst d
  intro parameter contained
  change parameter ∈ [.type ((2 : Fin 8),2),.type (2,2)] at contained
  rcases List.mem_cons.mp contained with rfl|rest
  · rfl
  · cases List.mem_singleton.mp rest; rfl

def StrictRefreshTo (t : State roles) : Prop :=
  ∃ (context : GeneralNominalCandidates.Context) (_ : Refresh observed context) (id : Nat),
    id ∈ sources snap ∧ ¬ Known snap id ∧ Known context.state id ∧ t = refresh observed context

def NovelEqualityTo (t : State roles) : Prop :=
  ∃ a b, a ∈ sources snap ∧ b ∈ sources snap ∧ Equal observed a b ∧
    ¬ RawEqual observed.core.erased.current a b ∧ t = equate observed a b

theorem exact_operations (t : State roles) :
    Step registry root observed t ↔ StrictRefreshTo t ∨ NovelEqualityTo t := by
  constructor
  · rintro ⟨focus,generated,op⟩
    cases op with
    | administrative act =>
      cases act with
      | enqueue linked absent =>
        rcases reached_cases generated with rfl|rfl
        · exact False.elim (absent _ (raw_sites ▸ List.mem_cons_self) rfl)
        · exact False.elim (absent _ (raw_sites ▸ List.mem_cons_of_mem _ (List.mem_singleton_self _)) rfl)
      | refresh context cert id support old new => exact Or.inl ⟨context,cert,id,support,old,new,rfl⟩
      | equate a b one two same novel => exact Or.inr ⟨a,b,one,two,same,novel,rfl⟩
      | reobserve rev _ improves =>
        exact False.elim (GeneralNominalReobservationSteps.pointClosed_no_revision point_closed rev improves)
    | refresh _ context cert id support old new => exact Or.inl ⟨context,cert,id,support,old,new,rfl⟩
    | install e enabled novel => exact False.elim (novel (no_install e generated enabled))
    | merge a b one two same fresh => exact False.elim (fresh (merge_already one two same))
  · rintro (⟨context,cert,id,support,old,new,rfl⟩ | ⟨a,b,one,two,same,novel,rfl⟩)
    · exact ⟨root,.root,.refresh root context cert id support old new⟩
    · exact ⟨root,.root,.administrative (.equate root a b one two same novel)⟩

end Yulang.GeneralMixedCompoundPointSteps308
