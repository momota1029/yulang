import Yulang.GeneralMixedCompoundTailEq307
import Yulang.GeneralDictionaryCompoundVacuity239
import Yulang.GeneralFiniteRawPresentation306

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 21000
set_option maxHeartbeats 11000000
namespace Yulang.GeneralMixedCompoundTail307
open GeneralDictionaryJournalRefinement228Source (roles root snapshot)
open GeneralDictionaryCompoundSource238 (registry sourceRegistry)
open GeneralDictionaryCompoundSites238 (childSite)
open GeneralDictionaryCompoundRefresh239 (refreshed)
open GeneralDictionaryCompoundSnapshot239 (extendedSnapshot)
open GeneralMixedCompoundUpperBase307 (upper)
open GeneralMixedCompoundUpperRefresh307 (upperState models_iff step)
open GeneralMixedCompoundUpperHalt307 (raw_sites centers no_merge_forward no_merge_backward)
open GeneralNominalVersionedMixedObservations233 (Refresh refresh_models)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralNominalVersionedJournal232 (State Models Effect)
open GeneralNominalVersionedMixedKernel234 (Step Installable)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalRecursiveCandidates (Context)
open GeneralNominalSaturationState (Generated)
open GeneralNominalCenters (Site SameInputs rootSite)
open GeneralNominalState (Known)

def AtTail (s : State roles) : Prop :=
  s = refreshed ∨ ∃ ctx : Context, Nonempty (Refresh refreshed ctx) ∧ Known ctx.state upper ∧ s = refresh refreshed ctx

theorem registered {s : State roles}
    (reached : B4TargetV8.Reachable (boundary roles) sourceRegistry root s)
    (sites : s.core.erased.current.sites = [GeneralNominalDemandMerging.pointSite root,childSite.observed])
    {focus : GeneralSourceDictionaries.Occurrence roles}
    (gen : Generated s.core.erased.current root focus) :
    focus = root ∨ focus = childSite.occurrence := by
  obtain ⟨raw,present,eq⟩ := GeneralNominalVersionedMixedTrace235.generated_registered
    (GeneralNominalVersionedMixedTrace235.reachable reached).1 gen
  rw [sites] at present
  rcases List.mem_cons.mp present with side|last
  · subst raw; exact Or.inl eq.symm
  · cases List.mem_singleton.mp last; exact Or.inr eq.symm

theorem no_merge {s : State roles} (equal : Models s = Models upperState)
    (listed : s.core.sites = [rootSite snapshot.seed root,childSite])
    {a b : Site roles} (one : a ∈ s.core.sites) (two : b ∈ s.core.sites)
    (same : SameInputs (Models s) a b) :
    GeneralNominalSaturationState.Alias s.core.erased.current a.occurrence.identity b.occurrence.identity := by
  rw [equal] at same
  rw [listed] at one two
  rcases List.mem_cons.mp one with rfl|first <;> rcases List.mem_cons.mp two with rfl|last
  · exact .refl _
  · cases List.mem_singleton.mp last; exact False.elim (no_merge_forward same)
  · cases List.mem_singleton.mp first; exact False.elim (no_merge_backward same)
  · cases List.mem_singleton.mp first; cases List.mem_singleton.mp last; exact .refl _

theorem raw_not_novel {s : State roles}
    (sites : s.core.erased.current.sites = [GeneralNominalDemandMerging.pointSite root,childSite.observed])
    {focus : GeneralSourceDictionaries.Occurrence roles}
    (which : focus = root ∨ focus = childSite.occurrence) :
    ∃ recorded ∈ s.core.erased.current.sites, recorded.occurrence = focus := by
  rcases which with rfl|rfl
  · exact ⟨_,sites ▸ List.mem_cons_self ..,rfl⟩
  · exact ⟨_,sites ▸ List.mem_cons_of_mem _ (List.mem_singleton_self _),rfl⟩

theorem anchor_models : Models refreshed = Models upperState :=
  funext (fun m => propext (models_iff m).symm)

theorem seen (ctx : Context) (cert : Refresh refreshed ctx) (gain : Known ctx.state upper) :
    Step registry root refreshed (refresh refreshed ctx) :=
  ⟨root,.root,.refresh root ctx cert upper GeneralMixedCompoundUpperSnapshot307.upper_supported
    GeneralMixedCompoundUpperSnapshot307.upper_unknown gain⟩

theorem reached_tail (ctx : Context) (cert : Refresh refreshed ctx) (gain : Known ctx.state upper) :
    B4TargetV8.Reachable (boundary roles) sourceRegistry root (refresh refreshed ctx) := by
  obtain ⟨s,initial,trace⟩ := GeneralDictionaryCompoundRefreshStep239.reachable
  exact ⟨s,initial,.tail trace (seen ctx cert gain)⟩

theorem no_install_anchor (e : Effect roles) (enabled : Installable registry refreshed e)
    (which : e.plan.packet.site.occurrence = root ∨ e.plan.packet.site.occurrence = childSite.occurrence) : False := by
  have frame := e.frame
  rw [enabled.registry_eq,enabled.snapshot_eq] at frame
  rcases which with rootHere|childHere
  · rw [rootHere] at frame
    have exactPlan := GeneralDictionaryCompoundNoInstance239.frame_plan frame
    obtain ⟨m,valid,held,_⟩ := enabled.common
    rw [exactPlan] at held
    exact GeneralDictionaryCompoundObstruction239.no_current_packet m valid held
  · rw [childHere] at frame
    exact GeneralDictionaryCompoundChild239.no_frame _ _ frame

theorem point_anchor : GeneralNominalReobservationSteps.PointClosed extendedSnapshot := by
  intro idx d found
  have same : d = GeneralDictionaryCompoundSnapshot239.pointDesc := by
    change (if idx = 0 ∨ idx = 1 then some GeneralDictionaryCompoundSnapshot239.pointDesc else none) = some d at found
    split at found
    · exact (Option.some.inj found).symm
    · cases found
  subst d
  intro parameter contained
  change parameter ∈ [.type ((2 : Fin 7),2),.type (2,2)] at contained
  rcases List.mem_cons.mp contained with p|rest
  · subst parameter; rfl
  · cases List.mem_singleton.mp rest; rfl

theorem exact_anchor {t : State roles} :
    Step registry root refreshed t ↔
      ∃ ctx : Context, Nonempty (Refresh refreshed ctx) ∧ Known ctx.state upper ∧ t = refresh refreshed ctx := by
  constructor
  · rintro ⟨focus,gen,op⟩
    have which := registered GeneralDictionaryCompoundRefreshStep239.reachable raw_sites gen
    cases op with
    | administrative act =>
      cases act with
      | enqueue linked absent =>
        obtain ⟨site,listed,eq⟩ := raw_not_novel raw_sites which
        exact False.elim (absent site listed eq)
      | refresh ctx cert n _ was gain =>
        have new := GeneralMixedCompoundAnyRefresh307.can_gain_only_upper ctx cert n was gain
        subst n; exact ⟨ctx,⟨cert⟩,gain,rfl⟩
      | equate a b one two equal novel =>
        exact False.elim (novel (GeneralMixedCompoundTailEq307.at_anchor a b one two equal))
      | reobserve revision _ improved =>
        exact False.elim (GeneralNominalReobservationSteps.pointClosed_no_revision
          (state := refreshed.core.erased.current)
          point_anchor revision improved)
    | refresh _ ctx cert n _ was gain =>
      have new := GeneralMixedCompoundAnyRefresh307.can_gain_only_upper ctx cert n was gain
      subst n; exact ⟨ctx,⟨cert⟩,gain,rfl⟩
    | install e enabled _ => exact False.elim (no_install_anchor e enabled which)
    | merge a b one two same novel =>
      exact False.elim (novel (no_merge anchor_models centers one two same))
  · rintro ⟨ctx,⟨cert⟩,gain,rfl⟩
    exact seen ctx cert gain

theorem every_successor_halted (ctx : Context) (cert : Refresh refreshed ctx) (gain : Known ctx.state upper)
    (t : State roles) : ¬ Step registry root (refresh refreshed ctx) t := by
  rintro ⟨focus,gen,op⟩
  have which := registered (reached_tail ctx cert gain) raw_sites gen
  cases op with
  | administrative act =>
    cases act with
    | enqueue linked absent =>
      obtain ⟨site,listed,eq⟩ := raw_not_novel raw_sites which
      exact absent site listed eq
    | refresh next more n present was got =>
      exact GeneralMixedCompoundAnyRefresh307.no_further_refresh ctx cert gain next more n present was got
    | equate a b one two equal novel =>
      exact novel (GeneralMixedCompoundTailEq307.at_refresh cert a b one two equal)
    | reobserve rev _ improved =>
      exact GeneralNominalReobservationSteps.pointClosed_no_revision
        (state := (refresh refreshed ctx).core.erased.current)
        (GeneralMixedCompoundAnyRefresh307.point_closed ctx cert) rev improved
  | refresh _ next more n present was got =>
    exact GeneralMixedCompoundAnyRefresh307.no_further_refresh ctx cert gain next more n present was got
  | install e enabled _ =>
    rcases which with r|c
    · exact GeneralMixedCompoundAnyRoot307.no_install ctx cert e enabled r
    · exact GeneralMixedCompoundAnyChild307.no_install ctx cert e enabled c
  | merge a b one two same novel =>
    have allModels : Models (refresh refreshed ctx) = Models upperState :=
      funext (fun m => propext ((refresh_models cert).trans (models_iff m).symm))
    exact novel (no_merge allModels centers one two same)

end Yulang.GeneralMixedCompoundTail307
