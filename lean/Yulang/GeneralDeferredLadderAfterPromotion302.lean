import Yulang.GeneralDeferredLadderRefreshHead302

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeferredLadderAfterPromotion302
open GeneralDeferredLadderLedger302 (Phase env)
open GeneralDeferredLadderNoAdmin302 (padded no_private_head only_equal_names)
open GeneralDeferredLadderReport302 (nominal_at)
open GeneralDeferredLadderRefreshHead302 (terminal_has_no_nominal)
open GeneralDeferredLadderOnlyInstall302 (generated)
open GeneralDeferredLadderExact302 (Promotion RawStep)
open GeneralObservedLadderRoute301 (sites_exact site)
open GeneralObservedLadderReport301 (pos)
open GeneralObservedLadderNoAdmin301 (padding free)
open GeneralNominalVersionedMixedTerminalStable234 (HeadlessUnknown EqualityClosed no_refresh)
open GeneralNominalVersionedMixedObservations233 (Refresh)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralDeclarationExamples (roles)
open GeneralNominalExamples (displayRoot)
open GeneralNominalVersionedMixedKernel234 (Step Committed Installable)
open GeneralDeferredLadderPlan302 (compiled)
open CommonNominalFullCarrier (subtype_refl Ty)

theorem all_known (p : Phase n k) (ctx : GeneralNominalCandidates.Context)
    (cert : Refresh p.state ctx) (terminal : GeneralNominalState.Known ctx.state (n+1))
    (a : Nat) (small : a ≤ n+1) : GeneralNominalState.Known ctx.state a := by
  by_cases earlier : a ≤ n
  · apply cert.refines.known
    rw [p.context_eq]
    exact GeneralObservedLadderRefreshProgram301.earlier_known n a earlier
  · have atEnd : a = n+1 := by omega
    subst a
    exact terminal

theorem headless (p : Phase n k) (ctx : GeneralNominalCandidates.Context)
    (cert : Refresh p.state ctx) (terminal : GeneralNominalState.Known ctx.state (n+1)) :
    HeadlessUnknown (refresh p.state ctx) := by
  refine ⟨padding n (fun _ => .top),
    (GeneralNominalVersionedMixedObservations233.refresh_models cert).mpr (padded p _),?_⟩
  intro id _ none test holds
  have high : n+1 < id := by
    by_cases small : id ≤ n+1
    · exact False.elim (none (all_known p ctx cert terminal id small))
    · omega
  rw [free _ _ _ high] at holds
  exact GeneralDictionaryGroundCopy218Refresh.top_no_head test holds

theorem equality_closed (p : Phase n k) (ctx : GeneralNominalCandidates.Context)
    (cert : Refresh p.state ctx) : EqualityClosed (refresh p.state ctx) := by
  intro a b _ _ holds
  have same : a = b := only_equal_names p a b
    (fun m atOld => holds m ((GeneralNominalVersionedMixedObservations233.refresh_models cert).mpr atOld))
  cases same
  intro _ _
  exact ⟨subtype_refl _,subtype_refl _⟩

theorem point_closed (p : Phase n k) (ctx : GeneralNominalCandidates.Context)
    (cert : Refresh p.state ctx) (terminal : GeneralNominalState.Known ctx.state (n+1)) :
    GeneralNominalReobservationSteps.PointClosed ctx.state := by
  intro slot desc seen
  let a := ctx.state.base.source slot
  by_cases inner : a ≤ n
  · let b := pos n a (by omega)
    have data : (env p).state.nominals b = some (GeneralNominalOutputGrowthModels.descriptor n b inner) :=
      nominal_at n a inner
    have lift := cert.refines
    rw [p.context_eq] at lift
    have records := lift.nominals b _ data
    have eq : lift.base.embed b = slot := ctx.state.base.source_injective (lift.base.source b)
    rw [eq] at records
    have exactDesc := Option.some.inj (seen.symm.trans records)
    rw [exactDesc]
    intro param member
    let c : Fin (n+2) := ⟨a+1,by omega⟩
    change param ∈ [GeneralNominalRefinements.renameParameter lift.base.embed
      (.type (c,c))] at member
    cases List.mem_singleton.mp member
    rfl
  by_cases last : a = n+1
  · rw [(terminal_has_no_nominal p ctx cert terminal slot last).2] at seen
    cases seen
  have high : n+1 < a := by omega
  exact False.elim (no_private_head p ctx cert a high ⟨slot,rfl,.inr ⟨desc,seen⟩⟩)

theorem same_lists (p : Phase n k) (ctx : GeneralNominalCandidates.Context) :
    (refresh p.state ctx).core.sites = p.state.core.sites ∧
    (refresh p.state ctx).core.erased.current.sites = p.state.core.erased.current.sites ∧
    (refresh p.state ctx).core.erased.current.edges = p.state.core.erased.current.edges := ⟨rfl,rfl,rfl⟩

theorem reverse_generated (p : Phase n k) (ctx : GeneralNominalCandidates.Context)
    {o : GeneralSourceDictionaries.Occurrence roles}
    (h : GeneralNominalSaturationState.Generated (refresh p.state ctx).core.erased.current displayRoot o) :
    GeneralNominalSaturationState.Generated p.state.core.erased.current displayRoot o := by
  have back {a b} (given : GeneralNominalSaturationState.Alias (refresh p.state ctx).core.erased.current a b) :
      GeneralNominalSaturationState.Alias p.state.core.erased.current a b := by
    induction given with
    | refl => exact .refl _
    | edge same => exact .edge same
    | symm _ ih => exact .symm ih
    | trans _ _ i j => exact .trans i j
  induction h with
  | root => exact .root
  | child _ edge ih => exact .child ih edge
  | alias _ first last same ih => exact .alias ih first last (back same)

theorem after_only_install (p : Phase n k) (cap : k ≤ n+1) (s t : State roles)
    (promotion : Promotion n p.state s) (raw : RawStep s t) :
    ∃ e, Installable compiled s e ∧ ¬ Committed s e.plan ∧
      t = GeneralNominalVersionedInstall232.install s e := by
  obtain ⟨ctx,cert,terminal,rfl⟩ := promotion
  change Step compiled displayRoot (refresh p.state ctx) t at raw
  obtain ⟨o,generated,action⟩ := raw
  cases action with
  | administrative action =>
    cases action with
    | enqueue _ absent =>
      obtain ⟨row,recorded,eq⟩ := GeneralDeferredLadderOnlyInstall302.recorded p (reverse_generated p ctx generated)
      exact False.elim (absent row recorded eq)
    | refresh target c id tracked unknown known =>
      exact False.elim (no_refresh (headless p ctx cert terminal) c tracked unknown known)
    | equate a b first last equal novel =>
      exact False.elim (novel (equality_closed p ctx cert a b first last equal))
    | reobserve rev _ improves =>
      exact False.elim (GeneralNominalReobservationSteps.pointClosed_no_revision (point_closed p ctx cert terminal) rev improves)
  | refresh _ target c id tracked unknown known =>
    exact False.elim (no_refresh (headless p ctx cert terminal) c tracked unknown known)
  | install e held fresh =>
    exact ⟨e,held,fresh,rfl⟩
  | merge a b first last same novel =>
    change a ∈ p.state.core.sites at first
    change b ∈ p.state.core.sites at last
    rw [p.centers_eq] at first last
    obtain ⟨i,ai,rfl⟩ := (sites_exact ..).mp first
    obtain ⟨j,bj,rfl⟩ := (sites_exact ..).mp last
    have eqModels : Models (refresh p.state ctx) = Models p.state :=
      funext fun m => propext (GeneralNominalVersionedMixedObservations233.refresh_models cert)
    rw [eqModels] at same
    have indexes := GeneralDeferredLadderNoAdmin302.separates p (by omega) (by omega) same
    cases indexes
    exact False.elim (novel (.refl _))

end Yulang.GeneralDeferredLadderAfterPromotion302
