import Yulang.GeneralDeferredLadderAdministrative304

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeferredLadderRawCase304
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedInstall232 (install)
open GeneralNominalVersionedMixedKernel234 (Step Installable Committed)
open GeneralNominalSaturationState (Generated Alias)
open GeneralNominalVersionedMixedTerminalStable234 (HeadlessUnknown EqualityClosed no_refresh)
open GeneralDeferredLadderResnapshot304 (HeadView)

variable {roles : Roles.RoleDecls}

/-- Independently checkable negative administrative guards at a reached
state. No claim that every reached state has them is part of this interface. -/
structure AdministrativeClosed (s : State roles) (root : Occurrence roles) : Prop where
  recorded : ∀ o, Generated s.core.erased.current root o →
    ∃ row ∈ s.core.erased.current.sites, row.occurrence = o
  headless : HeadlessUnknown s
  equalities : EqualityClosed s
  points : GeneralNominalReobservationSteps.PointClosed s.core.erased.current.context.state
  aliases : ∀ x ∈ s.core.sites, ∀ y ∈ s.core.sites, SameInputs (Models s) x y →
    Alias s.core.erased.current x.occurrence.identity y.occurrence.identity

theorem closed_forward {a b : State roles} (ab : HeadView a b) (closed : AdministrativeClosed a root) :
    AdministrativeClosed b root := by
  refine ⟨?_,GeneralDeferredLadderAdministrative304.headless_forward ab closed.headless,
    GeneralDeferredLadderAdministrative304.equality_forward ab closed.equalities,
    ab.context ▸ closed.points,?_⟩
  · intro o seen
    obtain ⟨row,listed,eq⟩ := closed.recorded o
      ((GeneralDeferredLadderOperationalView304.generated_iff ab.raw).mpr seen)
    exact ⟨row,ab.raw.sites ▸ listed,eq⟩
  · intro x hx y hy same
    have old := closed.aliases x (ab.centers.symm ▸ hx) y (ab.centers.symm ▸ hy)
    rw [← GeneralDeferredLadderAdministrative304.model_eq ab] at same
    exact GeneralDeferredLadderOperationalView304.alias_forward ab.raw (old same)

theorem only_installs {s t : State roles} (closed : AdministrativeClosed s root)
    (step : Step registry root s t) :
    ∃ e, Installable registry s e ∧ ¬ Committed s e.plan ∧
      Generated s.core.erased.current root e.plan.packet.site.occurrence ∧ t = install s e := by
  obtain ⟨o,seen,act⟩ := step
  cases act with
  | administrative act =>
    cases act with
    | enqueue _ absent =>
      obtain ⟨row,listed,eq⟩ := closed.recorded _ seen
      exact False.elim (absent row listed eq)
    | refresh ctx c id tracked unknown known =>
      exact False.elim (no_refresh closed.headless c tracked unknown known)
    | equate a b first last equal novel =>
      exact False.elim (novel (closed.equalities a b first last equal))
    | reobserve rev _ improves =>
      exact False.elim (GeneralNominalReobservationSteps.pointClosed_no_revision closed.points rev improves)
  | refresh _ ctx c id tracked unknown known =>
    exact False.elim (no_refresh closed.headless c tracked unknown known)
  | install e good fresh => exact ⟨e,good,fresh,seen,rfl⟩
  | merge x y first last same novel =>
    exact False.elim (novel (closed.aliases x first y last same))

end Yulang.GeneralDeferredLadderRawCase304
