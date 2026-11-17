import Yulang.GeneralNominalVersionedMixedTerminalStable234
set_option backward.isDefEq.respectTransparency false
/-! Actual mixed stability consequences; guarded-effect availability is explicit. -/
namespace Yulang.GeneralNominalVersionedMixedStableLaws235
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 GeneralNominalVersionedMixedKernel234
open GeneralNominalSaturationState (Generated)
variable {roles : Roles.RoleDecls} {registry : Registry} {state : State roles}
  {root focus : Occurrence roles}

theorem equality_closed (stable : Stable registry state root) :
    GeneralNominalVersionedMixedTerminalStable234.EqualityClosed state := by
  intro first last one two equal
  apply Classical.byContradiction
  intro novel
  exact stable root .root _ (.administrative (.equate root first last one two equal novel))

theorem no_new_known (stable : Stable registry state root)
    (certificate : GeneralNominalVersionedMixedObservations233.Refresh state context)
    (member : identity ∈ GeneralNominalState.sources state.core.erased.current.context.state)
    (unknown : ¬ GeneralNominalState.Known state.core.erased.current.context.state identity) :
    ¬ GeneralNominalState.Known context.state identity := by
  intro known
  exact stable root .root _ (.refresh root context certificate identity member unknown known)

theorem no_reobserve (stable : Stable registry state root)
    (certificate : GeneralNominalVersionedMixedObservations233.Reobserve state revision) :
    ¬ GeneralNominalReobservationSteps.Improves revision := by
  intro improved
  exact stable root .root _ (.administrative (.reobserve root revision certificate improved))

theorem generated_site (stable : Stable registry state root)
    (generated : Generated state.core.erased.current root focus)
    (linked : GeneralNominalState.Linked state.core.erased.current.context.state focus.demand) :
    ∃ site ∈ state.core.erased.current.sites, site.occurrence = focus := by
  apply Classical.byContradiction
  intro absent
  apply stable focus generated _ (.administrative (.enqueue focus linked ?_))
  intro site member equal
  exact absent ⟨site,member,equal⟩

theorem same_inputs_alias (stable : Stable registry state root)
    (generated : Generated state.core.erased.current root first.occurrence)
    (one : first ∈ state.core.sites) (two : last ∈ state.core.sites)
    (same : SameInputs (Models state) first last) :
    GeneralNominalSaturationState.Alias state.core.erased.current first.occurrence.identity last.occurrence.identity := by
  apply Classical.byContradiction
  intro novel
  exact stable first.occurrence generated _ (.merge first last one two same novel)

theorem install_committed (stable : Stable registry state root)
    (generated : Generated state.core.erased.current root effect.plan.packet.site.occurrence)
    (enabled : Installable registry state effect) : Committed state effect.plan := by
  apply Classical.byContradiction
  intro novel
  exact stable effect.plan.packet.site.occurrence generated _ (.install effect enabled novel)

theorem install_semantics (stable : Stable registry state root)
    (generated : Generated state.core.erased.current root effect.plan.packet.site.occurrence)
    (enabled : Installable registry state effect) (valid : Models state model) :
    GeneralNominalVersionedPlans231.Holds effect.plan model ∧
    GeneralNominalVersionedEffects231.ClassEffects state.core effect.plan.packet.site.occurrence effect.plan model :=
  (install_committed stable generated enabled).1 model valid

theorem install_children (stable : Stable registry state root)
    (generated : Generated state.core.erased.current root effect.plan.packet.site.occurrence)
    (enabled : Installable registry state effect)
    (member : child ∈ GeneralNominalVersionedFrame231.children effect.plan.packet) :
    (effect.plan.packet.site.occurrence,child) ∈ state.core.erased.current.edges :=
  (install_committed stable generated enabled).2 child member

end Yulang.GeneralNominalVersionedMixedStableLaws235
