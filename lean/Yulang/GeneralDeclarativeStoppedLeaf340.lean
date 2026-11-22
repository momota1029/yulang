import Yulang.GeneralDeclarativeStoppedCurrent340

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeStoppedLeaf340
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedJournal232 (State Effect Models)
open GeneralNominalVersionedMixedKernel234 (Step At Stable Installable)
open GeneralNominalVersionedInstallStep232 (Committed)
open GeneralNominalSaturationState (Generated)
open GeneralNominalCenteredHeadOutputs (requests)
open GeneralNominalCenteredHeadMatEffects (Ready)
open GeneralNominalVersionedEffects231 (body_holds_iff ClassEffects)
open GeneralNominalVersionedEvidence231 (Frame Certificate Evidence certificate_of_semantics evidence_leaf)
open GeneralDeclarativeStoppedOutput339 (Receipt ordinary ordinary_holds)
open GeneralDeclarativeStoppedOrder339 (complete_known checked_order compileRequests member_authored)
open GeneralDeclarativeStoppedProjection340 (project append append_exact exact_models)
open GeneralStoppedProjectedTrace335 (current)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeEntailment320 (Holds)
open GeneralSourceState (Output)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (All₂)

/-- Use the actual non-redundant raw install transition. At an already
halted state, an independently installable generated proposal must be
semantically committed in *each* current model. Journal membership
is not needed; this proves no progress, termination, or installability. -/
theorem committed {s : State roles} {r : Registry} {root : Occurrence roles} {effect : Effect roles}
    (stopped : ∀ after, ¬ Step r root s after)
    (live : Generated s.core.erased.current root effect.plan.packet.site.occurrence)
    (available : Installable r s effect) : Committed s effect.plan :=
  Classical.byContradiction (fun absent => stopped _ ⟨_,live,.install effect available absent⟩)

theorem frame {s : State roles} {r : Registry} {effect : Effect roles}
    (available : Installable r s effect) :
    Frame r s.core effect.plan.packet.site.occurrence effect.plan.packet.declaration.id effect.plan := by
  rw [← available.registry_eq,← available.snapshot_eq]
  exact effect.frame

theorem current_ready {s : State roles} {r : Registry} {effect : Effect roles}
    (available : Installable r s effect) :
    Ready s.core effect.plan.packet.site.occurrence effect.plan := by
  rw [← available.snapshot_eq]
  exact effect.ready

theorem receipt_holds {s : State roles} {effect : Effect roles}
    (accepted : ClassEffects s.core effect.plan.packet.site.occurrence effect.plan m)
    (receipt : Receipt s effect output row) : Holds m row := by
  obtain ⟨body,registered,printed⟩ := receipt.authored
  exact ordinary_holds printed ((body_holds_iff effect.plan output.target m body).mp
    (accepted.1 output receipt.requested body registered))

/-- The uninstalled path shares the given raw model with literal current
output syntax and its exact alias-class order; no existential change
of assignment and no fabricated completed-output origin. -/
theorem current_outputs {s : State roles} {r : Registry} {root : Occurrence roles} {effect : Effect roles}
    (stopped : ∀ after, ¬ Step r root s after)
    (live : Generated s.core.erased.current root effect.plan.packet.site.occurrence)
    (available : Installable r s effect) (m : Assignment) (fit : Models s m) :
    ∃ rows, compileRequests effect.plan (requests s.core effect.plan.packet.site.occurrence) = some rows ∧
      rows.map Equation.left = (requests s.core effect.plan.packet.site.occurrence).map Output.target ∧
      All₂ (Receipt s effect) (requests s.core effect.plan.packet.site.occurrence) rows ∧
      ∀ row ∈ rows, Holds m row := by
  obtain ⟨rows,found⟩ := complete_known (current_ready available) (fun _ h => h)
  obtain ⟨each,ordered⟩ := checked_order (fun _ h => h) found
  have accepted := ((committed stopped live available).1 m fit).2
  refine ⟨rows,found,ordered,each,?_⟩
  intro row within
  obtain ⟨_,_,exactRow⟩ := member_authored each within
  exact receipt_holds accepted exactRow

theorem same_model_leaf {s : State roles} {r : Registry} {root : Occurrence roles} {effect : Effect roles}
    (stopped : ∀ after, ¬ Step r root s after)
    (live : Generated s.core.erased.current root effect.plan.packet.site.occurrence)
    (available : Installable r s effect)
    (noChildren : GeneralNominalVersionedFrame231.children effect.plan.packet = [])
    (m : Assignment) (fit : Models s m) :
    Evidence r s.core m effect.plan.packet.site.occurrence (.node effect.plan.packet.declaration.id []) := by
  obtain ⟨packet,effects⟩ := (committed stopped live available).1 m fit
  exact evidence_leaf ⟨effect.plan,certificate_of_semantics (frame available) noChildren.symm
    packet (current_ready available) effects⟩

theorem projected_outputs {s : State roles} {r : Registry} {root : Occurrence roles} {effect : Effect roles}
    (stopped : ∀ after, ¬ Step r root s after)
    (live : Generated s.core.erased.current root effect.plan.packet.site.occurrence)
    (available : Installable r s effect) (lowered : project (current s) = some v)
    (m : Assignment) (fit : Models s m) :
    ∃ rows, compileRequests effect.plan (requests s.core effect.plan.packet.site.occurrence) = some rows ∧
      rows.map Equation.left = (requests s.core effect.plan.packet.site.occurrence).map Output.target ∧
      GeneralDeclarativeStoppedProjection340.Models (append v rows) m := by
  obtain ⟨rows,found,order,_,holds⟩ := current_outputs stopped live available m fit
  exact ⟨rows,found,order,(append_exact v rows m).mpr
    ⟨(exact_models _ m lowered).mpr fit.1.1,holds⟩⟩

end Yulang.GeneralDeclarativeStoppedLeaf340
