import Yulang.GeneralNominalVersionedJournalFrame236
import Yulang.GeneralNominalVersionedMixedEqualityClosure235
import Yulang.GeneralNominalVersionedMixedAdministrative236
set_option backward.isDefEq.respectTransparency false
/-! Semantic finite support is inherited through justified observations.
No syntactic provenance, satisfiability or target completion is assumed. -/
namespace Yulang.GeneralNominalVersionedModelSupport237
open GeneralNominalVersionedJournal232
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredFrame179 (Agree)
variable {roles : Roles.RoleDecls} {state before after : State roles}

def Support (state : State roles) (names : List Nat) : Prop :=
 ∀ first last : Assignment, Agree names first last → (Models state first ↔ Models state last)

theorem current (state : State roles) : Support state (GeneralNominalVersionedJournalFrame236.sources state) :=
 fun _ _ same => GeneralNominalVersionedJournalFrame236.models_iff state same

theorem weaken (supported : Support state names) (included : names ⊆ larger) : Support state larger :=
 fun _ _ same => supported _ _ (fun n h => same n (included h))

theorem transport (same : ∀ model, Models after model ↔ Models before model)
 (supported : Support before names) : Support after names :=
 fun first last agree => (same first).trans ((supported first last agree).trans (same last).symm)

theorem refresh (certificate : GeneralNominalVersionedMixedObservations233.Refresh state context)
 (supported : Support state names) : Support (GeneralNominalVersionedRefresh232.refresh state context) names :=
 transport (fun _ => GeneralNominalVersionedMixedObservations233.refresh_models certificate) supported

theorem reobserve (certificate : GeneralNominalVersionedMixedObservations233.Reobserve state revision)
 (supported : Support state names) : Support (GeneralNominalVersionedRefresh232.reobserve state revision) names :=
 transport (fun _ => GeneralNominalVersionedMixedObservations233.reobserve_models certificate) supported

theorem equate (equal : GeneralNominalVersionedMixedKernel234.Equal state first last)
 (supported : Support state names) : Support (GeneralNominalVersionedAdministrative232.equate state first last) names :=
 transport (GeneralNominalVersionedMixedEqualityClosure235.equate_models_iff equal) supported

inductive Observation : State roles → State roles → Prop
 | refresh (state : State roles) (context : GeneralNominalCandidates.Context) : GeneralNominalVersionedMixedObservations233.Refresh state context →
     Observation state (GeneralNominalVersionedRefresh232.refresh state context)
 | reobserve (state : State roles) (revision : GeneralNominalReobservationSteps.Revision state.core.erased.current) : GeneralNominalVersionedMixedObservations233.Reobserve state revision →
     Observation state (GeneralNominalVersionedRefresh232.reobserve state revision)
 | equate (state : State roles) (first last : Nat) : GeneralNominalVersionedMixedKernel234.Equal state first last →
     Observation state (GeneralNominalVersionedAdministrative232.equate state first last)

theorem observation_models (action : Observation before after) (model : Assignment) :
 Models after model ↔ Models before model := by
 cases action with
 | refresh _ certificate => exact GeneralNominalVersionedMixedObservations233.refresh_models certificate
 | reobserve _ certificate => exact GeneralNominalVersionedMixedObservations233.reobserve_models certificate
 | equate _ _ equal => exact GeneralNominalVersionedMixedEqualityClosure235.equate_models_iff equal model

theorem observations_models (path : B4Target.Steps Observation before after) (model : Assignment) :
 Models after model ↔ Models before model := by
 induction path with
 | refl => rfl
 | tail _ action ih => exact (observation_models action model).trans ih

theorem observations (path : B4Target.Steps Observation before after) (supported : Support before names) :
 Support after names := transport (observations_models path) supported

theorem patch (supported : Support state names) (valid : Models state model)
 (same : Agree names model patched) : Models state patched := (supported model patched same).mp valid

/-- Observation-only ordinary constraints cannot invalidate a patch that already
preserves the checkpoint model. No agreement on the later raw atom list is needed. -/
theorem checkpoint_patch (path : B4Target.Steps Observation before after)
 (valid : Models after model)
 (same : Agree (GeneralNominalVersionedJournalFrame236.sources before) model patched) :
 Models after patched := patch (observations path (current before)) valid same
end Yulang.GeneralNominalVersionedModelSupport237
