import Yulang.GeneralNominalFeedbackSteps

/-!
# Exact location of possible model loss in actual feedback traces

InitialSource does not assert model existence. Even starting inhabited, the
unchanged merge constructor supplies SameInputs but no DictionaryOutputs proof.
The theorems isolate the only transition that can remove all models; they do
not assert that such a merge is reachable or refute the reachable B4 target.
-/
namespace Yulang.GeneralDictionaryModelLoss
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalFeedbackSteps
open GeneralNominalDemandMerging (Site)
open GeneralNominalCommonBridge (Assignment)

variable {roles : Roles.RoleDecls} {registry : Registry}

def Inhabited (state : State roles) : Prop := ∃ model, Models state model

/-- An actual merge shape, retaining all enabling premises and the precise
output equations that exclude every previous model. -/
def DestructiveMerge (before after : State roles)
    (focus : Occurrence roles) : Prop :=
  ∃ first last : Site roles, first ∈ before.sites ∧ last ∈ before.sites ∧
    GeneralNominalFeedbackSites.SameInputs before first last ∧
    ¬ Alias before first.occurrence.identity last.occurrence.identity ∧
    focus = first.occurrence ∧ after = merge before first last ∧
    ∀ model, Models before model →
      ¬ PresenceNormalForm.All CommonNominalFullCarrier.model model
        (GeneralNominalDemandMerging.outputAtoms first last)

/-- All four non-merge constructors preserve existence. In particular install
contains its own compatible model witness; SameInputs alone is not silently
used as a model-preservation theorem for merge. -/
theorem at_loss_is_merge (update : At registry before focus after)
    (old : Inhabited before) (lost : ¬ Inhabited after) :
    DestructiveMerge before after focus := by
  obtain ⟨model,valid⟩ := old
  cases update with
  | enqueue focus _ _ =>
      exact False.elim (lost ⟨model,(enqueue_models _ _ _).mpr valid⟩)
  | install packet enabled _ =>
      obtain ⟨_,same,_,_,_,_,_,_,_,_,witness,_⟩ := enabled.1
      obtain ⟨chosen,holds,branch⟩ := witness
      exact False.elim (lost ⟨chosen,
        (GeneralNominalFeedbackSites.install_models _ packet _ same chosen).mpr ⟨holds,branch⟩⟩)
  | merge first last one two same novel =>
      refine ⟨first,last,one,two,same,novel,rfl,rfl,?_⟩
      intro chosen holds outputs
      exact lost ⟨chosen,(merge_models _ _ _ _).mpr ⟨holds,outputs⟩⟩
  | refresh _ _ certificate _ _ _ _ =>
      exact False.elim (lost ⟨model,(GeneralNominalCycleSteps.refresh_models certificate model).mpr valid⟩)
  | equate _ _ _ _ _ equal _ =>
      exact False.elim (lost ⟨model,(equate_models _ _ _ equal model).mpr valid⟩)

/-- A real update whose target is unequal to every matching merge-shaped state
cannot remove all models. This sufficient extensional exclusion is independent
of Models; it is stronger than merely naming a non-merge constructor. -/
theorem at_inhabited_of_not_merge (update : At registry before focus after)
    (old : Inhabited before)
    (notMerge : ∀ first last : Site roles, focus = first.occurrence →
      after ≠ merge before first last) : Inhabited after := by
  classical
  apply Classical.byContradiction
  intro lost
  obtain ⟨first,last,_,_,_,_,sameFocus,sameAfter,_⟩ := at_loss_is_merge update old lost
  exact notMerge first last sameFocus sameAfter

/-- A possibly destructive merge is still an actual enabled At transition. -/
theorem destructiveMerge_at (h : DestructiveMerge before after focus) :
    At registry before focus after := by
  obtain ⟨first,last,one,two,same,novel,rfl,rfl,_⟩ := h
  exact .merge first last one two same novel

/-- This exact certificate suffices to show the output state has no model. -/
theorem destructiveMerge_empty (h : DestructiveMerge before after focus) :
    ¬ Inhabited after := by
  obtain ⟨first,last,_,_,_,_,_,rfl,excludes⟩ := h
  rintro ⟨model,valid⟩
  obtain ⟨old,outputs⟩ := (merge_models _ _ _ _).mp valid
  exact excludes model old outputs

/-- If an actual finite path from an inhabited state loses all models, an
actual prefix ends just before a destructive merge. This locates an obligation,
not an example proving that the obstruction happens on formed states. -/
theorem trace_loss_has_merge (path : B4Target.Steps (Step registry root) start finish)
    (old : Inhabited start) (lost : ¬ Inhabited finish) :
    ∃ before after focus, B4Target.Steps (Step registry root) start before ∧
      Generated before root focus ∧ Inhabited before ∧
      DestructiveMerge before after focus := by
  classical
  induction path with
  | refl => exact False.elim (lost old)
  | @tail mid last previous step ih =>
      by_cases has : Inhabited mid
      · obtain ⟨focus,generated,update⟩ := step
        exact ⟨mid,last,focus,previous,generated,has,at_loss_is_merge update has lost⟩
      · exact ih has

end Yulang.GeneralDictionaryModelLoss
