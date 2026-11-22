import Yulang.GeneralDeclarativeStoppedLockstep341
import Yulang.GeneralNominalVersionedMixedChoice236
import Yulang.GeneralRebaseNonleafRetarget276

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeStoppedRetarget341
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalCenters (Plan)
open GeneralNominalVersionedJournal232 (State Effect Models)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary Local)
open GeneralNominalCenteredHeadAllocEncoding (registry)
open GeneralNominalVersionedKernel232
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedMixedFrameSelection235 (selected_identifies)
open GeneralNominalVersionedPlans231 (Holds)
open GeneralNominalVersionedEffects231 (ClassEffects)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRefinements (Refines)
open GeneralRebaseRetarget275 (retarget Observed)
open GeneralDeclarativeStoppedSelected340 (FitFrame)
open GeneralDeclarativeStoppedOrder339 (compileRequests)
open GeneralDeclarativeStoppedOutput339 (captureFor ordinary)
open GeneralNominalCenteredHeadMatEffects (compileBody)
open GeneralDictionaryAssociatedProvenance (Body)
open GeneralSourceState (Output)

section Retarget
variable {roles : Roles.RoleDecls} {s : State roles} {r : Registry} {root : Occurrence roles}
  {after : GeneralNominalCandidates.Context}
  (plan : Plan roles) (ref : Refines plan.packet.context.state after.state)
  (interp : after.interpretation = plan.packet.context.interpretation)
  (seen : Observed plan)

include interp seen in
theorem compiled_row_same (o : Output) (body : Body) :
    ordinary (retarget plan ref) o body = ordinary plan o body := by
  have rendered : compileBody (retarget plan ref) body = compileBody plan body := by
    cases body <;> simp only [compileBody,interp]
  have names : captureFor (retarget plan ref) body = captureFor plan body := by
    cases body with
    | explicit _ =>
      funext n
      exact congrArg GeneralDeclarativeOpaqueNominal328.point
        ((GeneralNominalVersionedFrame231.binder_eq (retarget plan ref) n).symm.trans
          ((GeneralRebaseRetarget275.binder plan ref interp seen n).trans
            (GeneralNominalVersionedFrame231.binder_eq plan n)))
    | default _ _ _ => rfl
  unfold ordinary
  rw [rendered,names]

include interp seen in
theorem ordered_rows_same (items : List Output) :
    compileRequests (retarget plan ref) items = compileRequests plan items := by
  induction items with
  | nil => rfl
  | cons first later ih =>
    unfold compileRequests
    have decl : (retarget plan ref).packet.declaration = plan.packet.declaration := rfl
    rw [decl]
    cases h : GeneralDictionaryAssociatedProvenance.lookup roles plan.packet.declaration first.name with
    | none => rfl
    | some body =>
      simp only [compiled_row_same plan ref interp seen,ih]

include interp seen in
/-- A true historical effect with an observation-preserving retarget
provides full, current packet feasibility in every current raw model.
The old packet is not reinstalled and retained class targets are
read from the actual current class, not the old snapshot. -/
theorem recorded_semantics
    (path : B4TargetV8.Reachable (boundary roles) r root s)
    {saved : Effect roles} (member : saved ∈ s.effects) (same : saved.plan = plan)
    (current : after = s.core.erased.current.context) (m : Assignment) (model : Models s m) :
    Holds (retarget plan ref) m ∧ ClassEffects s.core plan.packet.site.occurrence (retarget plan ref) m := by
  have old := GeneralNominalVersionedMixedRecorded234.reachable_effect_full_holds path model member
  have live := (GeneralNominalVersionedJournal232.effect_models model member).2
  change ClassEffects s.core saved.plan.packet.site.occurrence saved.plan m at live
  rw [same] at old live
  refine ⟨(GeneralRebaseNonleafRetarget276.holds_iff plan ref interp seen m).mpr
    ⟨current.symm ▸ model.1.1,old.2.1,old.2.2⟩,
    GeneralRebaseRetargetEffects275.class_effects plan ref interp s.core seen m live⟩

include interp seen in
/-- One key per role is a sufficient condition on this lemma, not an
eligibility restriction. This derives choice from actual reachable
journal history. It uses a given current Frame and a genuine previous
effect with independently preserved observation. -/
theorem fit_unique_role
    (checked : (boundary roles).Checked r)
    (path : B4TargetV8.Reachable (boundary roles) r root s)
    {saved : Effect roles} (member : saved ∈ s.effects) (same : saved.plan = plan)
    (frame : Frame (registry r) s.core focus key (retarget plan ref))
    (picked : Local r s focus (.selected key kids))
    (unique : ∀ a ∈ (registry r).declarations, ∀ b ∈ (registry r).declarations, a.role = b.role → a.id = b.id)
    (m : Assignment) (model : Models s m) :
    FitFrame (s := s) focus (retarget plan ref) := by
  have sel : Local r s (retarget plan ref).packet.site.occurrence
      (.selected (retarget plan ref).packet.declaration.id kids) := by
    rw [frame.occurrence_eq, frame.key_eq]
    exact picked
  have ready := recorded_semantics plan ref interp seen path member same frame.context_eq m model
  refine ⟨GeneralNominalVersionedMixedChoice236.choice_of_role_unique checked path sel frame.visible (frame.occurrence_eq.symm ▸ frame.role_eq) unique,
    m,model,ready.1,?_⟩
  rw [← frame.occurrence_eq]
  exact ready.2

end Retarget
end Yulang.GeneralDeclarativeStoppedRetarget341
