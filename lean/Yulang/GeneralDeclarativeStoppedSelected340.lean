import Yulang.GeneralDeclarativeStoppedLeaf340
import Yulang.GeneralNominalVersionedMixedCommon235

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeStoppedSelected340
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalCenters (Plan)
open GeneralNominalVersionedJournal232 (State Effect Models)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary Local local_iff)
open GeneralNominalCenteredHeadAllocEncoding (registry)
open GeneralNominalVersionedMixedKernel234 (Step Installable)
open GeneralNominalVersionedEvidence231 (Frame Evidence)
open GeneralNominalVersionedMixedFrameSelection235 (effect_of_selected selected_identifies)
open GeneralNominalVersionedMixedCommon235 (source_installable_iff)
open GeneralNominalSaturationState (Generated)
open GeneralNominalVersionedEffects231 (ClassEffects)
open GeneralNominalVersionedPlans231 (Holds)
open GeneralNominalCenteredHeadOutputs (requests)
open GeneralDeclarativeStoppedOrder339 (compileRequests complete_known checked_order member_authored)
open GeneralDeclarativeStoppedOutput339 (Receipt)
open GeneralDeclarativeStoppedLeaf340 (committed current_ready receipt_holds same_model_leaf)
open GeneralDeclarativeHead320 (Equation)
open GeneralSourceState (Output)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (All₂)

/-- Independent premises for filling the current raw effect. These are
not derivable solely from choosing a key: prior alias-class choices
must agree, and at least one actual full current packet must fit. -/
structure FitFrame {s : State roles} (a : Occurrence roles) (plan : Plan roles) : Prop where
  compatible : GeneralNominalCycleSteps.ChoiceCompatible s.core.erased.current plan.packet
  feasible : ∃ m, Models s m ∧ Holds plan m ∧ ClassEffects s.core a plan m

theorem install_from_frame {roles : Roles.RoleDecls} {r : Registry} {s : State roles} {root a : Occurrence roles} {plan : Plan roles} {key : Nat} {kids : List (Occurrence roles)}
    (checked : (boundary roles).Checked r)
    (path : B4TargetV8.Reachable (boundary roles) r root s)
    (selected : Local r s a (.selected key kids))
    (frame : Frame (registry r) s.core a key plan) (ready : FitFrame (s := s) a plan) :
    ∃ e : Effect roles, e.plan = plan ∧ Installable (registry r) s e := by
  have known := GeneralNominalVersionedMixedReady235.ready checked path frame
  let cand := effect_of_selected (local_iff.mp selected) frame known
  have exactSelection : Local r s cand.plan.packet.site.occurrence (.selected key kids) :=
    frame.occurrence_eq.symm ▸ selected
  have available := (source_installable_iff checked path exactSelection (effect := cand) rfl rfl).mpr
    ⟨ready.compatible,by
      obtain ⟨m,held,packet,body⟩ := ready.feasible
      refine ⟨m,held,packet,?_⟩
      change ClassEffects s.core plan.packet.site.occurrence plan m
      rw [frame.occurrence_eq]
      exact body⟩
  exact ⟨cand,rfl,available⟩

/-- A successful-stop source theorem with just the *actual* current
frame, prior-choice compatibility, and one full feasible packet as
independent premises. The very same literal ordered receipt is then
valid for every current raw model, as is the selected leaf dictionary. -/
theorem source_leaf {roles : Roles.RoleDecls} {r : Registry} {s : State roles} {root a : Occurrence roles} {plan : Plan roles} {key : Nat}
    (checked : (boundary roles).Checked r)
    (path : B4TargetV8.Reachable (boundary roles) r root s)
    (selected : Local r s a (.selected key []))
    (frame : Frame (registry r) s.core a key plan) (ready : FitFrame (s := s) a plan)
    (generated : Generated s.core.erased.current root a)
    (stopped : ∀ next, ¬ Step (registry r) root s next) :
    ∃ rows, compileRequests plan (requests s.core a) = some rows ∧
      rows.map Equation.left = (requests s.core a).map Output.target ∧
      ∀ m, Models s m → Evidence (registry r) s.core m a (.node key []) ∧
        ∀ row ∈ rows, GeneralDeclarativeEntailment320.Holds m row := by
  obtain ⟨e,rfl,available⟩ := install_from_frame checked path selected frame ready
  have live : Generated s.core.erased.current root e.plan.packet.site.occurrence :=
    frame.occurrence_eq.symm ▸ generated
  have leaf := (selected_identifies (local_iff.mp selected) frame).2
  have saved := committed stopped live available
  obtain ⟨rows,found⟩ := complete_known (current_ready available) (fun _ h => h)
  obtain ⟨each,exactOrder⟩ := checked_order (fun _ h => h) found
  have offer m (fit : Models s m) := same_model_leaf stopped live available leaf m fit
  refine ⟨rows,frame.occurrence_eq ▸ found,frame.occurrence_eq ▸ exactOrder,?_⟩
  intro m fit
  have evidence := offer m fit
  rw [frame.occurrence_eq,frame.key_eq] at evidence
  refine ⟨evidence,?_⟩
  intro row listed
  obtain ⟨_,_,got⟩ := member_authored each listed
  exact receipt_holds (saved.1 m fit).2 got

/-- A committed actual stopped node also composes with its original ordered
children, each already certified in this very same raw model. This is
a local fold rule, not proof of installing or finding child evidence. -/
theorem source_node {roles : Roles.RoleDecls} {r : Registry} {s : State roles}
    {root a : Occurrence roles} {plan : Plan roles} {key : Nat} {kids : List (Occurrence roles)}
    {dictionaries : List GeneralDictionaryReadback.Payload}
    (checked : (boundary roles).Checked r)
    (path : B4TargetV8.Reachable (boundary roles) r root s)
    (selected : Local r s a (.selected key kids))
    (frame : Frame (registry r) s.core a key plan) (ready : FitFrame (s := s) a plan)
    (generated : Generated s.core.erased.current root a)
    (stopped : ∀ next, ¬ Step (registry r) root s next) :
    ∃ rows, compileRequests plan (requests s.core a) = some rows ∧
      rows.map Equation.left = (requests s.core a).map Output.target ∧
      ∀ m, Models s m → All₂ (Evidence (registry r) s.core m) kids dictionaries →
        Evidence (registry r) s.core m a (.node key dictionaries) ∧
        ∀ row ∈ rows, GeneralDeclarativeEntailment320.Holds m row := by
  obtain ⟨e,rfl,available⟩ := install_from_frame checked path selected frame ready
  have live : Generated s.core.erased.current root e.plan.packet.site.occurrence :=
    frame.occurrence_eq.symm ▸ generated
  have matching := (selected_identifies (local_iff.mp selected) frame).2.symm
  have saved := committed stopped live available
  obtain ⟨rows,found⟩ := complete_known (current_ready available) (fun _ h => h)
  obtain ⟨each,order⟩ := checked_order (fun _ h => h) found
  have known := GeneralNominalVersionedMixedReady235.ready checked path frame
  refine ⟨rows,frame.occurrence_eq ▸ found,frame.occurrence_eq ▸ order,?_⟩
  intro m fit children
  obtain ⟨packet,writes⟩ := saved.1 m fit
  have effects : ClassEffects s.core a e.plan m := frame.occurrence_eq ▸ writes
  refine ⟨GeneralNominalVersionedEvidence231.evidence_node
    ⟨e.plan,GeneralNominalVersionedEvidence231.certificate_of_semantics frame matching packet known effects⟩ children,?_⟩
  intro row there
  obtain ⟨_,_,authored⟩ := member_authored each there
  exact receipt_holds writes authored

end Yulang.GeneralDeclarativeStoppedSelected340
