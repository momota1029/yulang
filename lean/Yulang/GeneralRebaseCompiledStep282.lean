import Yulang.GeneralRebaseCompiledInstall282

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseCompiledStep282
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedMixedProgressSplit236 (Reachable reachable_step)
open GeneralRebaseMixedCounts277 (Actual)
open GeneralRebaseCompiledInstall282 (NewInstall OldInstall same_install)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralRebaseChartStep281 (Chart Strict)
open GeneralRebasePhaseKeys281 (Codec Added)
open GeneralRebasePhaseMachine281 (Step)

variable {roles : Roles.RoleDecls} {r : Registry} {root : Occurrence roles}
  {before after start : State roles}

def ExistingNonInstall (r : Registry) (root : Occurrence roles) (before after : State roles) : Prop :=
  Actual r root before after ∧ after.plans.length = before.plans.length

def Driver (r : Registry) (root : Occurrence roles) (before after : State roles) : Prop :=
  Reachable r root before ∧ (ExistingNonInstall r root before after ∨ NewInstall r root before after)

theorem old_split (actual : Actual r root before after) :
    ExistingNonInstall r root before after ∨ OldInstall r root before after := by
  obtain ⟨focus,generated,actionAt⟩ := actual
  cases actionAt with
  | administrative action =>
    exact Or.inl ⟨⟨_,generated,.administrative action⟩,by cases action <;> rfl⟩
  | refresh _ context cert id member old new =>
    exact Or.inl ⟨⟨_,generated,.refresh _ context cert id member old new⟩,rfl⟩
  | merge a b inA inB equal novel =>
    exact Or.inl ⟨⟨_,generated,.merge a b inA inB equal novel⟩,rfl⟩
  | install e enabled novel =>
    exact Or.inr ⟨e,generated,enabled,novel,rfl⟩

theorem raw (h : Driver r root before after) : Actual r root before after := by
  rcases h.2 with quiet | installed
  · exact quiet.1
  · obtain ⟨e,generated,enabled,novel,rfl⟩ := (same_install h.1).mp installed
    exact ⟨_,generated,.install e enabled novel⟩

theorem driver_exact (reached : Reachable r root before) :
    Driver r root before after ↔ Actual r root before after := by
  refine ⟨raw,fun h => ⟨reached,?_⟩⟩
  exact (old_split h).imp (fun q => q) (same_install reached).mpr

theorem driver_path (reached : Reachable r root start) :
    B4Target.Steps (Driver r root) start after ↔ B4Target.Steps (Actual r root) start after := by
  constructor
  · intro path
    induction path with
    | refl => exact .refl
    | tail path edge ih => exact .tail ih (raw edge)
  · intro path
    induction path with
    | refl => exact .refl
    | @tail pre out walk edge ih =>
      have next : Reachable r root pre := B4TargetV5.reachable_steps _ reached walk
      exact .tail ih ((driver_exact next).mpr edge)

def Guarded (chart : Chart F V) (codec : Codec roles Q) (r : Registry) (root : Occurrence roles)
    (before after : State roles) : Prop :=
  Driver r root before after ∧
    ((after.plans.length = before.plans.length ∨ Strict chart before after) ∨ Added codec before after)

theorem guarded_raw {chart : Chart F V} {codec : Codec roles Q}
    (step : Guarded chart codec r root before after) : Step chart codec r root before after := by
  exact step.2.elim (fun quiet => Or.inl ⟨raw step.1,quiet⟩) (fun phase => Or.inr ⟨raw step.1,phase⟩)

theorem guarded_exact {chart : Chart F V} {codec : Codec roles Q} (reached : Reachable r root before) :
    Guarded chart codec r root before after ↔ Step chart codec r root before after := by
  refine ⟨guarded_raw,?_⟩
  intro step
  exact ⟨(driver_exact reached).mpr (GeneralRebasePhaseMachine281.raw step),
    step.elim (fun based => Or.inl based.2) (fun phase => Or.inr phase.2)⟩

theorem guarded_accessible (chart : Chart F V) (codec : Codec roles Q)
    (init : (boundary roles).Initial r root start) :
    Acc (fun after before => Guarded chart codec r root before after) start :=
  Subrelation.accessible (fun move => guarded_raw move)
    (GeneralRebasePhaseMachine281.accessible chart codec init)

end Yulang.GeneralRebaseCompiledStep282
