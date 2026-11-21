import Yulang.GeneralWherePhysicalCurrentPick319

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 33000
set_option maxHeartbeats 37000000
namespace Yulang.GeneralWherePhysicalCommit319
open GeneralWhereOriginSingleSource318
open GeneralWhereOriginSingleCells318 (oldChild hi loNow sig)
open GeneralWherePhysicalCurrentRead319 (packet plan address_lo address_hi child_bounds)
open GeneralWherePhysicalCurrentModel319 (full)
open GeneralWherePhysicalCurrentPick319 (selected classes)
open GeneralWherePhysicalCurrentFrame319 (frame)
open GeneralWherePhysicalPatch319 (n compatible_update)
open GeneralWherePhysicalReobserve319 (updated)
open GeneralWherePhysicalOldInstall319 (installed)
open GeneralWherePhysicalOldHead319 (before)
open GeneralWherePhysicalActive319 (active ctx refines)
open GeneralWherePhysicalTicket319 (raw_ticket)
open GeneralWhereVersionInstall317 (Journal InstallStep install emitted Models)
open GeneralWhereVersionCompiler317 (child children)
open GeneralWhereOriginSuccessor318 (SilentChildren with_parent)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryJournalRefinement228Source (roles root)
open GeneralLiveCompoundRegistry316 (otherChild)
open GeneralNominalCenters

noncomputable abbrev newChild : Site roles := child plan otherChild sig

theorem emission : emitted plan = [newChild] := by
  have kids : GeneralWhereVersionCompiler317.children plan = [newChild.occurrence] := by
    unfold GeneralWhereVersionCompiler317.children
    rw [GeneralWherePhysicalCurrentModel319.one_emission]
    rfl
  have len := congrArg List.length (GeneralWhereVersionInstall317.ordered plan)
  rw [kids] at len
  simp only [List.length_map,List.length_singleton] at len
  obtain ⟨one,eq⟩ := List.length_eq_one_iff.mp len
  have member : one ∈ GeneralWhereVersionInstall317.emitted plan := eq ▸ List.mem_singleton_self _
  obtain ⟨clause,_,same⟩ := List.mem_map.mp member
  have visible := (GeneralCanonicalChildOrder.canonicalRequirements_perm _).mem_iff.mpr clause.property
  have named : clause.val = otherChild := List.mem_singleton.mp visible
  have sameSite : one = newChild := by
    rw [← same]
    rcases clause with ⟨clause,valid⟩
    change clause = otherChild at named
    subst clause
    rfl
  exact eq.trans (congrArg List.singleton sameSite)

theorem silent : SilentChildren plan := by
  intro s member
  rw [emission] at member
  cases List.mem_singleton.mp member
  rfl

theorem child_changed : oldChild.occurrence ≠ newChild.occurrence := by
  intro same
  have two := congrArg (fun (o : GeneralSourceDictionaries.Occurrence roles) =>
    (o.demand.arguments (0 : Fin 1)).1) same
  change (oldChild.occurrence.demand.arguments 0).1 = (newChild.occurrence.demand.arguments 0).1 at two
  rw [GeneralWhereOriginSingleCells318.exact_old,child_bounds] at two
  exact GeneralWhereOriginSingleCells318.lower_moves two

noncomputable abbrev final : Journal roles := install updated ctx plan

theorem raw : GeneralNominalState.Models active n := raw_ticket n compatible_update full

theorem models : Models final n := with_parent compatible_update raw full classes silent

theorem legacy_choice : GeneralNominalCycleSteps.ChoiceCompatible updated.mixed.core.erased.current packet := by
  intro p found
  cases found

theorem step : InstallStep sourceRegistry updated final :=
  .whereRow ctx plan boundary_checked frame selected legacy_choice refines rfl ⟨n,compatible_update,models⟩

theorem both_in_history : final.versionedWhere = [oldPlan,plan] := rfl

theorem produced : GeneralNominalSaturationState.Generated final.mixed.core.erased.current root newChild.occurrence := by
  apply GeneralWhereOriginInstall318.generated_append
  rw [← GeneralWhereVersionInstall317.ordered,emission]
  exact List.mem_cons_self

/-- Genuine isolated install → underlying nominal reobservation → isolated
mixed fresh/reused install. The last two journals share the same assignment;
this theorem does not equate the isolated writer with the existing engine. -/
theorem physical_mixed_run :
    InstallStep sourceRegistry before installed ∧
    GeneralNominalVersionedMixedKernel234.Step registry root installed.mixed updated.mixed ∧
    InstallStep sourceRegistry updated final ∧
    Models installed n ∧ Models updated n ∧ Models final n ∧
    (∀ p ∈ final.versionedWhere,
      GeneralWhereVersionSemantics317.Holds p n) ∧
    GeneralNominalSaturationState.Generated final.mixed.core.erased.current root newChild.occurrence :=
  ⟨GeneralWherePhysicalOldInstall319.step,GeneralWherePhysicalReobserve319.underlying_step,step,
    (GeneralWherePhysicalReobserve319.models_unchanged n).mp compatible_update,
    compatible_update,models,fun p h => (models.2 p h).1,produced⟩

end Yulang.GeneralWherePhysicalCommit319
