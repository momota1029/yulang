import Yulang.GeneralLiveCompoundLeafSelect316

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 25000
set_option maxHeartbeats 30000000
namespace Yulang.GeneralLiveCompoundLeafInstall316
open GeneralDictionaryJournalRefinement228Source (roles root snapshot)
open GeneralLiveCompoundRegistry316 (registry sourceRegistry leaf boundary_checked)
open GeneralLiveCompoundUpperRefresh316 (upperState upper_reachable old_models)
open GeneralLiveCompoundChildSite316
open GeneralLiveCompoundLeafHead316 (packet plan)
open GeneralLiveCompoundLeafProof316 (w valid binder_exact binderId center_value)
open GeneralLiveCompoundLeafEvidence316 (holds)
open GeneralLiveCompoundLeafSelect316 (frame_plan selected class_effects ready)
open GeneralNominalVersionedJournal232 (Models Effect)
open GeneralNominalVersionedMixedKernel234 (Installable Committed Step)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

noncomputable def effect : Effect roles where
  registry := registry
  snapshot := upperState.core
  plan := plan
  frame := GeneralLiveCompoundLeafEvidence316.frame
  unique := by rw [GeneralLiveCompoundLeafEvidence316.terminal]; exact GeneralLiveCompoundLeafEvidence316.unique
  ready := ready

theorem choice : GeneralNominalCycleSteps.ChoiceCompatible upperState.core.erased.current packet := by
  intro prior present aliased
  change prior ∈ [GeneralLiveCompoundRoot316.packet] at present
  cases List.mem_singleton.mp present
  exact False.elim ((by decide +kernel : child.identity ≠ root.identity)
    (GeneralLiveCompoundAdmin316.alias_eq rfl aliased))

theorem installable : Installable registry upperState effect :=
  (GeneralNominalVersionedMixedCommon235.source_installable_iff boundary_checked upper_reachable selected
    (effect := effect) rfl rfl).mpr ⟨choice,w,valid,holds,class_effects⟩

def setValue (m : Assignment) (key : Nat) (value : Ty) : Assignment := fun n =>
  if key = n then (value,(m n).2) else m n

theorem patch_before (m : Assignment) (valid : Models upperState m) (key : Nat) (replacement : Ty)
    (outside : key ∉ GeneralDictionaryCompoundPointModel238.pool) :
    Models upperState (setValue m key replacement) := by
  apply (old_models _).mpr
  rw [GeneralMixedCompoundUpperRefresh307.models_iff,GeneralDictionaryCompoundRefresh239.models_iff,
    GeneralDictionaryCompoundPoint238.models_iff]
  have old := (old_models m).mp valid
  rw [GeneralMixedCompoundUpperRefresh307.models_iff,GeneralDictionaryCompoundRefresh239.models_iff,
    GeneralDictionaryCompoundPoint238.models_iff] at old
  refine (GeneralNominalVersionedJournalFrame236.models_iff _ ?_).mp old
  intro n member
  have h : key ≠ n := fun eq => outside (eq.symm ▸ GeneralDictionaryCompoundPointModel238.support member)
  rw [setValue,ite_eq_right h]

theorem binder_outside : binderId ∉ GeneralDictionaryCompoundPointModel238.pool := by decide +kernel

theorem not_committed : ¬ Committed upperState plan := by
  intro old
  let m := setValue w binderId .top
  have live : Models upperState m := patch_before w valid binderId .top binder_outside
  have held := (old.1 m live).1
  have fits := (GeneralNominalVersionedDiagnostic232.head_equations held).2.1 0 (List.mem_singleton_self _)
  rw [GeneralLiveCompoundLeafProof316.selected_bounds,binder_exact] at fits
  have top : (m binderId).1 = .top := by simp [m,setValue]
  rw [top] at fits
  have fixedTwo := GeneralDictionaryJournalRefinement228Source.width_two m live.1.2.1
  exact GeneralDictionaryGroundCopy218Refresh.top_no_head (.structural (.record []))
    ⟨[],rfl,subtype_trans fits.2 fixedTwo.1,GeneralNominalTopObservation.le_top _⟩

noncomputable abbrev after := GeneralNominalVersionedInstall232.install upperState effect

theorem step : Step registry root upperState after :=
  ⟨child,generated,.install effect installable not_committed⟩

theorem reachable : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles)
    sourceRegistry root after := by
  obtain ⟨start,first,path⟩ := upper_reachable
  exact ⟨start,first,.tail path step⟩

theorem models (m : Assignment) : Models after m ↔
    Models upperState m ∧ GeneralNominalVersionedPlans231.Holds plan m := by
  change Models (GeneralNominalVersionedInstall232.install upperState effect) m ↔ _
  rw [GeneralNominalVersionedInstall232.install_models (effect := effect) rfl,
    GeneralNominalVersionedMixedCommon235.installation_models_iff
      (effect := effect) boundary_checked upper_reachable rfl rfl]
  constructor
  · rintro ⟨a,b,_⟩; exact ⟨a,b⟩
  · rintro ⟨a,b⟩
    exact ⟨a,b,GeneralLiveCompoundAdmin316.leaf_classes raw_sites rfl plan⟩

theorem after_model : Models after w := (models w).mpr ⟨valid,holds⟩

end Yulang.GeneralLiveCompoundLeafInstall316
