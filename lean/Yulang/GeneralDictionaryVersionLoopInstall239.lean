import Yulang.GeneralDictionaryVersionLoopSafety239
import Yulang.GeneralNominalVersionedMixedQuietInstall235
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryVersionLoopInstall239
open GeneralDictionaryVersionLoopSource237 (roles registry root model)
open GeneralDictionaryVersionLoopBook239 GeneralDictionaryVersionLoopFrame239
open GeneralDictionaryVersionLoopFresh239 (fresh)
open GeneralNominalVersionedMixedKernel234

noncomputable abbrev chosen (shape : Shape journal n) := effect shape (fresh n)
noncomputable abbrev installed (shape : Shape journal n) := GeneralNominalVersionedInstall232.install journal (chosen shape)

theorem classes (shape : Shape journal n) (assignment) :
 GeneralNominalVersionedEffects231.ClassEffects journal.core root (plan n) assignment := by
 apply (GeneralNominalVersionedEffects231.class_effects_iff ..).mpr
 constructor <;> intro output member <;> simp [requests_empty shape] at member

theorem common_general (shape : Shape journal n) (assignment)
 (valid : GeneralNominalVersionedJournal232.Models journal assignment)
 (packetValid : GeneralNominalVersionedPlans231.Holds (plan n) assignment) :
 GeneralNominalVersionedInstall232.InstallationModels journal (chosen shape) assignment := by
 apply (GeneralNominalVersionedMixedQuietInstall235.installation_models_iff rfl
   (GeneralNominalVersionedMixedQuietInstall235.terminal_quiet (children_empty n)) assignment).mpr
 exact ⟨valid,packetValid,GeneralNominalVersionedPlans231.head_models packetValid,classes shape _⟩

theorem common (shape : Shape journal n) (valid : GeneralNominalVersionedJournal232.Models journal model) :
 GeneralNominalVersionedInstall232.InstallationModels journal (chosen shape) model := common_general shape model valid (packet_holds n)

theorem frame_plan (shape : Shape journal n) {candidate : GeneralNominalCenters.Plan roles} {key}
 (framed : GeneralNominalVersionedEvidence231.Frame registry journal.core root key candidate) : candidate = plan n :=
 GeneralNominalVersionedFrameFunctional232.frame_plan_unique rfl shape.rawSites shape.centers framed (frame shape (fresh n))

theorem positions (valid : GeneralNominalVersionedJournal232.Models journal model) (n) :
 GeneralNominalVersionedCycles232.Safe journal (plan n) := by
 constructor
 · unfold GeneralNominalCenteredSteps.inspection
   rw [GeneralDictionaryVersionLoopFamilyPacket238.query]
   have value3 : ((3 : Fin 4) : Nat) = 3 := rfl
   simp [GeneralNominalRecursiveInspection.inspectMany,GeneralNominalRecursiveInspection.inspect,
     GeneralNominalRecursiveInspection.typeArguments,GeneralNominalRecursiveInspection.Report.visit,
     GeneralNominalRecursiveInspection.Report.append,GeneralDictionaryVersionLoopFamilySnapshot238.snapshot,
     GeneralDictionaryVersionLoopFamilyBase238.pair,GeneralDictionaryVersionLoopFamilyBase238.original,value3,
     GeneralNominalCenters.Site.observed,GeneralNominalCenters.rootSite]
   rw [GeneralNominalRecursiveInspection.inspectMany.eq_2,GeneralNominalRecursiveInspection.inspectMany.eq_2,
     GeneralNominalRecursiveInspection.inspectMany.eq_1]
   simp [GeneralNominalRecursiveInspection.inspect,GeneralNominalRecursiveInspection.Report.append]
 · exact fun entry _ => GeneralDictionaryVersionLoopSafety239.acyclic valid entry.1

theorem installable (shape : Shape journal n) (valid : GeneralNominalVersionedJournal232.Models journal model)
 (recorded : ∀ index < n, plan index ∈ journal.plans) : Installable registry journal (chosen shape) := by
 refine ⟨rfl,rfl,GeneralDictionaryVersionLoopSafety239.safe shape valid,?_,?_,?_,positions valid n,?_,model,common shape valid⟩
 · rw [shape.current]
   exact GeneralDictionaryVersionLoopFamilyCache238.point_cache allocations reservations atoms journal n _ _ _ shape.source recorded
 · change (GeneralNominalVersionedPlans231.emittedSchema (plan n)).unknown = false
   rw [GeneralDictionaryVersionLoopFamilyFull238.emitted_empty]
 · intro prior member _
   exact (shape.choice prior member).symm
 · intro candidate input framed
   change GeneralNominalVersionedEvidence231.Frame registry journal.core root candidate.packet.declaration.id candidate at framed
   cases frame_plan shape framed
   exact positions valid n

theorem installed_model (shape : Shape journal n) (valid : GeneralNominalVersionedJournal232.Models journal model) :
 GeneralNominalVersionedJournal232.Models (installed shape) model :=
 (GeneralNominalVersionedInstall232.install_models rfl).mpr (common shape valid)

theorem installed_recorded (shape : Shape journal n)
 (recorded : ∀ index < n, plan index ∈ journal.plans) : ∀ index < n+1, plan index ∈ (installed shape).plans := by
 intro index before
 by_cases last : index=n
 · subst index; exact List.mem_cons_self
 · exact List.mem_cons_of_mem _ (recorded index (by omega))

theorem step (shape : Shape journal n) (valid : GeneralNominalVersionedJournal232.Models journal model)
 (recorded : ∀ index < n, plan index ∈ journal.plans) (novel : ¬ Committed journal (plan n)) :
 Step registry root journal (installed shape) := ⟨root,.root,.install _ (installable shape valid recorded) novel⟩
end Yulang.GeneralDictionaryVersionLoopInstall239
