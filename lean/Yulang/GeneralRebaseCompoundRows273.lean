import Yulang.GeneralRebaseCompoundFiniteMeaning273
import Yulang.GeneralRebaseTypeOnlyAtoms273
import Yulang.GeneralNominalVersionedMixedMaterialization237

set_option maxRecDepth 22000
set_option maxHeartbeats 5000000
namespace Yulang.GeneralRebaseCompoundRows273
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedPlans231
open GeneralDictionaryCompoundFrame238 (before installed effect)
open GeneralDictionaryCompoundSource238 (checked sourceRegistry declaration)
open GeneralDictionaryJournalRefinement228Source (root snapshot)
open GeneralDictionaryCompoundPacket238 (plan packet)
open GeneralRebaseRowIrrelevance273 (SameTypes)
open GeneralRebaseTypeOnlyAtoms273 (atomTypeOnly all_iff)
open GeneralRebaseCompoundSourceTypes273 (before_exact source_depends_on_types)
open GeneralNominalVersionedMixedMaterialization237 (Residual)

def atoms := GeneralNominalVersionedAllocation231.merges snapshot packet.registry root.identity declaration packet.bindings
def checks := GeneralNominalRecursiveInspection.selfChecks snapshot (GeneralNominalPacketSupport.report packet)

theorem merges_type_only : atoms.all atomTypeOnly = true := by decide +kernel
theorem checks_type_only : checks.all atomTypeOnly = true := by decide +kernel

theorem compatible (same : SameTypes first last) :
 GeneralNominalAllocation.Compatible packet.bindings first ↔
 GeneralNominalAllocation.Compatible packet.bindings last := by
 unfold GeneralNominalAllocation.Compatible
 exact forall_congr' fun a => forall_congr' fun _ => forall_congr' fun b => forall_congr' fun _ =>
   forall_congr' fun _ => by rw [same a.2.1,same b.2.2]

theorem ordinary (same : SameTypes first last) : Ordinary packet first ↔ Ordinary packet last := by
 unfold Ordinary
 exact and_congr (compatible same)
   (and_congr (all_iff same atoms merges_type_only) (all_iff same checks checks_type_only))

theorem old (same : SameTypes first last) : Models before first ↔ Models before last := by
 rw [before_exact first,before_exact last]
 exact source_depends_on_types first last (fun id _ => same id)

theorem source (same : SameTypes first last) :
 GeneralNominalState.Models snapshot first ↔ GeneralNominalState.Models snapshot last := by
 have exactSource (m : Assignment) : GeneralNominalState.Models snapshot m ↔ GeneralRebaseCompoundSourceTypes273.PublicSource m :=
   ⟨GeneralRebaseCompoundSourceTypes273.source_reads m,GeneralRebaseCompoundSourceTypes273.source_write m⟩
 exact (exactSource first).trans ((source_depends_on_types first last (fun id _ => same id)).trans (exactSource last).symm)

theorem head (same : SameTypes first last) : HeadModels packet first ↔ HeadModels packet last := by
 unfold HeadModels
 rw [private_models_iff,private_models_iff]
 exact and_congr (and_congr (source same) (ordinary same))
   (GeneralRebaseRowIrrelevance273.projection same _ _)

theorem residual (same : SameTypes first last) : Residual before effect first ↔ Residual before effect last := by
 unfold Residual
 apply and_congr (old same)
 apply and_congr (head same)
 apply and_congr (GeneralRebaseRowIrrelevance273.head_schema same plan plan.headSchema)
 apply and_congr (GeneralRebaseRowIrrelevance273.schema same plan (emittedSchema plan))
 apply and_congr
 · exact forall_congr' fun clause => forall_congr' fun _ => forall_congr' fun valid =>
    GeneralRebaseRowIrrelevance273.schema same plan (childSchema plan clause valid)
 · exact GeneralRebaseRowIrrelevance273.live same before.core root plan

theorem installed_row_free (same : SameTypes first last) :
 Models installed first ↔ Models installed last := by
 have exact (m : Assignment) : Models installed m ↔ Residual before effect m :=
   (GeneralNominalVersionedInstall232.install_models rfl).trans
     (GeneralNominalVersionedMixedMaterialization237.installation_models_iff
       (registry := sourceRegistry) ⟨rfl,checked⟩ GeneralDictionaryCompoundStep238.initial_reachable rfl rfl)
 exact (exact first).trans ((residual same).trans (exact last).symm)

def Agrees (internal publicAssignment : Assignment) : Prop :=
 (∀ id ≤ 4, internal id = publicAssignment id) ∧ (∀ id, (internal id).2 = (publicAssignment id).2)

noncomputable def completeRows (boundary : Assignment) : Assignment :=
 fun id => ((GeneralRebaseCompoundPublic273.complete boundary id).1,(boundary id).2)

theorem complete_rows (boundary : Assignment) : Agrees (completeRows boundary) boundary :=
 ⟨fun id small => Prod.ext (GeneralRebaseCompoundPublic273.complete_types boundary id small) rfl,fun _ => rfl⟩

theorem complete_valid (boundary : Assignment) (fixed : GeneralRebaseCompoundPublic273.Fixed boundary) :
 Models installed (completeRows boundary) := by
 have same : SameTypes (GeneralRebaseCompoundPublic273.complete boundary) (completeRows boundary) := fun _ => rfl
 exact (installed_row_free same).mp (GeneralRebaseCompoundPublic273.complete_valid boundary fixed)

theorem public_exact (boundary : Assignment) :
 (∃ m, Agrees m boundary ∧ Models installed m) ↔ GeneralRebaseCompoundPublic273.Fixed boundary := by
 constructor
 · rintro ⟨m,agree,valid⟩
   exact (GeneralRebaseCompoundPublic273.public_exact boundary).mp
     ⟨m,fun id small => congrArg Prod.fst (agree.1 id small),valid⟩
 · intro fixed
   exact ⟨completeRows boundary,complete_rows boundary,complete_valid boundary fixed⟩

end Yulang.GeneralRebaseCompoundRows273
