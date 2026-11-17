import Yulang.GeneralNominalRebaseJournalSupport243
import Yulang.GeneralNominalRebasePublicModel242
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalRebaseDefinitionSupport244
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredFrame179 (Agree)
open GeneralNominalFiniteEquationRealization236
open GeneralNominalRebaseEscapedProjection242
open GeneralNominalRebaseJournalView243 (Journal)
def entrySources (entry : Entry) : List Nat :=
 (GeneralNominalAllocation.equations entry.1 entry.2).flatMap GeneralNominalState.atomSources
def sources (entries : List Entry) : List Nat := entries.flatMap entrySources
theorem definitions_iff (entries : List Entry) {first last : Assignment}
 (same : Agree (sources entries) first last) : Definitions entries first ↔ Definitions entries last := by
 apply forall_congr'; intro entry
 apply forall_congr'; intro member
 apply forall_congr'; intro atom
 apply forall_congr'; intro included
 apply GeneralNominalCenteredModelExtension.atom_same
 intro name present
 exact same name (List.mem_flatMap.mpr ⟨entry,member,List.mem_flatMap.mpr ⟨atom,included,present⟩⟩)
def reads (retained : List Entry) (journal : Journal) (extra : List Nat) : List Nat :=
 sources retained ++ GeneralNominalRebaseJournalSupport243.sources journal ++ extra
def Checked (fresh retained : List Entry) (journal : Journal) (extra : List Nat) : Prop :=
 ∀ entry ∈ fresh, entry.1 ∉ reads retained journal extra
def check (fresh retained : List Entry) (journal : Journal) (extra : List Nat) : Bool :=
 fresh.all (fun entry => !(reads retained journal extra).contains entry.1)
theorem check_iff (fresh retained : List Entry) (journal : Journal) (extra : List Nat) :
 check fresh retained journal extra = true ↔ Checked fresh retained journal extra := by
 simp [check,Checked]
def Models (retained : List Entry) (journal : Journal) (model : Assignment) : Prop :=
 Definitions retained model ∧ journal.Models model
theorem kept_agree (fresh retained : List Entry) (journal : Journal) (extra : List Nat)
 (checked : Checked fresh retained journal extra) {first last : Assignment}
 (kept : Preserves fresh first last) : Agree (reads retained journal extra) first last := by
 intro name present
 apply kept.1 name
 intro entry member equal
 exact checked entry member (equal ▸ present)
theorem models_iff (retained : List Entry) (journal : Journal) (extra : List Nat)
 {first last : Assignment} (same : Agree (reads retained journal extra) first last) :
 Models retained journal first ↔ Models retained journal last := by
 exact and_congr
   (definitions_iff retained (fun name present => same name (List.mem_append_left _ (List.mem_append_left _ present))))
   (GeneralNominalRebaseJournalSupport243.models_iff journal
     (fun name present => same name (List.mem_append_left _ (List.mem_append_right _ present))))
theorem activate (fresh retained : List Entry) (coherent : Coherent fresh) (external : External fresh)
 (journal : Journal) (extra : List Nat) (checked : Checked fresh retained journal extra)
 (model : Assignment) (valid : Models retained journal model) :
 Preserves fresh (patch fresh model) model ∧ Definitions fresh (patch fresh model) ∧
 Models retained journal (patch fresh model) ∧ Agree extra (patch fresh model) model := by
 have kept := patch_preserves fresh model
 have same := kept_agree fresh retained journal extra checked kept
 exact ⟨kept,patch_definitions fresh coherent external model,
   (models_iff retained journal extra same).mpr valid,
   fun name present => same name (List.mem_append_right _ present)⟩
theorem public_activation (fresh retained : List Entry) (coherent : Coherent fresh) (external : External fresh)
 (journal : Journal) (extra : List Nat) (checked : Checked fresh retained journal extra)
 (hidden : ∀ entry ∈ fresh, entry.1 ∈ privateNames) (publicModel : Assignment) :
 GeneralNominalRebasePublicModel242.Models privateNames (Models retained journal) publicModel ↔
 GeneralNominalRebasePublicModel242.Models privateNames
   (fun internal => Definitions fresh internal ∧ Models retained journal internal) publicModel := by
 constructor
 · rintro ⟨internal,publicSame,valid⟩
   obtain ⟨kept,definitions,valid,_⟩ := activate fresh retained coherent external journal extra checked internal valid
   exact ⟨patch fresh internal,GeneralNominalRebasePublicModel242.preserves_public fresh hidden kept publicSame,
     definitions,valid⟩
 · rintro ⟨internal,publicSame,_,valid⟩
   exact ⟨internal,publicSame,valid⟩
end Yulang.GeneralNominalRebaseDefinitionSupport244
