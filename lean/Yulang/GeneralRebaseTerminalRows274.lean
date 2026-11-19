import Yulang.GeneralRebaseTerminalRowFrame274
import Yulang.GeneralDictionaryVersionedSecondStable233

set_option maxRecDepth 21000
set_option maxHeartbeats 6500000
namespace Yulang.GeneralRebaseTerminalRows274
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralDictionaryJournalRefinement228Source (roles root)
open GeneralDictionaryOptionalInitial229 (registry declaration)
open GeneralDictionaryVersionedInitialFrame233 (before)
open GeneralDictionaryVersionedPointStage233 (point)
open GeneralDictionaryVersionedSecondInstall233 (installed)
open GeneralRebaseTerminalPublic274 (first final_fixed point_fixed first_fixed complete complete_types complete_terminal)
open GeneralRebaseCompoundPublic273 (Fixed)
open GeneralRebaseCompoundRows273 (Agrees)
open GeneralRebaseCompoundRowsMeaning273 (Public)
open GeneralRebaseCompoundSourceTypes273 (PublicSource)
open GeneralNominalVersionedEvidence231 (Evidence)
open GeneralRebaseRowIrrelevance273 (SameTypes)

noncomputable def completeRows (boundary : Assignment) : Assignment :=
 fun id => ((complete boundary id).1,(boundary id).2)

theorem complete_agrees (boundary : Assignment) : Agrees (completeRows boundary) boundary :=
 ⟨fun id small => Prod.ext (complete_types boundary id small) rfl,fun _ => rfl⟩

theorem complete_model (boundary : Assignment) (fixed : Fixed boundary) :
 Models installed (completeRows boundary) := by
 have same : SameTypes (complete boundary) (completeRows boundary) := fun _ => rfl
 exact (GeneralRebaseTerminalRowFrame274.terminal_row_free same).mp (complete_terminal boundary fixed)

theorem before_models (m : Assignment) : Models before m ↔ PublicSource m :=
 GeneralRebaseCompoundSourceTypes273.before_exact m

theorem before_public (boundary : Assignment) : Public before boundary ↔ PublicSource boundary := by
 constructor
 · rintro ⟨m,agree,held⟩
   exact (GeneralRebaseCompoundSourceTypes273.source_depends_on_types m boundary
      (fun id small => congrArg Prod.fst (agree.1 id small))).mp ((before_models m).mp held)
 · intro source
   exact ⟨boundary,⟨fun _ _ => rfl,fun _ => rfl⟩,(before_models boundary).mpr source⟩

theorem first_public (boundary : Assignment) : Public first boundary ↔ Fixed boundary := by
 constructor
 · rintro ⟨m,agree,held⟩ id small
   rw [← agree.1 id small]; exact first_fixed m held id small
 · intro fixed
   exact ⟨completeRows boundary,complete_agrees boundary,
     GeneralRebaseTerminalPublic274.final_to_first _ (complete_model boundary fixed)⟩

theorem point_public (boundary : Assignment) : Public point boundary ↔ Fixed boundary :=
 (exists_congr (fun m => and_congr Iff.rfl (GeneralDictionaryVersionedPointStage233.models_iff m))).trans
  (first_public boundary)

theorem terminal_public (boundary : Assignment) : Public installed boundary ↔ Fixed boundary := by
 constructor
 · rintro ⟨m,agree,held⟩ id small
   rw [← agree.1 id small]; exact final_fixed m held id small
 · intro fixed; exact ⟨completeRows boundary,complete_agrees boundary,complete_model boundary fixed⟩

def HasLeaf (m : Assignment) : Prop :=
 Evidence registry installed.core m root (.node declaration.id [])

theorem completed_leaf (boundary : Assignment) (known : Fixed boundary) :
 HasLeaf (completeRows boundary) :=
 GeneralDictionaryVersionedSecondInstall233.evidence (complete_model boundary known)

theorem terminal_leaf_exact (boundary : Assignment) :
 (∃ m, Agrees m boundary ∧ Models installed m ∧ HasLeaf m) ↔ Fixed boundary := by
 constructor
 · rintro ⟨m,agree,valid,_⟩
   exact (terminal_public boundary).mp ⟨m,agree,valid⟩
 · intro known
   exact ⟨completeRows boundary,complete_agrees boundary,complete_model boundary known,completed_leaf boundary known⟩

theorem terminal_positive_at_every_boundary (boundary : Assignment) (known : Fixed boundary) :
 (∃ m, Agrees m boundary ∧ Models installed m ∧ HasLeaf m) ∧
 ∀ next, ¬ GeneralNominalVersionedKernel232.Step registry root installed next :=
 ⟨(terminal_leaf_exact boundary).mpr known,GeneralDictionaryVersionedSecondStable233.halted⟩

end Yulang.GeneralRebaseTerminalRows274
