import Yulang.GeneralRebaseJournalMeaning271
import Yulang.GeneralDictionaryOutputDepth252

namespace Yulang.GeneralRebaseOutputDepthPocket271
open GeneralDictionaryOutputDepth252 (context root initial model initial_model)
open GeneralRebaseLocalOriginPocket271 (nodes checked inspect rootOrigin rootOrigin_sound)
open GeneralRebaseScalarSnapshot271 (journal initial_models initial_sites)
open GeneralRebaseJournalMeaning271 (SameModels)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedCycles232 (RootCycle Cyclic)

def inspected := journal context root

theorem unchanged : SameModels inspected initial := initial_models context root

theorem preserves_semantics : ∀ o, Cyclic inspected o ↔ Cyclic initial o :=
 GeneralRebaseJournalMeaning271.cyclic unchanged

theorem actual_model : Models inspected model := (unchanged model).mpr initial_model

def points (i : Fin 4) : GeneralRebaseStructuralOrigin270.Slots inspected := i

theorem old_abstains : rootOrigin initial root = none := by decide +kernel

theorem global_still_open : GeneralRebaseClosedRecordDriver271.covered inspected = false := by decide +kernel

theorem local_closed : checked inspected (points 2) = true := by decide +kernel

theorem used_slots :
 (nodes inspected (points 2)).map Fin.val = [0,2] := by decide +kernel

theorem deferred_outside : inspect inspected (.source 3) = none := by decide +kernel

theorem diagnostic : rootOrigin inspected root = some false := by decide +kernel

/-- The actual source journal of the output-depth regression has no
semantic root cycle. The inspected view was only used as a certificate;
no assertion is made about raw K2 or candidate readiness. -/
theorem actual_no_root_cycle : ¬ RootCycle initial root := by
 have reflected := rootOrigin_sound inspected ⟨model,actual_model⟩ root
 rw [diagnostic] at reflected
 exact fun found => reflected ((GeneralRebaseJournalMeaning271.root unchanged (initial_sites context root) root).mpr found)

end Yulang.GeneralRebaseOutputDepthPocket271
