import Yulang.GeneralRebaseNominalWindow269
import Yulang.GeneralRebaseOriginWindowFixture269
import Yulang.GeneralRebaseCompilerInputs269

namespace Yulang.GeneralRebaseNominalWindowFixture269
open GeneralRebaseOriginWindowFixture269 (journal childOrigin keyOrigin equality equality_sound journal_models matchOrigin not_literal_forward)
open GeneralNominalProgressObstruction (root model)
open GeneralRebaseNominalOrigin269 (Raw)
open GeneralRebaseOriginCycles268 (Window Sound)
open GeneralNominalVersionedCycles232 (Cyclic Equal)
open GeneralRebasePartialBool268 (Answer Reflect)

def indices (_ : Fin 1) : Fin (Raw journal).base.slots := ⟨0,by decide +kernel⟩

theorem checked : GeneralRebaseNominalWindow269.check journal indices = true := by decide +kernel

def current : Window 1 := GeneralRebaseNominalWindow269.window journal indices equality

theorem tested : Sound journal current ∧ GeneralRebaseOriginQuotient269.Forward journal current.point :=
 GeneralRebaseNominalWindow269.window_sound journal indices equality equality_sound checked ⟨model,journal_models⟩

def query (o : GeneralNominalRecursiveInspection.Origin) : Answer :=
 GeneralRebaseOriginExecutable269.cyclic current matchOrigin (fun _ => true) (fun _ => false) o

theorem query_sound (o : GeneralNominalRecursiveInspection.Origin) : Reflect (Cyclic journal o) (query o) := by
 apply GeneralRebaseOriginExecutable269.with_semantic_closure current tested.1 matchOrigin _ tested.2
 intro i
 exact equality_sound o keyOrigin

theorem exact_child : query childOrigin = some true := by decide +kernel

theorem exact_root : GeneralRebaseVersionedK2Probe268.rootOrigin journal (root 0) query = some true := by decide +kernel

/-- Raw descriptor data, a graph-tight covering check and partial Equal
evidence recover the journal's actual root recurrence. Neither the list
of complete head tests nor the origin edges were preassigned. -/
theorem root_cycle : GeneralNominalVersionedCycles232.RootCycle journal (root 0) := by
 have h := GeneralRebaseVersionedK2Probe268.rootOrigin_sound journal (root 0) query query_sound
 rw [exact_root] at h
 exact h

end Yulang.GeneralRebaseNominalWindowFixture269
