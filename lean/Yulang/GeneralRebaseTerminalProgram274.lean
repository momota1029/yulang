import Yulang.GeneralRebaseTerminalSchedulerModels274

set_option maxRecDepth 21000
set_option maxHeartbeats 6700000
namespace Yulang.GeneralRebaseTerminalProgram274
open GeneralNominalCandidates (Context)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)
open GeneralDictionaryJournalRefinement228Source (context root roles)
open GeneralDictionaryOptionalInitial229 (registry sourceRegistry declaration)
open GeneralDictionaryVersionedInitialFrame233 (before)
open GeneralDictionaryVersionedPointStage233 (point)
open GeneralDictionaryVersionedSecondInstall233 (installed)
open GeneralNominalVersionedJournal232 (Models)
open GeneralRebaseTerminalMachine274 (Stage next owner)
open GeneralRebaseTerminalObservation274 (installFrom observeFrom)
open GeneralRebaseTerminalActivation274 (finish)
open GeneralRebaseTerminalRows274 (HasLeaf)
open GeneralRebaseTerminalStableCells274 (StoreChecked)
open GeneralRebaseTerminalPayload274 (ViewEvidence accepts)

def run (initialContext observed : Context) : Option Payload :=
 match installFrom initialContext,observeFrom observed with
 | some .installed,some step =>
   match next step (.service owner) with
   | some .terminal => some (.node declaration.id [])
   | _ => none
 | _,_ => none

theorem computed : run context point.core.erased.current.context = some (.node declaration.id []) := by
 unfold run
 rw [GeneralRebaseTerminalObservation274.install_computed,GeneralRebaseTerminalObservation274.observed_computed]
 rfl

theorem no_replay_without_observation : run context context = none := by
 unfold run
 rw [GeneralRebaseTerminalObservation274.install_computed,GeneralRebaseTerminalObservation274.rejects_unrevised]

theorem exact_output (initialContext observed : Context) (dict : Payload) (successful : run initialContext observed = some dict) :
 dict = .node declaration.id [] := by
 unfold run at successful
 split at successful
 · split at successful
   · exact (Option.some.inj successful).symm
   · contradiction
 · contradiction

theorem source_executed (m : Assignment) (valid : Models before m) :
 run context point.core.erased.current.context = some (.node declaration.id []) ∧
 B4Target.Steps (GeneralNominalVersionedKernel232.Step registry root) before installed ∧
 Models installed (finish m) ∧ HasLeaf (finish m) ∧ StoreChecked (finish m) :=
 ⟨computed,GeneralDictionaryVersionedSecondStep233.path,GeneralRebaseTerminalActivation274.finished m valid⟩

theorem source_verified_view (m : Assignment) (valid : Models before m) :
 ∃ result, run context point.core.erased.current.context = some result ∧
 Models installed (finish m) ∧ ViewEvidence (finish m) result ∧
 StoreChecked (finish m) ∧
 (∀ id < 4, finish m id = m id) ∧
 (finish m 4).1 = GeneralDictionaryOptionalOutput229.value ∧
 (∀ id, (finish m id).2 = (m id).2) := by
 have checked := GeneralRebaseTerminalActivation274.finished m valid
 refine ⟨.node declaration.id [],computed,checked.1,?_,checked.2.2,
   GeneralRebaseTerminalActivation274.finish_public m⟩
 exact (GeneralRebaseTerminalPayload274.view_exact _ checked.1 _).mp rfl

end Yulang.GeneralRebaseTerminalProgram274
