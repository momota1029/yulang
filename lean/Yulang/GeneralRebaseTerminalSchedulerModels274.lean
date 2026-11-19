import Yulang.GeneralRebaseTerminalScheduler274

set_option maxRecDepth 19500
set_option maxHeartbeats 6800000
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseTerminalSchedulerModels274
open CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (Models)
open GeneralDictionaryOptionalInstall229 (lo hi)
open GeneralDictionaryVersionedSecondInstall233 (installed)
open GeneralDictionaryRebase230Service241 (oldBlock newBlock owner)
open GeneralDictionaryRebase230Scheduler242 (initial observed final)
open GeneralNominalRebaseScheduler242 (State)
open GeneralRebaseTerminalScheduler274 (scheduler logical_cells)
open GeneralRebaseTerminalBridge274 (raw)
open GeneralRebaseTerminalMachine274 (Stage)
open GeneralRebaseTerminalDecode274 (decode stable_hi)
open GeneralRebaseCompoundRows273 (Agrees)
open GeneralRebaseCompoundPublic273 (Fixed)
open GeneralRebaseCompoundOwnerBlock273 (normalized_lo normalized_hi)
open GeneralNominalAllocation (equations)
open PresenceNormalForm (All all_append)

def beforeService (boundary : Assignment) : Assignment :=
 fun id => (if id = lo then (boundary 4).1 else (decode boundary id).1,(boundary id).2)

theorem outside (boundary : Assignment) (id : Nat) (notLo : id ≠ lo) :
 beforeService boundary id = decode boundary id := by simp [beforeService,decode,notLo]

theorem preserves (boundary : Assignment) : Agrees (beforeService boundary) boundary := by
 refine ⟨?_,fun _ => rfl⟩
 intro id small
 have big : 4 < lo := GeneralDictionaryOptionalInstall229.fresh_large 0
 exact (outside boundary id (by omega)).trans ((GeneralRebaseTerminalDecode274.agrees boundary).1 id small)

theorem still_terminal (boundary : Assignment) (known : Fixed boundary) :
 Models installed (beforeService boundary) := by
 apply (GeneralNominalVersionedJournalFrame236.models_iff installed ?_).mp
   (GeneralRebaseTerminalDecode274.terminal boundary known)
 intro id used
 exact (outside boundary id (fun eq => GeneralRebaseTerminalStableCells274.terminal_hidden.1 (eq ▸ used))).symm

theorem before_lo (boundary : Assignment) : (beforeService boundary lo).1 = (beforeService boundary 4).1 := by
 rw [(preserves boundary).1 4 (by decide)]
 simp [beforeService]

theorem before_hi (boundary : Assignment) : (beforeService boundary hi).1 = (beforeService boundary 2).1 := by
 have differs : hi ≠ lo := GeneralNominalCenteredAllocation.fresh_namespaces (by decide : (1 : Nat) ≠ 0)
 rw [outside boundary hi differs,stable_hi,
    (GeneralRebaseTerminalDecode274.agrees boundary).1 2 (by decide),(preserves boundary).1 2 (by decide)]

theorem old_body (m : Assignment) (lower : (m lo).1 = (m 4).1) (upper : (m hi).1 = (m 2).1) : All model m oldBlock := by
 let block := equations lo (.union (.var 4) (.var 4)) ++ equations hi (.inter (.var 2) (.var 2))
 have ok : All model m block := by
   unfold block
   rw [all_append,GeneralNominalCaptureMerges.equations_exact,GeneralNominalCaptureMerges.equations_exact]
   change Equivalent (m lo).1 (.union (m 4).1 (m 4).1) ∧ Equivalent (m hi).1 (.inter (m 2).1 (m 2).1)
   rw [lower,upper]
   exact ⟨⟨(normalized_lo _).2,(normalized_lo _).1⟩,⟨(normalized_hi _).2,(normalized_hi _).1⟩⟩
 change All model m (block ++ block)
 exact (all_append ..).mpr ⟨ok,ok⟩

def Store (s : State 1 1) (m : Assignment) : Prop :=
 GeneralNominalRebaseStore241.Models s.table.baseAtoms s.table.owners s.table.blocks m

theorem store_initial (boundary : Assignment) (known : Fixed boundary) : Store initial (beforeService boundary) := by
 refine ⟨GeneralRebaseTerminalStableCells274.terminal_atoms _ (still_terminal boundary known),?_⟩
 intro key chosen
 cases List.mem_singleton.mp chosen
 rw [logical_cells.1]
 exact old_body _ (before_lo boundary) (before_hi boundary)

theorem store_observed (boundary : Assignment) (known : Fixed boundary) : Store observed (beforeService boundary) := by
 refine ⟨GeneralRebaseTerminalStableCells274.terminal_atoms _ (still_terminal boundary known),?_⟩
 intro key chosen
 cases List.mem_singleton.mp chosen
 rw [logical_cells.2.1]
 exact old_body _ (before_lo boundary) (before_hi boundary)

theorem store_terminal (boundary : Assignment) (known : Fixed boundary) : Store final (decode boundary) := by
 have p := GeneralRebaseTerminalDecode274.realizes_run boundary known
 unfold GeneralRebaseTerminalStableCells274.StoreChecked at p
 rw [GeneralDictionaryRebase230Executor242.run_eq_final] at p
 exact p

theorem one_common_state (stage : Stage) (boundary : Assignment) (already : stage ≠ .source) :
 (∃ s m, scheduler stage = some s ∧ Agrees m boundary ∧ Models (raw stage) m ∧ Store s m) ↔ Fixed boundary := by
 constructor
 · rintro ⟨s,m,_,same,valid,_⟩
   exact (GeneralRebaseTerminalMachine274.after_install already boundary).mp
     ((GeneralRebaseTerminalBridge274.public_agrees stage boundary).mpr ⟨m,same,valid⟩)
 · intro known
   cases stage with
   | source => exact False.elim (already rfl)
   | installed =>
     exact ⟨initial,beforeService boundary,rfl,preserves boundary,
       GeneralRebaseTerminalPublic274.final_to_first _ (still_terminal boundary known),store_initial boundary known⟩
   | observed =>
     exact ⟨observed,beforeService boundary,rfl,preserves boundary,
       GeneralNominalVersionedInstall232.step_models rfl (still_terminal boundary known),store_observed boundary known⟩
   | terminal =>
     exact ⟨final,decode boundary,rfl,GeneralRebaseTerminalDecode274.agrees boundary,
       GeneralRebaseTerminalDecode274.terminal boundary known,store_terminal boundary known⟩

theorem not_both_blocks (m : Assignment) (real : Models installed m)
 (historical : All model m oldBlock) (current : All model m newBlock) : False := by
 have oldFacts : GeneralRebaseCompoundOwnerCapture273.PairFacts m lo hi 4 2 :=
   ((all_append ..).mp historical).1
 have newFacts : GeneralRebaseCompoundOwnerCapture273.PairFacts m lo hi 2 2 :=
   ((all_append ..).mp current).1
 have first := (GeneralRebaseCompoundOwnerCapture273.read_pair m lo hi 4 2 oldFacts).1
 have last := (GeneralRebaseCompoundOwnerCapture273.read_pair m lo hi 2 2 newFacts).1
 exact GeneralRebaseTerminalRepair274.not_equivalent_endpoints m
   (GeneralNominalVersionedInstall232.step_models rfl real)
   (GeneralDictionaryDefaultExpression209.equivalent_trans ⟨first.2,first.1⟩ last)

theorem service_changes_lower (boundary : Assignment) (known : Fixed boundary) :
 ¬ Equivalent (beforeService boundary lo).1 (decode boundary lo).1 := by
 intro same
 rw [before_lo,GeneralRebaseTerminalDecode274.stable_lo,(preserves boundary).1 4 (by decide),
   (GeneralRebaseTerminalDecode274.agrees boundary).1 2 (by decide)] at same
 have optional : Equivalent (boundary 4).1 GeneralDictionaryOptionalOutput229.value := known 4 (by decide)
 have width : Equivalent (boundary 2).1 .emptyRecord := known 2 (by decide)
 exact GeneralDictionaryOptionalOutput229.not_width
   (GeneralDictionaryDefaultExpression209.equivalent_trans ⟨optional.2,optional.1⟩
     (GeneralDictionaryDefaultExpression209.equivalent_trans same width))

end Yulang.GeneralRebaseTerminalSchedulerModels274
