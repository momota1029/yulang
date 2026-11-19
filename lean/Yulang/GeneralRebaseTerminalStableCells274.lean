import Yulang.GeneralRebaseTerminalStableSupport274
import Yulang.GeneralDictionaryRebase230Executor242
import Yulang.GeneralDictionaryRebaseEvidence230243

set_option maxRecDepth 26000
set_option maxHeartbeats 8000000
namespace Yulang.GeneralRebaseTerminalStableCells274
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedJournalFrame236 (sources models_iff)
open GeneralNominalFiniteEquationRealization236 (Entry)
open GeneralDictionaryJournalRefinement228Source (snapshot root)
open GeneralDictionaryOptionalInitial229 (registry declaration)
open GeneralDictionaryOptionalInstall229 (lo hi actual)
open GeneralDictionaryVersionedSecondInstall233 (installed)
open GeneralDictionaryRebase230Private241 (newBindings oldBindings publicAtoms isolated linked)
open GeneralDictionaryRebase230Public242 (newEntries)
open GeneralRebaseCompoundRows273 (Agrees)
open GeneralRebaseCompoundPublic273 (Fixed)
open GeneralRebaseTerminalRows274 (HasLeaf completeRows complete_agrees complete_model)
open GeneralDictionaryRebase230Service241 (ownerAt owner newBlock)
open GeneralDictionaryRebase230Scheduler242 (initial final compile discover)
open GeneralNominalRebaseExecutor242 (run)

noncomputable def stable (m : Assignment) : Assignment :=
 GeneralNominalRebaseDefinitions241.patch snapshot.seed root.identity declaration.id newBindings declaration.inputNames m

theorem entry_target (entry : Entry) (member : entry ∈ newEntries) : entry.1 = lo ∨ entry.1 = hi := by
 obtain ⟨name,listed,_,writes⟩ := (GeneralNominalRebaseDefinitions241.member_iff ..).mp member
 have zero := GeneralDictionaryRebase230Private241.named_zero listed
 subst name
 rcases writes with rfl | rfl
 · exact Or.inl rfl
 · exact Or.inr rfl

theorem terminal_hidden : lo ∉ sources installed ∧ hi ∉ sources installed :=
 GeneralRebaseTerminalStableSupport274.terminal_hidden

theorem preserves (m : Assignment) (id : Nat) (notLo : id ≠ lo) (notHi : id ≠ hi) :
 stable m id = m id := by
 apply GeneralNominalFiniteEquationRealization236.outside
 intro entry present equal
 have touched := entry_target entry present
 rw [equal] at touched
 exact touched.elim notLo notHi

theorem public_preserved (m : Assignment) : Agrees (stable m) m := by
 constructor
 · intro id small
   have l : 4 < lo := GeneralDictionaryOptionalInstall229.fresh_large 0
   have h : 4 < hi := GeneralDictionaryOptionalInstall229.fresh_large 1
   exact preserves m id (by omega) (by omega)
 · exact GeneralNominalFiniteEquationRealization236.row newEntries

theorem stable_terminal (m : Assignment) (old : Models installed m) :
 Models installed (stable m) := by
 apply (models_iff installed ?_).mp old
 intro id used
 exact (preserves m id (fun eq => terminal_hidden.1 (eq ▸ used)) (fun eq => terminal_hidden.2 (eq ▸ used))).symm

theorem terminal_atoms (m : Assignment) (valid : Models installed m) :
 PresenceNormalForm.All CommonNominalFullCarrier.model m publicAtoms := by
 have first := GeneralRebaseTerminalPublic274.final_to_first m valid
 have packet := first.2.1 GeneralDictionaryOptionalInstall229.plan (List.mem_cons_self ..)
 have ordinary := packet.2.1.1
 apply (PresenceNormalForm.all_append ..).mpr
 constructor
 · apply (GeneralNominalAllocation.cross_exact oldBindings m).mpr
   rw [← GeneralDictionaryRebase230Private241.old_report_bindings]
   exact ordinary.1
 · exact ordinary.2.2

theorem stable_block (m : Assignment) :
 PresenceNormalForm.All CommonNominalFullCarrier.model (stable m) newBlock :=
 GeneralNominalRebaseDefinitions241.merges snapshot registry root.identity declaration newBindings m isolated linked

theorem stable_store (m : Assignment) (valid : Models installed (stable m)) :
 GeneralNominalRebaseStore241.Models (run ownerAt compile discover initial).table.baseAtoms
 (run ownerAt compile discover initial).table.owners
 (run ownerAt compile discover initial).table.blocks (stable m) := by
 rw [GeneralDictionaryRebase230Executor242.run_eq_final]
 refine ⟨terminal_atoms _ valid,?_⟩
 intro key present
 cases List.mem_singleton.mp present
 rw [GeneralDictionaryRebase230Scheduler242.final_block]
 exact stable_block m

theorem agrees_trans {a b c : Assignment} (ab : Agrees a b) (bc : Agrees b c) : Agrees a c :=
 ⟨fun i h => (ab.1 i h).trans (bc.1 i h),fun i => (ab.2 i).trans (bc.2 i)⟩

def StoreChecked (m : Assignment) : Prop :=
 GeneralNominalRebaseStore241.Models (run ownerAt compile discover initial).table.baseAtoms
 (run ownerAt compile discover initial).table.owners
 (run ownerAt compile discover initial).table.blocks m

theorem joint_checked (boundary : Assignment) (fixed : Fixed boundary) :
 Agrees (stable (completeRows boundary)) boundary ∧
 Models installed (stable (completeRows boundary)) ∧
 HasLeaf (stable (completeRows boundary)) ∧ StoreChecked (stable (completeRows boundary)) := by
 have model := stable_terminal _ (complete_model boundary fixed)
 exact ⟨agrees_trans (public_preserved _) (complete_agrees boundary),model,
   GeneralDictionaryVersionedSecondInstall233.evidence model,stable_store _ model⟩

theorem exact_joint (boundary : Assignment) :
 (∃ m, Agrees m boundary ∧ Models installed m ∧ HasLeaf m ∧ StoreChecked m) ↔ Fixed boundary := by
 constructor
 · rintro ⟨m,agree,model,_,_⟩
   exact (GeneralRebaseTerminalRows274.terminal_public boundary).mp ⟨m,agree,model⟩
 · intro fixed; exact ⟨stable (completeRows boundary),joint_checked boundary fixed⟩

end Yulang.GeneralRebaseTerminalStableCells274
