import Yulang.GeneralRebaseTerminalAlias274

set_option maxRecDepth 24000
set_option maxHeartbeats 7700000
namespace Yulang.GeneralRebaseTerminalDecode274
open CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (Models)
open GeneralDictionaryVersionedSecondInstall233 (installed)
open GeneralDictionaryOptionalInstall229 (lo hi actual)
open GeneralRebaseTerminalAlias274 (sourceId normalize normalize_valid bounded)
open GeneralRebaseTerminalTypePool274 (pool covered)
open GeneralRebaseTerminalStableCells274 (terminal_hidden StoreChecked terminal_atoms)
open GeneralRebaseTerminalRows274 (completeRows complete_model complete_agrees HasLeaf)
open GeneralRebaseCompoundPublic273 (Fixed)
open GeneralRebaseCompoundRows273 (Agrees)
open GeneralRebaseCompoundOwnerBlock273 (normalized_lo normalized_hi)
open GeneralDictionaryRebase230Service241 (newBlock)
open GeneralNominalAllocation (equations)
open PresenceNormalForm (All all_append)

/-- No type is read from an arbitrary private assignment. The only
readback is a fixed finite source table; all row components stay literal. -/
def decode (boundary : Assignment) : Assignment :=
 fun id => (if id = lo ∨ id = hi then (boundary 2).1
   else if id ∈ pool then (boundary (sourceId id)).1 else .bottom,(boundary id).2)

theorem small_in_pool (id : Nat) (small : id ≤ 4) : id ∈ pool := by
 have enumerate : id = 0 ∨ id = 1 ∨ id = 2 ∨ id = 3 ∨ id = 4 := by omega
 rcases enumerate with rfl | rfl | rfl | rfl | rfl <;> simp [pool]

theorem agrees (boundary : Assignment) : Agrees (decode boundary) boundary := by
 constructor
 · intro id small
   have low : 4 < lo := GeneralDictionaryOptionalInstall229.fresh_large 0
   have high : 4 < hi := GeneralDictionaryOptionalInstall229.fresh_large 1
   have outside : ¬ (id = lo ∨ id = hi) := by omega
   simp [decode,outside,small_in_pool id small,GeneralRebaseTerminalAlias274.public_id id small]
 · intro id; rfl

theorem independent (a b : Assignment) (same : Agrees a b) : decode a = decode b := by
 funext id
 apply Prod.ext
 · change (if id = lo ∨ id = hi then (a 2).1 else if id ∈ pool then (a (sourceId id)).1 else .bottom) =
     (if id = lo ∨ id = hi then (b 2).1 else if id ∈ pool then (b (sourceId id)).1 else .bottom)
   by_cases fixed : id = lo ∨ id = hi
   · simpa [fixed] using congrArg Prod.fst (same.1 2 (by decide))
   · by_cases inside : id ∈ pool
     · simpa [fixed,inside] using congrArg Prod.fst (same.1 _ (bounded id inside))
     · simp [fixed,inside]
       rfl
 · exact same.2 id

theorem stable_lo (boundary : Assignment) : (decode boundary lo).1 = (decode boundary 2).1 := by
 rw [(agrees boundary).1 2 (by decide)]
 simp [decode]

theorem stable_hi (boundary : Assignment) : (decode boundary hi).1 = (decode boundary 2).1 := by
 rw [(agrees boundary).1 2 (by decide)]
 simp [decode]

theorem terminal (boundary : Assignment) (known : Fixed boundary) : Models installed (decode boundary) := by
 have real := normalize_valid _ (complete_model boundary known)
 apply (GeneralNominalVersionedJournalFrame236.models_iff installed ?_).mp real
 intro id used
 have publicId := bounded id (covered used)
 have unused : ¬ (id = lo ∨ id = hi) := by
   rintro (rfl | rfl)
   · exact terminal_hidden.1 used
   · exact terminal_hidden.2 used
 apply Prod.ext
 · change (completeRows boundary (sourceId id)).1 = (decode boundary id).1
   rw [(complete_agrees boundary).1 _ publicId]
   simp [decode,unused,covered used]
 · rfl

theorem current_body (m : Assignment) (one : (m lo).1 = (m 2).1) (two : (m hi).1 = (m 2).1) :
 All model m newBlock := by
 have equations : All model m
   (equations lo (.union (.var 2) (.var 2)) ++ equations hi (.inter (.var 2) (.var 2))) := by
   rw [all_append,GeneralNominalCaptureMerges.equations_exact,GeneralNominalCaptureMerges.equations_exact]
   change Equivalent (m lo).1 (.union (m 2).1 (m 2).1) ∧
      Equivalent (m hi).1 (.inter (m 2).1 (m 2).1)
   rw [one,two]
   exact ⟨⟨(normalized_lo _).2,(normalized_lo _).1⟩,⟨(normalized_hi _).2,(normalized_hi _).1⟩⟩
 let block := GeneralNominalAllocation.equations lo (.union (.var 2) (.var 2)) ++ GeneralNominalAllocation.equations hi (.inter (.var 2) (.var 2))
 change All model m (block ++ block)
 exact (all_append ..).mpr ⟨equations,equations⟩

theorem realizes_run (boundary : Assignment) (known : Fixed boundary) : StoreChecked (decode boundary) := by
 unfold StoreChecked
 rw [GeneralDictionaryRebase230Executor242.run_eq_final]
 refine ⟨terminal_atoms _ (terminal boundary known),?_⟩
 intro key member
 cases List.mem_singleton.mp member
 rw [GeneralDictionaryRebase230Scheduler242.final_block]
 exact current_body _ (stable_lo boundary) (stable_hi boundary)

theorem positive (boundary : Assignment) (known : Fixed boundary) :
 Agrees (decode boundary) boundary ∧ Models installed (decode boundary) ∧
 HasLeaf (decode boundary) ∧ StoreChecked (decode boundary) :=
 ⟨agrees boundary,terminal boundary known,
   GeneralDictionaryVersionedSecondInstall233.evidence (terminal boundary known),realizes_run boundary known⟩

theorem exact (boundary : Assignment) :
 Fixed boundary ↔ Models installed (decode boundary) ∧ HasLeaf (decode boundary) ∧ StoreChecked (decode boundary) := by
 constructor
 · intro fixed; exact (positive boundary fixed).2
 · rintro ⟨held,_,_⟩
   exact (GeneralRebaseTerminalRows274.terminal_public boundary).mp ⟨decode boundary,agrees boundary,held⟩

end Yulang.GeneralRebaseTerminalDecode274
