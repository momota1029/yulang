import Yulang.GeneralRebaseAliasFamily283

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 30000
set_option maxHeartbeats 9800000
namespace Yulang.GeneralRebaseVersionAliases283
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedAggregateLedger236 (packetEntries)
open GeneralNominalVersionedAggregateRealization236 (member_iff)
open GeneralNominalVersionedMixedSeedLedger237 (entries)
open GeneralRebaseHistoryOrder282 (history ordered member_exact decode)
open GeneralPresenceDefinitionRewrite244 (Entry)
open GeneralRebaseAliasFamily283 (Family lowerRow upperRow)
open GeneralRebaseAliasMemo283 (Aliases cache root assignment)
open GeneralDictionaryVersionLoopNames238 (lower upper lower_above upper_above)
open GeneralDictionaryVersionLoopIteration239 (state stages)
open GeneralDictionaryVersionLoopBook239 (packet plan)
open GeneralRebaseLoopBase282.Version (decode_reach old_plan)
open GeneralNominalCommonBridge (Assignment)
open GeneralPresenceModelCongruence245 (Compatible)
open CommonNominalFullCarrier (model)

theorem packet_shape (i : Nat) (e : Entry Nat) :
    e ∈ packetEntries (packet i) ↔ e = lowerRow lower i ∨ e = upperRow upper lower i := by
  constructor
  · intro seen
    obtain ⟨name,named,_,shape⟩ := (member_iff ..).mp seen
    change name ∈ ([0,0] : List Nat) at named
    have eq : name = 0 := by simpa using named
    subst name
    rw [GeneralDictionaryVersionLoopFamilyPacket238.bindings_exact] at shape
    exact shape
  · intro eq
    apply (member_iff ..).mpr
    refine ⟨0,by change 0 ∈ ([0,0] : List Nat); simp,?_,?_⟩
    · rw [GeneralDictionaryVersionLoopFamilyPacket238.bindings_exact]; change 2 ≠ 1; decide
    · rw [GeneralDictionaryVersionLoopFamilyPacket238.bindings_exact]
      exact eq

theorem history_shape (n : Nat) (e : Entry Nat) :
    e ∈ history (state n) ↔ ∃ i < n, e = lowerRow lower i ∨ e = upperRow upper lower i := by
  rw [member_exact (decode_reach n) e]
  constructor
  · intro seen
    obtain ⟨q,qMem,fact⟩ := List.mem_flatMap.mp seen
    obtain ⟨i,less,rfl⟩ := old_plan n q qMem
    exact ⟨i,less,(packet_shape i e).mp fact⟩
  · rintro ⟨i,less,eq⟩
    exact List.mem_flatMap.mpr ⟨plan i,(stages n).recorded i less,(packet_shape i e).mpr eq⟩

theorem family (n : Nat) : Family (history (state n)) n 2 2 lower upper lower := by
  refine ⟨history_shape n,rfl,(fun _ _ => Or.inl rfl),?_,?_,(ordered _).2.2⟩
  all_goals
    intro e found
    obtain ⟨i,_,rfl|rfl⟩ := (history_shape n e).mp found
    · have hi := lower_above i
      change lower (i+1) ≠ _
      omega
    · have hi := upper_above i
      change upper i ≠ _
      omega

theorem canonical (n : Nat) : ∃ memo, cache (history (state n)) [] = some memo ∧
    (∀ i ≤ n, root memo (lower i) = 2) ∧
    (∀ i < n, root memo (upper i) = 2) ∧
    ∀ base : Assignment, Compatible model (assignment base memo) (decode (state n) base) := by
  obtain ⟨memo,made⟩ := GeneralRebaseAliasFamily283.compiled (family n)
  refine ⟨memo,made,GeneralRebaseAliasFamily283.lower_root (family n) made,?_,?_⟩
  · intro i small
    exact (GeneralRebaseAliasFamily283.upper_root (family n) made i small).1 rfl
  · exact fun base => GeneralRebaseAliasMemo283.exact _ base _ made

end Yulang.GeneralRebaseVersionAliases283
