import Yulang.GeneralRebaseGuardedCache283

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 30000
set_option maxHeartbeats 11000000
namespace Yulang.GeneralRebaseOptionalDelta283
open GeneralDictionaryVersionedNames231 (freshName oldVersionName)
open GeneralDictionaryVersionedPointStage233 (point)
open GeneralDictionaryVersionedSecondInstall233 (effect)
open GeneralDictionaryOptionalInstall229 (plan)
open GeneralRebaseOptionalOverwrite282 (point_reached)
open GeneralNominalVersionedAggregateLedger236 (packetEntries)
open GeneralNominalVersionedMixedSeedLedger237 (Recorded)
open GeneralRebaseInstallCache283 (Valid add)
open GeneralRebaseHistoryOrder282 (history member_exact)
open GeneralRebaseProspectiveDelta283 (ext_history)
open GeneralPresenceDefinitionRewrite244 (Entry)
open GeneralRebaseFreshDelta283 (NoBackReads member_exact)
open GeneralRebaseIncrementalHistory283 (changes)
open GeneralPresenceUsedSupport245 (typedReads)

def oldLo : Entry Nat := (oldVersionName 0,.union (.var 4) (.var 4))
def oldHi : Entry Nat := (oldVersionName 1,.inter (.var 2) (.var 2))
def newLo : Entry Nat := (freshName 0,.union (.var 2) (.var 2))
def newHi : Entry Nat := (freshName 1,.inter (.var 2) (.var 2))

theorem old_packet (e : Entry Nat) : e ∈ packetEntries plan.packet ↔ e = oldLo ∨ e = oldHi := by
  constructor
  · intro seen
    obtain ⟨name,named,_,shape⟩ := (GeneralNominalVersionedAggregateRealization236.member_iff ..).mp seen
    change name ∈ ([0,0] : List Nat) at named
    have eq : name = 0 := by simpa using named
    subst name
    rw [GeneralDictionaryOptionalInstall229.bindings_exact] at shape
    exact shape
  · intro shape
    apply (GeneralNominalVersionedAggregateRealization236.member_iff ..).mpr
    refine ⟨0,by change 0 ∈ ([0,0] : List Nat); simp,?_,?_⟩
    · rw [GeneralDictionaryOptionalInstall229.bindings_exact]; decide
    · rw [GeneralDictionaryOptionalInstall229.bindings_exact]
      exact shape

theorem next_packet (e : Entry Nat) : e ∈ packetEntries effect.plan.packet ↔ e = newLo ∨ e = newHi := by
  constructor
  · intro seen
    obtain ⟨name,named,_,shape⟩ := (GeneralNominalVersionedAggregateRealization236.member_iff ..).mp seen
    change name ∈ ([0,0] : List Nat) at named
    have eq : name = 0 := by simpa using named
    subst name
    unfold effect at shape
    rw [GeneralDictionaryVersionedPoint233.bindings_exact] at shape
    exact shape
  · intro shape
    apply (GeneralNominalVersionedAggregateRealization236.member_iff ..).mpr
    refine ⟨0,by change 0 ∈ ([0,0] : List Nat); simp,?_,?_⟩
    · unfold effect
      rw [GeneralDictionaryVersionedPoint233.bindings_exact]; decide
    · unfold effect
      rw [GeneralDictionaryVersionedPoint233.bindings_exact]
      exact shape

theorem before_contents {defs : List (Entry Nat)} (valid : Valid defs point) (row : Entry Nat) :
    row ∈ defs ↔ row = oldLo ∨ row = oldHi := by
  rw [valid.content,GeneralRebaseHistoryOrder282.member_exact point_reached]
  change row ∈ packetEntries plan.packet ++ [] ↔ _
  rw [List.append_nil]
  exact old_packet row

theorem after_contents {defs : List (Entry Nat)} (valid : Valid defs point) (row : Entry Nat) :
    row ∈ add defs effect ↔ (row = newLo ∨ row = newHi) ∨ row ∈ defs := by
  have recorded := GeneralNominalVersionedMixedSeedLedger237.reachable point_reached
  have next := GeneralRebaseInstallCache283.add_valid (effect := effect) valid recorded rfl
  rw [next.content,ext_history recorded rfl,next_packet,← valid.content]

theorem novel {defs : List (Entry Nat)} (valid : Valid defs point) :
    newLo.1 ∉ defs.map Prod.fst ∧ newHi.1 ∉ defs.map Prod.fst := by
  constructor <;> intro found
  all_goals obtain ⟨old,present,hit⟩ := List.mem_map.mp found
  all_goals rcases (before_contents valid old).mp present with rfl|rfl
  all_goals revert hit; decide +kernel

theorem a_new_entry {defs : List (Entry Nat)} (valid : Valid defs point) (e : Entry Nat)
    (used : e ∈ add defs effect) (fresh : e.1 ∉ defs.map Prod.fst) : e = newLo ∨ e = newHi :=
  ((after_contents valid e).mp used).resolve_right
    (fun present => fresh (List.mem_map.mpr ⟨e,present,rfl⟩))

theorem a_prior_entry {defs : List (Entry Nat)} (valid : Valid defs point) (e : Entry Nat)
    (used : e ∈ add defs effect) (old : e.1 ∈ defs.map Prod.fst) : e = oldLo ∨ e = oldHi := by
  rcases (after_contents valid e).mp used with (rfl|rfl)|prior
  · exact False.elim ((novel valid).1 old)
  · exact False.elim ((novel valid).2 old)
  · exact (before_contents valid e).mp prior

theorem clean {defs : List (Entry Nat)} (valid : Valid defs point) :
    NoBackReads (defs.map Prod.fst) (add defs effect) := by
  intro before inside old post present fresh
  rcases a_prior_entry valid before inside old with rfl|rfl <;>
    rcases a_new_entry valid post present fresh with rfl|rfl <;> decide +kernel

theorem selected {defs : List (Entry Nat)} (valid : Valid defs point) (e : Entry Nat) :
    e ∈ changes defs (add defs effect) ↔ e = newLo ∨ e = newHi := by
  rw [GeneralRebaseFreshDelta283.member_exact (clean valid)]
  constructor
  · rintro ⟨member,fresh⟩
    exact a_new_entry valid e member fresh
  · rintro (rfl|rfl)
    · exact ⟨(after_contents valid _).mpr (Or.inl (Or.inl rfl)),(novel valid).1⟩
    · exact ⟨(after_contents valid _).mpr (Or.inl (Or.inr rfl)),(novel valid).2⟩

end Yulang.GeneralRebaseOptionalDelta283
