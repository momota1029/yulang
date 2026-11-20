import Yulang.GeneralRebaseRawWatchBound284

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 30000
set_option maxHeartbeats 11000000
namespace Yulang.GeneralRebaseVersionWatchLower284
open GeneralDictionaryVersionLoopBook239 (atoms atoms_next packet)
open GeneralDictionaryVersionLoopIteration239 (state stages)
open GeneralRebaseRawWatchBound284 (raw atom_in_packet all_keys_required)
open GeneralNominalVersionedAggregateLedger236 (packetEntries)
open GeneralPresenceDefinitionRewrite244 (Entry)
open PresenceNormalForm (Atom)
open GeneralRebaseHistoryOrder282 (history)
open GeneralRebaseVersionAliases283 (family packet_shape history_shape)
open GeneralRebaseVersionDelta283 (distinct)

theorem persistence (i n : Nat) (earlier : i < n) (row : Entry Nat)
    (definedAt : row ∈ packetEntries (packet i)) :
    Atom.tyLe (.var row.1) row.2 ∈ atoms n := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [atoms_next]
    by_cases new : i = n
    · subst i
      exact List.mem_append_right _ (atom_in_packet _ _ definedAt)
    · exact List.mem_append_left _ (ih (by omega))

theorem history_read (n : Nat) (row : Entry Nat) (mem : row ∈ history (state n)) :
    Atom.tyLe (.var row.1) row.2 ∈ (raw (state n)).ordinary := by
  obtain ⟨i,less,shape⟩ := (history_shape n row).mp mem
  unfold raw
  rw [(stages n).shape.current]
  exact persistence i n less row ((packet_shape i row).mpr shape)

theorem no_short_watch (n : Nat) (watch : List Nat)
    (covers : GeneralRebaseSliceJournal283.journalReads (state n) ⊆ watch) :
    2*n ≤ watch.length :=
  all_keys_required (family n) distinct (state n) watch covers (history_read n)

theorem impossible_uniform (watch : List Nat) :
    ¬ ∀ n, GeneralRebaseSliceJournal283.journalReads (state n) ⊆ watch := by
  intro all
  have tooLarge := no_short_watch (watch.length+1) watch (all _)
  omega

end Yulang.GeneralRebaseVersionWatchLower284
