import Yulang.GeneralRebaseDisplayEvidenceWatch284

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseNoLiteralTrim284
open GeneralRebaseFutureWatch284 (trim)
open GeneralRebaseHistoryOrder282 (history decode compatible)
open GeneralRebaseRawWatchFailure284 (omitted_unsound ignores_written)
open GeneralRebasePrivateStore282 (Joint)
open GeneralPresenceDefinitionRewrite244 (Entry)
open GeneralPresenceOrderedBlock247 (solve put)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (model)
open GeneralNominalVersionedJournal232 (Models)
open GeneralRebaseSliceJournal283 (journalReads)

theorem trim_all (word : List Nat) (defs : List (Entry Nat))
    (covers : ∀ e ∈ defs, e.1 ∈ word) :
    trim word defs = defs := by
  apply List.filter_eq_self.mpr
  intro e used
  simpa using covers e used

theorem necessary {defs : List (Entry Nat)} {watch : List Nat} {Full Slots : Assignment → Prop}
    (fails : ∀ row ∈ defs, row.1 ∉ watch → ∃ base, Full base ∧ ¬ Slots base)
    (exactAt : ∀ base, Full base ↔ Slots base) : trim watch defs = defs := by
  apply trim_all
  intro row used
  classical
  apply Classical.byContradiction
  intro missing
  obtain ⟨base,held,lost⟩ := fails row used missing
  exact lost ((exactAt base).mp held)

namespace Version
open GeneralDictionaryVersionLoopSource237 (registry root snapshot)
open GeneralDictionaryVersionLoopIteration239 (state stages)
open GeneralRebaseLoopBase282.Version (decode_reach)
open GeneralRebaseVersionErasureFailure284 (determined any_omitted_counterexample)

theorem necessary_models (n : Nat) (watch : List Nat)
    (exactAt : ∀ base, Models (state n) (decode (state n) base) ↔
       Models (state n) (solve model (trim watch (history (state n))) base)) :
    trim watch (history (state n)) = history (state n) :=
  necessary (any_omitted_counterexample n watch) exactAt

theorem joint_counter (n : Nat) (watch : List Nat) (row : Entry Nat)
    (recorded : row ∈ history (state n)) (missing : row.1 ∉ watch) :
    ∃ probe, Joint (state n) registry root (.node 0 []) (decode (state n) probe) ∧
      ¬ Joint (state n) registry root (.node 0 []) (solve model (trim watch (history (state n))) probe) := by
  let base := GeneralDictionaryVersionLoopSource237.model
  obtain ⟨front,listed,forces⟩ := determined n row recorded
  have bound : front ≤ (GeneralRebaseMixedOwnedTrace277.raw (state n)).seed := by
    rw [GeneralRebaseLoopView282.Version.seed_exact n]
    simp only [List.mem_cons,List.not_mem_nil,or_false] at listed
    rcases listed with rfl|rfl <;> decide
  have visible := (GeneralRebaseWholeJournal282.source_visibility (decode_reach n) [front]
    (fun _ d => List.mem_singleton.mp d ▸ bound)).1 front (List.mem_singleton_self _)
  have notBottom : ¬ CommonNominalFullCarrier.Subtype (base front).1 .bottom := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at listed
    rcases listed with rfl|rfl <;> exact GeneralRebaseRawWatchFailure284.nominal_not_bottom
  have facts := omitted_unsound (decode_reach n) base (stages n).valid watch row recorded missing front visible notBottom forces
  refine ⟨put model base row.1 .bottom,⟨facts.1,?_⟩,fun h => facts.2 h.1⟩
  rw [ignores_written (decode_reach n) base row recorded .bottom]
  have payload := GeneralRebaseVersionEvidence278.enter_leaf n base (GeneralDictionaryVersionLoopBook239.packet_holds n)
  exact (GeneralNominalRebaseEvidenceProjection243.evidence_congruent registry (state n).core root _
    _ _ (compatible (decode_reach n) (stages n).valid)).mpr payload

theorem necessary_joint (n : Nat) (watch : List Nat)
    (exactAt : ∀ base, Joint (state n) registry root (.node 0 []) (decode (state n) base) ↔
       Joint (state n) registry root (.node 0 []) (solve model (trim watch (history (state n))) base)) :
    trim watch (history (state n)) = history (state n) :=
  necessary (joint_counter n watch) exactAt

end Version

namespace Loose
open GeneralDictionaryLooseLoopSource240 (registry root snapshot)
open GeneralDictionaryLooseIterationIteration240 (state stages)
open GeneralRebaseLoopBase282.Loose (decode_reach)
open GeneralRebaseLooseErasureFailure284 (determined any_omitted_counterexample)

theorem necessary_models (n : Nat) (watch : List Nat)
    (exactAt : ∀ base, Models (state n) (decode (state n) base) ↔
       Models (state n) (solve model (trim watch (history (state n))) base)) :
    trim watch (history (state n)) = history (state n) :=
  necessary (any_omitted_counterexample n watch) exactAt

theorem joint_counter (n : Nat) (watch : List Nat) (row : Entry Nat)
    (recorded : row ∈ history (state n)) (missing : row.1 ∉ watch) :
    ∃ probe, Joint (state n) registry root (.node 0 []) (decode (state n) probe) ∧
      ¬ Joint (state n) registry root (.node 0 []) (solve model (trim watch (history (state n))) probe) := by
  let base := GeneralDictionaryLooseLoopSource240.model
  obtain ⟨front,listed,forces⟩ := determined n row recorded
  have bound : front ≤ (GeneralRebaseMixedOwnedTrace277.raw (state n)).seed := by
    rw [GeneralRebaseLoopView282.Loose.seed_exact n]
    simp only [List.mem_cons,List.not_mem_nil,or_false] at listed
    rcases listed with rfl|rfl <;> decide
  have visible := (GeneralRebaseWholeJournal282.source_visibility (decode_reach n) [front]
    (fun _ d => List.mem_singleton.mp d ▸ bound)).1 front (List.mem_singleton_self _)
  have notBottom : ¬ CommonNominalFullCarrier.Subtype (base front).1 .bottom := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at listed
    rcases listed with rfl|rfl <;> exact GeneralRebaseRawWatchFailure284.nominal_not_bottom
  have facts := omitted_unsound (decode_reach n) base (stages n).valid watch row recorded missing front visible notBottom forces
  refine ⟨put model base row.1 .bottom,⟨facts.1,?_⟩,fun h => facts.2 h.1⟩
  rw [ignores_written (decode_reach n) base row recorded .bottom]
  have payload := GeneralRebaseLooseEvidence278.enter_leaf n base (GeneralDictionaryLooseIterationBook240.packet_holds n)
  exact (GeneralNominalRebaseEvidenceProjection243.evidence_congruent registry (state n).core root _
    _ _ (compatible (decode_reach n) (stages n).valid)).mpr payload

theorem necessary_joint (n : Nat) (watch : List Nat)
    (exactAt : ∀ base, Joint (state n) registry root (.node 0 []) (decode (state n) base) ↔
       Joint (state n) registry root (.node 0 []) (solve model (trim watch (history (state n))) base)) :
    trim watch (history (state n)) = history (state n) :=
  necessary (joint_counter n watch) exactAt

end Loose

end Yulang.GeneralRebaseNoLiteralTrim284
