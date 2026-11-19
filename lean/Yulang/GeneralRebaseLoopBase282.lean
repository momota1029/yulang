import Yulang.GeneralRebaseFixedBasis282
import Yulang.GeneralRebaseLoopReplay281

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 27000
set_option maxHeartbeats 11000000
namespace Yulang.GeneralRebaseLoopBase282
open GeneralRebaseHistoryOrder282 (history decode ordered member_exact)
open GeneralNominalVersionedMixedSeedLedger237 (entries)
open GeneralNominalVersionedAggregateLedger236 (packetEntries)
open GeneralNominalVersionedAggregateRealization236 (member_iff)
open GeneralRebaseTermCopy281 (Write Respects)
open GeneralNominalCommonBridge (Assignment)
open GeneralRebaseLiveOwner282 (newest lookup_first lookup_spec newest_iff)
open GeneralRebaseLiveStore282 (live)
open GeneralRebaseWholeStore282 (store expression_exact)
open GeneralRebasePrivateKey282 (port)
open GeneralRebasePhaseKeys281 (owner)
open GeneralRebaseTermAggregate281 (writes)
open CommonNominalFullCarrier (Equivalent model subtype_refl subtype_trans)
open GeneralRebaseAggregateCollapse281 (equivalence_retarget)
open GeneralNominalCenters (Plan)
open GeneralPresenceDefinitionRewrite244 (Entry block)
open GeneralNominalAllocation (equations)
open PresenceNormalForm (All)

theorem union_same (a : CommonNominalFullCarrier.Ty) : Equivalent (.union a a) a :=
  GeneralRebaseCompoundOwnerBlock273.normalized_lo a

theorem inter_same (a : CommonNominalFullCarrier.Ty) : Equivalent (.inter a a) a :=
  GeneralRebaseCompoundOwnerBlock273.normalized_hi a

theorem equiv_trans {a b c : CommonNominalFullCarrier.Ty} (x : Equivalent a b) (y : Equivalent b c) : Equivalent a c :=
  ⟨subtype_trans x.1 y.1,subtype_trans y.2 x.2⟩

theorem lists_all {α : Type} (f : α → List Write) (xs : List α) (m : Assignment) :
    Respects (xs.flatMap f) m ↔ ∀ a ∈ xs, Respects (f a) m := by
  constructor
  · intro good a used row member
    exact good row (List.mem_flatMap.mpr ⟨a,used,member⟩)
  · intro good row used
    obtain ⟨a,member,found⟩ := List.mem_flatMap.mp used
    exact good a member row found

namespace Version
open GeneralDictionaryVersionLoopIteration239 (stages state)
open GeneralDictionaryVersionLoopBook239 (packet plan)
open GeneralDictionaryVersionLoopNames238 (lower upper)
open GeneralDictionaryVersionLoopSource237 (declaration roles)

theorem indexed_plan (n : Nat) : (state (n+1)).plans = plan n :: (state n).plans := rfl

theorem old_plan (n : Nat) (q : Plan roles) (seen : q ∈ (state n).plans) :
    ∃ i < n, q = plan i := by
  induction n with
  | zero => cases seen
  | succ n ih =>
    rw [indexed_plan n] at seen
    rcases List.mem_cons.mp seen with rfl|rest
    · exact ⟨n,by omega,rfl⟩
    · obtain ⟨i,bound,eq⟩ := ih rest
      exact ⟨i,by omega,eq⟩

theorem newest_eq (n : Nat) (q : Plan roles) :
    q ∈ newest (state (n+1)).plans ↔ q = plan n := by
  constructor
  · intro known
    obtain ⟨i,_,rfl⟩ := old_plan (n+1) q (GeneralRebaseLiveOwner282.newest_subset _ known)
    have same : owner (plan i) = owner (plan n) := rfl
    have listed := (newest_iff _ _).mp known
    rw [indexed_plan n,same,lookup_first] at listed
    exact (Option.some.inj listed).symm
  · rintro rfl
    apply (newest_iff _ _).mpr
    rw [indexed_plan n,lookup_first]

theorem entry_lo (i : Nat) :
    (lower (i+1),.union (.var (lower i)) (.var (lower i))) ∈ packetEntries (packet i) := by
  apply (member_iff ..).mpr
  refine ⟨0,by change 0 ∈ ([0,0] : List Nat); simp,?_,?_⟩
  · rw [GeneralDictionaryVersionLoopFamilyPacket238.bindings_exact]
    change 2 ≠ 1
    decide
  · left
    rw [GeneralDictionaryVersionLoopFamilyPacket238.bindings_exact]
    rfl

theorem decode_reach (n : Nat) :
    GeneralNominalVersionedMixedProgressSplit236.Reachable GeneralDictionaryVersionLoopSource237.sourceRegistry GeneralDictionaryVersionLoopSource237.root (state n) :=
  GeneralDictionaryVersionLoopIteration239.reachable n

theorem lower_chain (n i : Nat) (within : i ≤ n) (m : Assignment) :
    Equivalent (decode (state n) m (lower i)).1 (m 2).1 := by
  induction i with
  | zero =>
    have keep : GeneralRebaseWholeJournal282.Observable (state n) [2] :=
      (GeneralRebaseWholeJournal282.source_visibility (decode_reach n) [2] (by
        intro id listed
        cases List.mem_singleton.mp listed
        change 2 ≤ (state n).core.erased.current.context.state.seed
        rw [GeneralDictionaryVersionLoopIteration239.stages n |>.shape.current]
        change 2 ≤ 3
        decide)).1
    have agreement := GeneralRebaseWholeJournal282.preserves_reads keep m 2 (List.mem_singleton_self _)
    have equal : (decode (state n) m (lower 0)).1 = (m 2).1 := congrArg Prod.fst agreement
    rw [equal]
    exact ⟨subtype_refl _,subtype_refl _⟩
  | succ i ih =>
    let row : Entry Nat := (lower (i+1),.union (.var (lower i)) (.var (lower i)))
    have member : row ∈ history (state n) :=
      (member_exact (decode_reach n) row).mpr (List.mem_flatMap.mpr ⟨plan i,(stages n).recorded i (by omega),entry_lo i⟩)
    have whole := GeneralPresenceOrderedBlock247.block_satisfied model
      GeneralPresenceCommonLaws245.common_laws.refl (history (state n)) (ordered (state n)).2.2 m
    have localEq := (GeneralNominalCaptureMerges.equations_exact (decode (state n) m) row.1 row.2).mp (by
      intro atom used
      exact whole atom (List.mem_flatMap.mpr ⟨row,member,used⟩))
    have step : Equivalent (decode (state n) m (lower (i+1))).1 (decode (state n) m (lower i)).1 :=
      equiv_trans localEq (union_same _)
    exact equiv_trans step (ih (by omega))

end Version

namespace Loose
open GeneralDictionaryLooseIterationIteration240 (stages state)
open GeneralDictionaryLooseIterationBook240 (packet plan)
open GeneralDictionaryLooseFamilyNames240 (lower upper)
open GeneralDictionaryLooseLoopSource240 (declaration roles)

theorem indexed_plan (n : Nat) : (state (n+1)).plans = plan n :: (state n).plans := rfl

theorem old_plan (n : Nat) (q : Plan roles) (seen : q ∈ (state n).plans) :
    ∃ i < n, q = plan i := by
  induction n with
  | zero => cases seen
  | succ n ih =>
    rw [indexed_plan n] at seen
    rcases List.mem_cons.mp seen with rfl|rest
    · exact ⟨n,by omega,rfl⟩
    · obtain ⟨i,bound,eq⟩ := ih rest
      exact ⟨i,by omega,eq⟩

theorem newest_eq (n : Nat) (q : Plan roles) :
    q ∈ newest (state (n+1)).plans ↔ q = plan n := by
  constructor
  · intro known
    obtain ⟨i,_,rfl⟩ := old_plan (n+1) q (GeneralRebaseLiveOwner282.newest_subset _ known)
    have same : owner (plan i) = owner (plan n) := rfl
    have listed := (newest_iff _ _).mp known
    rw [indexed_plan n,same,lookup_first] at listed
    exact (Option.some.inj listed).symm
  · rintro rfl
    apply (newest_iff _ _).mpr
    rw [indexed_plan n,lookup_first]

theorem entry_lo (i : Nat) :
    (lower (i+1),.union (.var (lower i)) (.var (lower i))) ∈ packetEntries (packet i) := by
  apply (member_iff ..).mpr
  refine ⟨0,by change 0 ∈ ([0,0] : List Nat); simp,?_,?_⟩
  · rw [GeneralDictionaryLooseFamilyPacket240.bindings_exact]
    change 2 ≠ 1
    decide
  · left
    rw [GeneralDictionaryLooseFamilyPacket240.bindings_exact]
    rfl

theorem decode_reach (n : Nat) :
    GeneralNominalVersionedMixedProgressSplit236.Reachable GeneralDictionaryLooseLoopSource240.sourceRegistry GeneralDictionaryLooseLoopSource240.root (state n) :=
  GeneralNominalPointTransport240.reachable_old (GeneralDictionaryLooseIterationIteration240.reachable n)

theorem lower_chain (n i : Nat) (within : i ≤ n) (m : Assignment) :
    Equivalent (decode (state n) m (lower i)).1 (m 2).1 := by
  induction i with
  | zero =>
    have keep : GeneralRebaseWholeJournal282.Observable (state n) [2] :=
      (GeneralRebaseWholeJournal282.source_visibility (decode_reach n) [2] (by
        intro id listed
        cases List.mem_singleton.mp listed
        change 2 ≤ (state n).core.erased.current.context.state.seed
        rw [GeneralDictionaryLooseIterationIteration240.stages n |>.shape.current]
        change 2 ≤ 4
        decide)).1
    have agreement := GeneralRebaseWholeJournal282.preserves_reads keep m 2 (List.mem_singleton_self _)
    have equal : (decode (state n) m (lower 0)).1 = (m 2).1 := congrArg Prod.fst agreement
    rw [equal]
    exact ⟨subtype_refl _,subtype_refl _⟩
  | succ i ih =>
    let row : Entry Nat := (lower (i+1),.union (.var (lower i)) (.var (lower i)))
    have member : row ∈ history (state n) :=
      (member_exact (decode_reach n) row).mpr (List.mem_flatMap.mpr ⟨plan i,(stages n).recorded i (by omega),entry_lo i⟩)
    have whole := GeneralPresenceOrderedBlock247.block_satisfied model
      GeneralPresenceCommonLaws245.common_laws.refl (history (state n)) (ordered (state n)).2.2 m
    have localEq := (GeneralNominalCaptureMerges.equations_exact (decode (state n) m) row.1 row.2).mp (by
      intro atom used
      exact whole atom (List.mem_flatMap.mpr ⟨row,member,used⟩))
    have step : Equivalent (decode (state n) m (lower (i+1))).1 (decode (state n) m (lower i)).1 :=
      equiv_trans localEq (union_same _)
    exact equiv_trans step (ih (by omega))

end Loose

end Yulang.GeneralRebaseLoopBase282
