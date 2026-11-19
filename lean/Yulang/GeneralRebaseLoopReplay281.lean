import Yulang.GeneralRebaseReplayCriterion281
import Yulang.GeneralRebasePhaseLoop281
import Yulang.GeneralDictionaryVersionLoopFamilyFresh238
import Yulang.GeneralDictionaryLooseFamilyFresh240
import Yulang.GeneralNominalPointTransport240

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 11000000
namespace Yulang.GeneralRebaseLoopReplay281
open GeneralRebaseAggregateTags281 (Tag tags collectTags tag fixed versioned)
open GeneralRebaseAggregateCompile281 (repeated)
open GeneralRebaseAggregateLift281 (sourceView)
open GeneralRebaseActualReplay281 (fixedState projected_actual_replacement)
open GeneralRebasePortProjection280 (Project)
open GeneralRebasePortCopy280 (Apart)
open GeneralNominalState (Models Known atomSources)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedInstallation231 (replayPlan)

namespace Version
open GeneralDictionaryVersionLoopBook239 (packet plan context reservations atoms reserved_next)
open GeneralDictionaryVersionLoopNames238 (lower upper lower_above upper_above separate injective upper_injective)
open GeneralDictionaryVersionLoopSource237 (sourceRegistry root)
open GeneralDictionaryVersionLoopIteration239 (state reachable stages)

def rows (n : Nat) : List Tag :=
  [⟨0,false,lower n⟩,⟨0,true,lower n⟩,⟨0,false,lower n⟩,⟨0,true,lower n⟩]

theorem tags_exact (n : Nat) : tags (packet n) = some (rows n) := by
  change collectTags (packet n) [0,0] = _
  simp [collectTags,tag,GeneralDictionaryVersionLoopFamilyPacket238.bindings_exact,
    GeneralDictionaryVersionLoopNames238.repeated,GeneralNominalAllocation.occurrences,repeated,rows]

theorem versioned_exact (n : Nat) :
    (rows n).map (versioned (packet n)) =
      [(lower (n+1),lower n),(upper n,lower n),(lower (n+1),lower n),(upper n,lower n)] := by
  unfold rows
  simp only [List.map_cons,List.map_nil,versioned,GeneralRebaseAggregateSupport281.endKey]
  simp only [GeneralDictionaryVersionLoopFamilyPacket238.bindings_exact]
  rfl

theorem same_slots (n : Nat) :
    ((rows n).map (fixed (packet n))).map Prod.fst =
      ((rows 0).map (fixed (packet 0))).map Prod.fst := rfl

theorem reserve_exact (n : Nat) :
    GeneralNominalVersionedInstallation231.reserved (packet n) =
      [lower (n+1),upper n,lower (n+1),upper n] := by
  unfold GeneralNominalVersionedInstallation231.reserved GeneralNominalVersionedAllocation231.reserved
  simp only [GeneralDictionaryVersionLoopFamilyPacket238.bindings_exact]
  rfl

theorem reserve_provenance (n name : Nat) (member : name ∈ reservations n) :
    ∃ index < n, name = lower (index+1) ∨ name = upper index := by
  induction n with
  | zero => cases member
  | succ n ih =>
    rw [reserved_next,reserve_exact] at member
    rcases List.mem_append.mp member with before|today
    · obtain ⟨i,small,id⟩ := ih before
      exact ⟨i,by omega,id⟩
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at today
      rcases today with h|h|h|h
      · exact ⟨n,by omega,Or.inl h⟩
      · exact ⟨n,by omega,Or.inr h⟩
      · exact ⟨n,by omega,Or.inl h⟩
      · exact ⟨n,by omega,Or.inr h⟩

theorem next_lower_absent (n : Nat) : lower (n+1) ∉ sourceView (packet n) := by
  intro member
  change lower (n+1) ∈ (List.ofFn (GeneralDictionaryVersionLoopFamilyBase238.source n) ++
    List.ofFn (GeneralDictionaryVersionLoopFamilyBase238.source n) ++ reservations n ++ (atoms n).flatMap atomSources) at member
  simp only [List.mem_append,List.mem_ofFn] at member
  rcases member with (((⟨slot,eq⟩|⟨slot,eq⟩)|old)|atomsMember)
  · exact GeneralDictionaryVersionLoopFamilyFresh238.next_lower_not_base n slot eq.symm
  · exact GeneralDictionaryVersionLoopFamilyFresh238.next_lower_not_base n slot eq.symm
  · obtain ⟨i,small,eq|eq⟩ := reserve_provenance n _ old
    · have index := injective eq
      omega
    · exact separate n i eq
  · rcases GeneralDictionaryVersionLoopBookSupport239.atoms_provenance n _ atomsMember with eq|⟨i,small,eq|eq|eq⟩
    · have larger := lower_above n; omega
    · have index := injective eq
      omega
    · have index := injective eq
      omega
    · exact separate n i eq

theorem next_upper_absent (n : Nat) : upper n ∉ sourceView (packet n) := by
  intro member
  change upper n ∈ (List.ofFn (GeneralDictionaryVersionLoopFamilyBase238.source n) ++
    List.ofFn (GeneralDictionaryVersionLoopFamilyBase238.source n) ++ reservations n ++ (atoms n).flatMap atomSources) at member
  simp only [List.mem_append,List.mem_ofFn] at member
  rcases member with (((⟨slot,eq⟩|⟨slot,eq⟩)|old)|atomsMember)
  · exact GeneralDictionaryVersionLoopFamilyFresh238.next_upper_not_base n slot eq.symm
  · exact GeneralDictionaryVersionLoopFamilyFresh238.next_upper_not_base n slot eq.symm
  · obtain ⟨i,small,eq|eq⟩ := reserve_provenance n _ old
    · exact separate i n eq.symm
    · have index := upper_injective eq
      omega
  · exact GeneralDictionaryVersionLoopBookSupport239.fresh_upper n n (Nat.le_refl _) atomsMember

theorem versioned_private (n : Nat) : Apart ((rows n).map (versioned (packet n))) (sourceView (packet n)) := by
  rw [versioned_exact n]
  intro row member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl
  · exact next_lower_absent n
  · exact next_upper_absent n
  · exact next_lower_absent n
  · exact next_upper_absent n

theorem raw_context (n : Nat) : (packet n).context.state = GeneralRebaseMixedOwnedTrace277.raw (state n) :=
  congrArg GeneralNominalCandidates.Context.state (stages n).shape.current.symm

theorem projected_equal (n : Nat) (m : Assignment) :
    Project (sourceView (packet n)) (Models (replayPlan (plan n)).packet.context.state) m ↔
      Project (sourceView (packet n)) (Models (fixedState (packet n) ((rows n).map (fixed (packet n))))) m :=
  projected_actual_replacement (plan n) (reachable n) (raw_context n) (tags_exact n) (versioned_private n) m

theorem known_equal (n id : Nat) :
    Known (replayPlan (plan n)).packet.context.state id ↔
      Known (fixedState (packet n) ((rows n).map (fixed (packet n)))) id :=
  GeneralRebaseActualReplay281.fixed_known _ _ _

end Version

namespace Loose
open GeneralDictionaryLooseIterationBook240 (packet plan context reservations atoms reserved_next)
open GeneralDictionaryLooseFamilyNames240 (lower upper lower_above upper_above separate injective upper_injective)
open GeneralDictionaryLooseLoopSource240 (sourceRegistry root)
open GeneralDictionaryLooseIterationIteration240 (state reachable stages)

def rows (n : Nat) : List Tag :=
  [⟨0,false,lower n⟩,⟨0,true,4⟩,⟨0,false,lower n⟩,⟨0,true,4⟩]

theorem tags_exact (n : Nat) : tags (packet n) = some (rows n) := by
  change collectTags (packet n) [0,0] = _
  simp [collectTags,tag,GeneralDictionaryLooseFamilyPacket240.bindings_exact,
    GeneralDictionaryLooseFamilyNames240.repeated,GeneralNominalAllocation.occurrences,repeated,rows]

theorem versioned_exact (n : Nat) :
    (rows n).map (versioned (packet n)) =
      [(lower (n+1),lower n),(upper n,4),(lower (n+1),lower n),(upper n,4)] := by
  unfold rows
  simp only [List.map_cons,List.map_nil,versioned,GeneralRebaseAggregateSupport281.endKey]
  simp only [GeneralDictionaryLooseFamilyPacket240.bindings_exact]
  rfl

theorem same_slots (n : Nat) :
    ((rows n).map (fixed (packet n))).map Prod.fst =
      ((rows 0).map (fixed (packet 0))).map Prod.fst := rfl

theorem reserve_exact (n : Nat) :
    GeneralNominalVersionedInstallation231.reserved (packet n) =
      [lower (n+1),upper n,lower (n+1),upper n] := by
  unfold GeneralNominalVersionedInstallation231.reserved GeneralNominalVersionedAllocation231.reserved
  simp only [GeneralDictionaryLooseFamilyPacket240.bindings_exact]
  rfl

theorem reserve_provenance (n name : Nat) (member : name ∈ reservations n) :
    ∃ index < n, name = lower (index+1) ∨ name = upper index := by
  induction n with
  | zero => cases member
  | succ n ih =>
    rw [reserved_next,reserve_exact] at member
    rcases List.mem_append.mp member with before|today
    · obtain ⟨i,small,id⟩ := ih before
      exact ⟨i,by omega,id⟩
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at today
      rcases today with h|h|h|h
      · exact ⟨n,by omega,Or.inl h⟩
      · exact ⟨n,by omega,Or.inr h⟩
      · exact ⟨n,by omega,Or.inl h⟩
      · exact ⟨n,by omega,Or.inr h⟩

theorem next_lower_absent (n : Nat) : lower (n+1) ∉ sourceView (packet n) := by
  intro member
  change lower (n+1) ∈ (List.ofFn (GeneralDictionaryLooseFamilyBase240.source n) ++
    List.ofFn (GeneralDictionaryLooseFamilyBase240.source n) ++ reservations n ++ (atoms n).flatMap atomSources) at member
  simp only [List.mem_append,List.mem_ofFn] at member
  rcases member with (((⟨slot,eq⟩|⟨slot,eq⟩)|old)|atomsMember)
  · exact GeneralDictionaryLooseFamilyFresh240.next_lower_not_base n slot eq.symm
  · exact GeneralDictionaryLooseFamilyFresh240.next_lower_not_base n slot eq.symm
  · obtain ⟨i,small,eq|eq⟩ := reserve_provenance n _ old
    · have index := injective eq
      omega
    · exact separate n i eq
  · rcases GeneralDictionaryLooseIterationBookSupport240.atoms_provenance n _ atomsMember with eq|eq|⟨i,small,eq|eq|eq⟩
    · have larger := lower_above n; omega
    · have larger := lower_above n; omega
    · have index := injective eq
      omega
    · have index := injective eq
      omega
    · exact separate n i eq

theorem next_upper_absent (n : Nat) : upper n ∉ sourceView (packet n) := by
  intro member
  change upper n ∈ (List.ofFn (GeneralDictionaryLooseFamilyBase240.source n) ++
    List.ofFn (GeneralDictionaryLooseFamilyBase240.source n) ++ reservations n ++ (atoms n).flatMap atomSources) at member
  simp only [List.mem_append,List.mem_ofFn] at member
  rcases member with (((⟨slot,eq⟩|⟨slot,eq⟩)|old)|atomsMember)
  · exact GeneralDictionaryLooseFamilyFresh240.next_upper_not_base n slot eq.symm
  · exact GeneralDictionaryLooseFamilyFresh240.next_upper_not_base n slot eq.symm
  · obtain ⟨i,small,eq|eq⟩ := reserve_provenance n _ old
    · exact separate i n eq.symm
    · have index := upper_injective eq
      omega
  · exact GeneralDictionaryLooseIterationBookSupport240.fresh_upper n n (Nat.le_refl _) atomsMember

theorem versioned_private (n : Nat) : Apart ((rows n).map (versioned (packet n))) (sourceView (packet n)) := by
  rw [versioned_exact n]
  intro row member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl
  · exact next_lower_absent n
  · exact next_upper_absent n
  · exact next_lower_absent n
  · exact next_upper_absent n

theorem raw_context (n : Nat) : (packet n).context.state = GeneralRebaseMixedOwnedTrace277.raw (state n) :=
  congrArg GeneralNominalCandidates.Context.state (stages n).shape.current.symm

theorem projected_equal (n : Nat) (m : Assignment) :
    Project (sourceView (packet n)) (Models (replayPlan (plan n)).packet.context.state) m ↔
      Project (sourceView (packet n)) (Models (fixedState (packet n) ((rows n).map (fixed (packet n))))) m :=
  projected_actual_replacement (plan n) (GeneralNominalPointTransport240.reachable_old (reachable n)) (raw_context n) (tags_exact n) (versioned_private n) m

theorem known_equal (n id : Nat) :
    Known (replayPlan (plan n)).packet.context.state id ↔
      Known (fixedState (packet n) ((rows n).map (fixed (packet n)))) id :=
  GeneralRebaseActualReplay281.fixed_known _ _ _

end Loose

end Yulang.GeneralRebaseLoopReplay281
