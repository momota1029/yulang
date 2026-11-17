import Yulang.GeneralPresenceUsedTable245
import Yulang.GeneralPresenceOwnerOwnership244
/-! A sufficient representation invariant for repeated table guards.
The actual install/promotion procedures have not been shown to produce it.
This is not a termination theorem or a restriction on accepted programs. -/
namespace Yulang.GeneralPresenceRankedTable245
open Core.PresenceGeneration
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOwnerRewrite244
open GeneralPresenceCrossRead244 GeneralPresenceOwnerTable244
open GeneralPresenceSubstitutionSupport244 GeneralPresenceOwnerOwnership244
open GeneralPresenceUsedSupport245
variable {Name Owner : Type} [DecidableEq Name] [DecidableEq Owner]

def RankedState (rank : Name → Nat) (state : State Name Owner) : Prop :=
 ∀ owner ∈ state.owners, RankedEntries rank (state.entries owner)

def UniformRanks (rank : Name → Nat) (state : State Name Owner) : Prop :=
 ∀ owner ∈ state.owners, ∀ first ∈ state.entries owner, ∀ last ∈ state.entries owner,
 rank first.1 = rank last.1

omit [DecidableEq Name] [DecidableEq Owner] in
theorem external_of_rank (rank : Name → Nat) (state : State Name Owner)
 (ranked : RankedState rank state) (uniform : UniformRanks rank state) : ExternalState state := by
 intro owner member
 exact block_external (ranked owner member) (uniform owner member)

theorem active_of_rank (rank : Name → Nat) (removed retained : List (Entry Name))
 (oldRanked : RankedEntries rank removed) (retainedRanked : RankedEntries rank retained)
 (uniform : ∀ first ∈ retained, ∀ last ∈ retained, rank first.1 = rank last.1) :
 ActiveCrossRead removed retained := by
 apply (external_active_exact removed retained (block_external retainedRanked uniform)).mp
 exact GeneralPresenceSubstitutionSupport244.transformed_external _ (substitution_below oldRanked) retainedRanked uniform

theorem checked_of_rank (rank : Name → Nat) (state : State Name Owner) (owner : Owner)
 (present : owner ∈ state.owners) (ranked : RankedState rank state)
 (uniform : UniformRanks rank state) (disjoint : DisjointState state) :
 GeneralPresenceUsedTable245.check state owner = true := by
 apply (GeneralPresenceUsedTable245.check_exact ..).mpr
 intro other member different
 apply (GeneralPresenceUsedTable245.retained_exact ..).mpr
 exact ⟨⟨disjoint owner present other member (Ne.symm different),
   external_of_rank rank state ranked uniform other member⟩,
   active_of_rank rank _ _ (ranked owner present) (ranked other member) (uniform other member)⟩

theorem rebase_ranked (rank : Name → Nat) (state : State Name Owner) (owner : Owner)
 (fresh : List (Entry Name)) (present : owner ∈ state.owners)
 (ranked : RankedState rank state) (freshRanked : RankedEntries rank fresh) :
 RankedState rank (rebase state owner fresh) := by
 intro other member
 by_cases same : other = owner
 · subst other; simpa only [rebase_at] using freshRanked
 · rw [rebase_other state owner other fresh same]
   exact transformed_ranked _ (substitution_below (ranked owner present)) (ranked other member)

theorem rebase_uniform (rank : Name → Nat) (state : State Name Owner) (owner : Owner)
 (fresh : List (Entry Name)) (uniform : UniformRanks rank state)
 (freshUniform : ∀ first ∈ fresh, ∀ last ∈ fresh, rank first.1 = rank last.1) :
 UniformRanks rank (rebase state owner fresh) := by
 intro other member
 by_cases same : other = owner
 · subst other; simpa only [rebase_at] using freshUniform
 · rw [rebase_other state owner other fresh same]
   exact transformed_same_rank _ (uniform other member)

omit [DecidableEq Name] in
theorem uniform_within (rank : Name → Nat) (fresh old : List (Entry Name))
 (within : TargetsWithin fresh old)
 (uniform : ∀ first ∈ old, ∀ last ∈ old, rank first.1 = rank last.1) :
 ∀ first ∈ fresh, ∀ last ∈ fresh, rank first.1 = rank last.1 := by
 intro first firstMem last lastMem
 obtain ⟨a,am,ae⟩ := within first firstMem
 obtain ⟨b,bm,be⟩ := within last lastMem
 rw [← ae,← be]
 exact uniform a am b bm

/-- Every next owner passes the exact used-read check after a ranked refresh.
Fresh rankedness remains a separate producer obligation. -/
theorem next_checked (rank : Name → Nat) (state : State Name Owner) (owner next : Owner)
 (fresh : List (Entry Name)) (present : owner ∈ state.owners) (nextPresent : next ∈ state.owners)
 (ranked : RankedState rank state) (uniform : UniformRanks rank state) (disjoint : DisjointState state)
 (within : TargetsWithin fresh (state.entries owner)) (freshRanked : RankedEntries rank fresh) :
 GeneralPresenceUsedTable245.check (rebase state owner fresh) next = true := by
 exact checked_of_rank rank _ next nextPresent
   (rebase_ranked rank state owner fresh present ranked freshRanked)
   (rebase_uniform rank state owner fresh uniform (uniform_within rank _ _ within (uniform owner present)))
   (rebase_disjoint state owner fresh disjoint within)
end Yulang.GeneralPresenceRankedTable245
