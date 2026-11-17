import Yulang.GeneralPresenceOwnerCheck244
namespace Yulang.GeneralPresenceOwnerSequence244
open Core.PresenceGeneration
open PresenceNormalForm
open GeneralPresenceDefinitionRewrite244
open GeneralPresenceSubstitutionSupport244
open GeneralPresenceOwnerRewrite244
variable {Name : Type} [DecidableEq Name]

def rewriteMany : List (List (Entry Name)) → List (Entry Name) → List (Entry Name)
 | [],entries => entries
 | removed :: rest,entries => rewriteMany rest (transform (substitution removed) entries)

def readMany (model : Model) : List (List (Entry Name)) → (Name → Comp model) → (Name → Comp model)
 | [],assignment => assignment
 | removed :: rest,assignment => fun name => (substitution removed name).eval model (readMany model rest assignment)

omit [DecidableEq Name] in
theorem disjoint_transform (removed retained : List (Entry Name)) (mapping : Name → CompTerm Name)
 (disjoint : DisjointTargets removed retained) : DisjointTargets removed (transform mapping retained) := by
 intro old oldMem other otherMem
 obtain ⟨original,member,rfl⟩ := List.mem_map.mp otherMem
 exact disjoint old oldMem original member

theorem sequence_exact (blocks : List (List (Entry Name))) (entries : List (Entry Name))
 (disjoint : ∀ removed ∈ blocks, DisjointTargets removed entries)
 (model : Model) (assignment : Name → Comp model) :
 All model assignment (block (rewriteMany blocks entries)) ↔
 All model (readMany model blocks assignment) (block entries) := by
 induction blocks generalizing entries assignment with
 | nil => rfl
 | cons removed rest ih =>
   have subsequent : ∀ later ∈ rest, DisjointTargets later (transform (substitution removed) entries) :=
     fun later member => disjoint_transform later entries _ (disjoint later (List.mem_cons_of_mem _ member))
   exact (ih _ subsequent assignment).trans
     (owner_block_exact removed entries (disjoint removed (by simp)) model (readMany model rest assignment))

theorem sequence_ranked {rank : Name → Nat} (blocks : List (List (Entry Name)))
 (blocksRanked : ∀ removed ∈ blocks, RankedEntries rank removed)
 (entries : List (Entry Name)) (ranked : RankedEntries rank entries) :
 RankedEntries rank (rewriteMany blocks entries) := by
 induction blocks generalizing entries with
 | nil => exact ranked
 | cons removed rest ih =>
   apply ih (fun later member => blocksRanked later (List.mem_cons_of_mem _ member))
   exact transformed_ranked _ (substitution_below (blocksRanked removed (by simp))) ranked

theorem sequence_same_rank {rank : Name → Nat} (blocks : List (List (Entry Name)))
 (entries : List (Entry Name))
 (sameRank : ∀ first ∈ entries, ∀ last ∈ entries, rank first.1 = rank last.1) :
 ∀ first ∈ rewriteMany blocks entries, ∀ last ∈ rewriteMany blocks entries, rank first.1 = rank last.1 := by
 induction blocks generalizing entries with
 | nil => exact sameRank
 | cons removed rest ih => exact ih _ (transformed_same_rank _ sameRank)

theorem sequence_external {rank : Name → Nat} (blocks : List (List (Entry Name)))
 (blocksRanked : ∀ removed ∈ blocks, RankedEntries rank removed)
 (entries : List (Entry Name)) (ranked : RankedEntries rank entries)
 (sameRank : ∀ first ∈ entries, ∀ last ∈ entries, rank first.1 = rank last.1) :
 ∀ entry ∈ rewriteMany blocks entries, ∀ source ∈ typeSources entry.2,
 ∀ target ∈ rewriteMany blocks entries, target.1 ≠ source :=
 block_external (sequence_ranked blocks blocksRanked entries ranked) (sequence_same_rank blocks entries sameRank)

theorem sequence_coherent (blocks : List (List (Entry Name))) (entries : List (Entry Name))
 (coherent : Coherent entries) : Coherent (rewriteMany blocks entries) := by
 induction blocks generalizing entries with
 | nil => exact coherent
 | cons removed rest ih => exact ih _ (transform_coherent _ coherent)

theorem sequence_targets (blocks : List (List (Entry Name))) (entries : List (Entry Name)) :
 (rewriteMany blocks entries).map Prod.fst = entries.map Prod.fst := by
 induction blocks generalizing entries with
 | nil => rfl
 | cons removed rest ih => exact (ih _).trans (targets_preserved _ entries)
end Yulang.GeneralPresenceOwnerSequence244
