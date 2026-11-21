import Yulang.GeneralDeclarativeStableReads329
import Yulang.GeneralDeclarativeStableCanonical329

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeStableMerge329
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeOpaqueConserve328 (Retains)
open GeneralDeclarativeOpaqueShared328 (build built)
open GeneralDeclarativeStableReads329 (Heads head weakened names_all)
open GeneralDeclarativeStableTies329 (Consequence pairOf repeated_shares)
open GeneralDeclarativeTraceNames321 (names)
open GeneralDeclarativeOpaqueNested328 (occurrences)
open GeneralDeclarativeTermWalk322 (Binds)
open GeneralDeclarativeEqualities322 (Derives entails)
open GeneralDeclarativeGrowth327 (Extends derives fits)
open GeneralDeclarativeNFHead324 (fact)
open GeneralDeclarativeCompileLists321 (Result)
open GeneralDeclarationPatterns (variablesArgs normalizeArgs)
open CommonRoleOutermostResolver (All₂)

theorem head_with_binds {s : State} (read : Heads s c i args pats spans)
    (shared : Binds s merged (occurrences spans)) :
    All₂ (fun a p => Bounds s a ∧ Result s (fact c i merged a p)) args pats := by
  induction read with
  | nil => exact .nil
  | @cons a p left as ps right mark more ih =>
    obtain ⟨code,form,compiled,known,walk⟩ := mark.actual
    have split : occurrences (left ++ right) = occurrences left ++ occurrences right := List.map_append ..
    rw [split] at shared
    obtain ⟨first,last⟩ := GeneralDeclarativeTermWalk322.split_binds shared
    exact .cons ⟨mark.fits,GeneralDeclarativeForwardHead325.by_walk compiled (entails known) walk first⟩ (ih last)

/-- After selected ordinary writes, fold all occurrences of each input
binder across the entire ordered head. The bounded merge is now a
conservative logical naming step, not a proof that the selected
equality was redundant before it was written. -/
theorem compile_after {s : State} (read : Heads s c i args pats spans)
    (intervals : ∀ a ∈ spans, Bounds s a.2)
    (recorded : Consequence s selected (spans.map pairOf)) (keep : List Nat) (fallback : Nat → Capture) :
    let result := build keep spans fallback s (spans.map Prod.fst)
    Retains s result.state keep ∧
    (∀ key ∈ variablesArgs (normalizeArgs pats), Bounds result.state (result.captures key)) ∧
    All₂ (fun a p => Bounds result.state a ∧ Result result.state (fact c i result.captures a p)) args pats := by
  let result := build keep spans fallback s (spans.map Prod.fst)
  obtain ⟨conservative,provided⟩ := built keep fallback (spans.map Prod.fst) intervals (repeated_shares recorded)
  refine ⟨conservative,?_,head_with_binds (weakened conservative.grows read) ?_⟩
  · intro key found
    rw [← names_all read] at found
    obtain ⟨⟨n,span⟩,member,rfl⟩ := List.mem_map.mp found
    exact (provided n (List.mem_map.mpr ⟨_,member,rfl⟩) span member).1
  · intro o found
    obtain ⟨⟨key,span⟩,member,rfl⟩ := List.mem_map.mp found
    exact (provided key (List.mem_map.mpr ⟨_,member,rfl⟩) span member).2

end Yulang.GeneralDeclarativeStableMerge329
