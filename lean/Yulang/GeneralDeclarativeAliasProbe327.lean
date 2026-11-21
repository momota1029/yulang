import Yulang.GeneralDeclarativeEndpointProbe321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeAliasProbe327
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeLowerKnown321 (Alias alias_symm)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeTrace321 (Trace)
open GeneralDeclarativeEndpointProbe321 (Matches HeadMatches)
open CommonRoleOutermostResolver (All₂)

/-- Transport a real supported trace along a name alias. This allows
the recorded occurrence name to change at a bare capture. It does not
assert that model-equivalence alone exposes an authorized head. -/
theorem trace {s : State} (link : Alias s to fromName) (old : Trace s mode fromName code uses) :
    ∃ other, Trace s mode to code other := by
  cases old with
  | capture => exact ⟨_,.capture⟩
  | primitive eq row kids => exact ⟨_,.primitive (.trans link eq) row kids⟩
  | nominal eq row kids => exact ⟨_,.nominal (.trans link eq) row kids⟩
  | record eq row a b => exact ⟨_,.record (.trans link eq) row a b⟩
  | variant eq row one => exact ⟨_,.variant (.trans link eq) row one⟩
  | join eq row a b => exact ⟨_,.join (.trans link eq) row a b⟩

structure Ends (s : State) (a b : Capture) : Prop where
  lower : Alias s a.lower b.lower
  upper : Alias s a.upper b.upper
  bounds : Bounds s a
  otherBounds : Bounds s b

theorem one {s : State} (linked : Ends s a b) : Matches s c i a p ↔ Matches s c i b p := by
  constructor
  · rintro ⟨_,code,lo,hi,printed,left,right⟩
    obtain ⟨newLo,fromLo⟩ := trace (alias_symm linked.lower) left
    obtain ⟨newHi,fromHi⟩ := trace (alias_symm linked.upper) right
    exact ⟨linked.otherBounds,code,newLo,newHi,printed,fromLo,fromHi⟩
  · rintro ⟨_,code,lo,hi,printed,left,right⟩
    obtain ⟨newLo,fromLo⟩ := trace linked.lower left
    obtain ⟨newHi,fromHi⟩ := trace linked.upper right
    exact ⟨linked.bounds,code,newLo,newHi,printed,fromLo,fromHi⟩

theorem replay {s : State} (linked : All₂ (Ends s) as bs) :
    All₂ (Matches s c i) as pats ↔ All₂ (Matches s c i) bs pats := by
  induction linked generalizing pats with
  | nil => exact Iff.rfl
  | cons head rest ih =>
    constructor
    · intro had; cases had with
      | cons first more => exact .cons ((one head).mp first) (ih.mp more)
    · intro had; cases had with
      | cons first more => exact .cons ((one head).mpr first) (ih.mpr more)

end Yulang.GeneralDeclarativeAliasProbe327
