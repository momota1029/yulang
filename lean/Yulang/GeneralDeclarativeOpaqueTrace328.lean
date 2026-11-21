import Yulang.GeneralDeclarativeOpaqueIntervals328
import Yulang.GeneralDeclarativeOpaqueAuthority328
import Yulang.GeneralDeclarativeEndpointProbe321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeOpaqueTrace328
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativePairCenters326 (pair)
open GeneralDeclarativePairProbe326 (components)
open GeneralDeclarativeTrace321 (Trace)
open GeneralDeclarativeOrigins321 (Supported restriction backed_iff)
open GeneralDeclarativeOrdinaryIncrease325 (Extends derives)
open GeneralDeclarativeOpaqueIntervals328 (Ends protect low high left right ready actual)
open GeneralDeclarativeOpaqueNames328 (kept)
open GeneralDeclarativeEqualities322 (Derives entails)
open GeneralDeclarativeEndpointProbe321 (Matches)
open GeneralDeclarativeTermWalk322 (Walk Binds)
open GeneralDeclarativeNFHead324 (fact)
open GeneralDeclarativeCompileLists321 (Result)
open GeneralDeclarationPatterns (normalize)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)

theorem ordinary_over_support {s : State} (p : Supported s done) : Extends (restriction p) s := by
  refine ⟨rfl,?_⟩
  intro row already
  obtain ⟨orig,proved,used⟩ := (backed_iff p row).mp already
  exact p.ordinary proved

/-- Names of both endpoint components come from actual authorized
source traces; the actual coordinate names are computed separately.
This theorem requires neither an ordinary center equation nor a mere
existential model supplying candidate viability. -/
theorem from_pair_match {s : State} {p : Supported s done} {arg : Capture}
    (printed : translate c i (normalize pat) = some (pair a b))
    (matched : Matches (restriction p) c i arg pat) (extra : List Nat) :
    ∃ e : Ends, ∃ l₁ l₂ h₁ h₂,
      Trace (restriction p) .lower e.firstLo a l₁ ∧
      Trace (restriction p) .lower e.secondLo b l₂ ∧
      Trace (restriction p) .upper e.firstHi a h₁ ∧
      Trace (restriction p) .upper e.secondHi b h₂ ∧
      Derives s (.variable arg.lower) (low e) ∧ Derives s (.variable arg.upper) (high e) ∧
      Bounds (ready s arg.center extra e) (left s arg.center extra e) ∧
      Bounds (ready s arg.center extra e) (right s arg.center extra e) ∧
      (∀ m, Models s m ↔ ∃ expanded, Models (ready s arg.center extra e) expanded ∧
        ∀ n ∈ kept s arg.center (protect extra e), expanded n = m n) ∧
      Derives (ready s arg.center extra e) (.variable arg.center)
        (pair (.variable (left s arg.center extra e).center) (.variable (right s arg.center extra e).center)) := by
  obtain ⟨bounded,code,leftRaw,rightRaw,translated,lo,hi⟩ := matched
  have term : code = pair a b := Option.some.inj (translated.symm.trans printed)
  subst code
  obtain ⟨lA,lB,l₁,l₂,readLo,leftA,leftB,_⟩ := components lo
  obtain ⟨hA,hB,h₁,h₂,readHi,rightA,rightB,_⟩ := components hi
  let e : Ends := ⟨lA,hA,lB,hB⟩
  have startLo := derives (ordinary_over_support p) readLo
  have startHi := derives (ordinary_over_support p) readHi
  have intervals := GeneralDeclarativeOpaqueIntervals328.bounds (s := s) arg.center extra e
  exact ⟨e,l₁,l₂,h₁,h₂,leftA,leftB,rightA,rightB,startLo,startHi,intervals.1,intervals.2,
    GeneralDeclarativeOpaqueIntervals328.preserved (s := s) (e := e) bounded (entails startLo) (entails startHi) extra,
    actual arg.center extra e⟩

end Yulang.GeneralDeclarativeOpaqueTrace328
