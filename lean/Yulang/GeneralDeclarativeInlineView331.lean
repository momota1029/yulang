import Yulang.GeneralDeclarativeInlineCompiler331
import Yulang.GeneralDeclarativeGuardView330

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeInlineView331
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeDemand320 (Bounds Demand)
open GeneralDeclarativeInlineEndpoint331 (Matches Heads candidates)
open GeneralDeclarativeInlineGrowth331 (extend)
open GeneralDeclarativeGrowth327 (Extends fits)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeLowerKnown321 (Ready)
open GeneralDeclarativeStableAttempt329 (Elected)
open GeneralDeclarativePriority321 (Recurs)
open GeneralDeclarativeEndpointProbe321 (HeadMatches)
open CommonRoleOutermostResolver (All₂)

theorem match_grows {s t : State} (grown : Extends s t) (hit : Matches s c i a pat) :
    Matches t c i a pat := by
  obtain ⟨inside,code,left,right,translated,lo,hi⟩ := hit
  exact ⟨fits grown inside,code,left,right,translated,extend grown lo,extend grown hi⟩

theorem ordered_growth {s t : State} (grown : Extends s t)
    (hit : All₂ (Matches s c i) args pats) : All₂ (Matches t c i) args pats := by
  induction hit with
  | nil => exact .nil
  | cons one _ rest => exact .cons (match_grows grown one) rest

theorem positive_grows {s t : State} {p : Supported s done} {q : Supported t later}
    (grown : Extends (restriction p) (restriction q)) :
    (candidates p r i awaits).viable d impl → (candidates q r i awaits).viable d impl := by
  intro old
  rcases old with legacy|inline
  · exact .inl (GeneralDeclarativeGuardView330.args ⟨GeneralDeclarativeGrowth327.boundsOne grown,grown.equations⟩ legacy)
  · exact .inr (ordered_growth grown inline)

/-- If the actual supported positive view is unchanged, neither an
ordinary write nor equal all-model semantics is used as an election.
We preserve the existing independent wait judgment and still require
the currently applicable full-ordinary K2 guard. -/
theorem exact_current_election {s t : State} {p : Supported s done} {q : Supported t later}
    (toNow : Extends (restriction p) (restriction q))
    (fromNow : Extends (restriction q) (restriction p))
    (safeNow : ¬Recurs t r i (candidates q r i awaits) d)
    (old : Elected s r i p (candidates p r i awaits) d impl) :
    Elected t r i q (candidates q r i awaits) d impl :=
  GeneralDeclarativeGuardView330.elected
    ⟨GeneralDeclarativeGrowth327.boundsOne toNow,toNow.equations⟩
    (fun _ => ⟨positive_grows toNow,positive_grows fromNow⟩) (fun _ => Iff.rfl) safeNow old

end Yulang.GeneralDeclarativeInlineView331
