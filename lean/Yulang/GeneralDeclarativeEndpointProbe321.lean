import Yulang.GeneralDeclarativeTrace321
import Yulang.GeneralDeclarativePriority321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeEndpointProbe321
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeDemand320 (Demand Bounds)
open GeneralDeclarativeTrace321 (Occurrence Trace)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarationPatterns (Pattern Constructors normalize)
open GeneralNominalCenteredHeadMatExpressions (translate)
open GeneralDeclarations (Declaration)
open GeneralNominalInspection (Interpretation)
open CommonRoleOutermostResolver (All₂)

/-- Positive endpoint probe. Variables record actual syntactic captures
without needing a constructor at that position. Readiness of all lower
endpoints is still an independent demand-level gate. This positive
fragment does not decide whether failure to match is a clash or unknown. -/
def Matches (s : State) (c : Constructors) (interp : Interpretation) (arg : Capture) (p : Pattern) : Prop :=
  Bounds s arg ∧ ∃ code lo hi,
    translate c interp (normalize p) = some code ∧
    Trace s .lower arg.lower code lo ∧ Trace s .upper arg.upper code hi

def HeadMatches (s : State) (c : Constructors) (interp : Interpretation) (d : Demand) (decl : Declaration) : Prop :=
  All₂ (Matches s c interp) d.arguments decl.head

end Yulang.GeneralDeclarativeEndpointProbe321
