import Yulang.GeneralDeclarativeTermCapture322
import Yulang.GeneralDeclarativeNormalizeCovered322
import Yulang.GeneralDeclarativeExistingLocal322

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeTermCapturedHead322
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeEqualities322 (Derives)
open GeneralDeclarativeTermWalk322 (Occurrence Walk)
open GeneralDeclarativeTermCapture322 (Shared KnownNames named named_binds)
open GeneralDeclarativeExistingLocal322 (Heads)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralNominalCenteredHeadWFSource (PatternCovered)
open GeneralNominalCenteredHeadMatExpressions (Expr translate translate_complete)
open GeneralDeclarations (Registry Declaration)
open GeneralDeclarationPatterns (normalize)
open CommonRoleOutermostResolver (All₂)

/-- Observed sources are actual ordinary equations and shape walks. This
input does not itself assign a capture map or require a compiler equation. -/
structure ActualSyntax (s : State) (r : Registry) (interp : GeneralNominalInspection.Interpretation)
    (d : Demand) (decl : Declaration) (all : List Occurrence) : Prop where
  atPosition : All₂ (fun arg p => PatternCovered r.constructors interp p ∧
    ∃ term code used, Derives s (.variable arg.center) term ∧
      translate r.constructors interp (normalize p) = some code ∧
      Walk .actual term code used ∧ used ⊆ all) d.arguments decl.head

/-- One common actual capture is constructed across all head arguments.
A source binder may occur repeatedly at different depths; each occurrence
is checked using the same map of already existing logical names. -/
theorem gives_heads {s : State} {p : Supported s completed}
    (read : ActualSyntax s r interp d decl all)
    (ordinary : Shared s all) (anchors : KnownNames s all pool)
    (endpoints : Nat → Capture) :
    Heads s p r interp d decl (named s all pool endpoints) := by
  apply Or.inr
  apply GeneralDeclarativeNormalized320.ordered_map read.atPosition
  rintro arg _ pattern _ ⟨covered,term,code,used,actual,normalized,walk,member⟩
  obtain ⟨raw,rawCode⟩ := translate_complete covered
  exact ⟨raw,code,rawCode,normalized,term,used,actual,walk,
    named_binds (initial := endpoints) member ordinary anchors walk⟩

end Yulang.GeneralDeclarativeTermCapturedHead322
