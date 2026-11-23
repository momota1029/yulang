import Yulang.GeneralDeclarativeI65Heads367
import Yulang.GeneralDeclarativeI65Origins367

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65
open GeneralDeclarativeWitnessConstructorModes357 (Use Mode SourceMode)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralNominalCenteredHeadMatExpressions (translate translateMany application)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarationPatterns (Pattern normalize)
open CommonRoleOutermostResolver (All₂)
open GeneralDeclarations (Declaration)

theorem ordered_head_at {α β : Type} {R : α → β → Prop} {as bs}
    (seen : All₂ R as bs) {i : Nat} {a b} (left : as[i]? = some a) (right : bs[i]? = some b) : R a b := by
  induction seen generalizing i with
  | nil => simp at left
  | cons here _ next =>
    cases i with
    | zero =>
      simp at left right
      cases left; cases right
      exact here
    | succ i => exact next (by simpa using left) (by simpa using right)

/-- A declaration with a real declared-mode key cannot be manufactured
by the ordinary primitive/invariant translator. This is a mode fact
about the actual source, not a generic failed-check rejection. -/
theorem declared_application_not_ordinary {s : State} {key : Nat} {ps : List Pattern}
    {parameters : List CommonDeclaredNominalInspection.Parameter}
    (read : SourceMode s.current.environment key (.declared parameters)) :
    translate (authoredRegistry s.current).constructors
      (interpretation s.current.environment.source.snapshot) (.app key ps) = none := by
  cases read with
  | declared _ noPrim noInv =>
    rw [translate]
    cases done : translateMany (authoredRegistry s.current).constructors
        (interpretation s.current.environment.source.snapshot) ps with
    | none => simp
    | some args =>
      cases ctor : (authoredRegistry s.current).constructors key <;>
        simp [application,ctor,interpretation,noPrim,noInv]

/-- A negative candidate fact must cite the actual ordered demand,
the actual source pattern, its declared-mode authority and a positively
observed, incompatible rigid original head. -/
structure RigidCandidateMiss (s : State) (q : Request) (row : Declaration) where
  index : Nat
  arg : Capture
  exactInput : q.demand.arguments[index]? = some arg
  name : Nat
  written : List Pattern
  exactHead : row.head[index]? = some (.app name written)
  authored : Use s.current.environment name written.length
  parameters : List CommonDeclaredNominalInspection.Parameter
  actualMode : authored.mode = .declared parameters
  conflict : RigidMismatch s arg (.app name written)

theorem rigid_candidate_excludes_a_source_head {s : State} {q : Request} {row : Declaration}
    (miss : RigidCandidateMiss s q row) (candidate : SourceHead s q row)
    (m : Model) (fit : Fits s m) : False := by
  cases candidate with
  | ordered cap all =>
    have selected := ordered_head_at all miss.exactInput miss.exactHead
    cases selected with
    | ordinary h =>
      have no := declared_application_not_ordinary (s := s)
        (ps := miss.written) (miss.actualMode ▸ miss.authored.sourced)
      obtain ⟨_,e,hit,_⟩ := h
      rw [no] at hit
      cases hit
    | declared obs _ => exact rigid_mismatch_excludes_same_lane miss.conflict obs m fit
  | joined head =>
    have whereHead := miss.exactHead
    rw [head.head] at whereHead
    cases k : miss.index with
    | zero =>
      have actual : head.written = .app miss.name miss.written := by simpa [k] using whereHead
      have incorrect := head.normalized
      rw [actual,normalize] at incorrect
      cases incorrect
    | succ n =>
      simp [k] at whereHead

end Yulang.GeneralDeclarativeI65
