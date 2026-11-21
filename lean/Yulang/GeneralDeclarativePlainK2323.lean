import Yulang.GeneralDeclarativePlainCapture323
import Yulang.GeneralDeclarativeInspect321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativePlainK2323
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralCandidateInspection (plainNames)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralDeclarativeInspect321 (Visit PatternK2 variable_has_no_visit)
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeGraphRows321 (observed)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativePlainCapture323 (actual_probe)

theorem plain_code_no_visit (names : plainNames p = some seen)
    (spelled : translate c interp p = some code) :
    ¬Visit view root code site := by
  cases p with
  | var binder =>
    have exact := Option.some.inj spelled
    cases exact
    exact variable_has_no_visit
  | join a b =>
    cases fa : translate c interp a with
    | none => simp [translate,fa] at spelled
    | some lhs =>
      cases fb : translate c interp b with
      | none => simp [translate,fa,fb] at spelled
      | some rhs =>
        have same := Option.some.inj (show some (.join lhs rhs) = some code by simpa [translate,fa,fb] using spelled)
        cases same
        intro visited
        cases visited with
        | here impossible => cases impossible
  | app | record | variant => cases names

theorem visits_only_outer (names : plainNames p = some seen)
    (spelled : translate c interp p = some code)
    (there : Visit view root (.variant tag code) site) : site = root := by
  cases there with
  | here => rfl
  | variant _ deeper => exact False.elim (plain_code_no_visit names spelled deeper)

/-- Exactly the outer tag is consulted for this approved merged-plain
query; no descendant constructor cycle is demanded at a captured payload.
The cycle of the tag root itself still uses the full ordinary state. -/
theorem k2_exact (s : State) (names : plainNames p = some seen)
    (spelled : translate c interp p = some code) :
    PatternK2 s root (.variant tag code) ↔ AliasCycle s (observed s) root := by
  constructor
  · rintro ⟨site,visited,cycle⟩
    cases visits_only_outer names spelled visited
    exact cycle
  · intro issue
    exact ⟨root,.here .variant,issue⟩

end Yulang.GeneralDeclarativePlainK2323
