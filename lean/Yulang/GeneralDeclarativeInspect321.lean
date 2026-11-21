import Yulang.GeneralDeclarativeK2Alias321
import Yulang.GeneralDeclarativeGraphRows321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeInspect321
open GeneralDeclarativeK2Graph321 (Shape View)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeGraphRows321 (observed structural)
open GeneralDeclarativeHead320 (State)
open GeneralNominalCenteredHeadMatExpressions (Expr)

inductive Inspects : Expr → Prop where
  | primitive : Inspects (.primitive tag children)
  | nominal : Inspects (.nominal tag children)
  | record : Inspects (.record label payload tail)
  | variant : Inspects (.variant label payload)

def fieldPatterns : Expr → List (Nat × Expr)
  | .record label payload tail => (label,payload) ::
      (fieldPatterns tail).filter (fun field => decide (field.1 ≠ label))
  | _ => []

/-- Positions actually inspected by a constructor prefix. A variable has no
such position; record payloads are named by field, not by row tail. Further
pattern forms require a normalization correspondence before descent. -/
inductive Visit (view : View) : Nat → Expr → Nat → Prop where
  | here : Inspects code → Visit view name code name
  | primitive {i : Nat} :
    view name (.primitive tag actual) →
    queries[i]? = some query → actual[i]? = some child →
    Visit view child query site → Visit view name (.primitive tag queries) site
  | nominal {i : Nat} :
    view name (.nominal tag actual) →
    queries[i]? = some query → actual[i]? = some child →
    Visit view child query site → Visit view name (.nominal tag queries) site
  | field :
    view name (.record fields) → (label,child) ∈ fields →
    (label,query) ∈ fieldPatterns (.record first payload tail) →
    Visit view child query site → Visit view name (.record first payload tail) site
  | variant :
    view name (.variant label child) →
    Visit view child payload site → Visit view name (.variant label payload) site

theorem variable_has_no_visit {view : View} : ¬Visit view root (.variable binder) site := by
  intro visited
  cases visited with
  | here notVariable => cases notVariable

theorem nominal_variable_visits_only_root {view : View}
    (visited : Visit view root (.nominal label [.variable binder]) site) :
    site = root := by
  cases visited with
  | here => rfl
  | nominal _ atIndex _ inside =>
    have eq := List.mem_singleton.mp (List.mem_of_getElem? atIndex)
    subst_vars
    exact False.elim (variable_has_no_visit inside)

/-- A K2 finding at a reached position uses the ordinary structural view,
including unavailable outputs, not the separate support-filtered view. -/
def PatternK2 (s : State) (root : Nat) (code : Expr) : Prop :=
  ∃ site, Visit (structural s) root code site ∧ AliasCycle s (observed s) site

theorem no_descendant_visit_for_nominal_capture {s : State} (safeRoot : ¬AliasCycle s (observed s) root) :
    ¬PatternK2 s root (.nominal tag [.variable binder]) := by
  rintro ⟨site,reaches,cycle⟩
  have same := nominal_variable_visits_only_root reaches
  subst site
  exact safeRoot cycle

end Yulang.GeneralDeclarativeInspect321
