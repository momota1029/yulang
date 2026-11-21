import Yulang.GeneralDeclarativeSourceCodes321
import Yulang.GeneralDeclarativeSourceNames321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeChildScope321
open GeneralDeclarations (Registry Clause Declaration DeclarationChecked)
open GeneralDeclarationPatterns (Pattern normalize normalizeArgs variablesArgs)
open GeneralDeclarativeTraceNames321 (names namesMany)
open GeneralDeclarativeSourceNames321 (actual_names actual_names_many)
open GeneralDeclarativeFreshCalls321 (SourceCodes)
open GeneralDeclarativeSourceCodes321 (clauseCodes forest_exact)
open GeneralDeclarativeFreshForest321 (ClauseCode)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open CommonRoleOutermostResolver (All₂)

theorem normalize_member {patterns : List Pattern} {p : Pattern} (found : p ∈ patterns) :
    normalize p ∈ normalizeArgs patterns := by
  induction patterns with
  | nil => cases found
  | cons first rest ih =>
    rcases List.mem_cons.mp found with rfl|later
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih later)

theorem member_variables {patterns : List Pattern} {p : Pattern} (found : p ∈ patterns) :
    p.variables ⊆ variablesArgs patterns := by
  induction patterns with
  | nil => cases found
  | cons first rest ih =>
    intro name appears
    rcases List.mem_cons.mp found with rfl|later
    · exact List.mem_append_left _ appears
    · exact List.mem_append_right _ (ih later appears)

/-- Every actual or polar binder read in a generated unnamed operand,
including below invariant nominal constructors, is a visible head
binder. No output-only binder is accepted as a new source input. -/
theorem translated_where_names {r : Registry} {decl : Declaration} {clause : Clause}
    (checked : DeclarationChecked r.constructors r.roles decl)
    (belongs : clause ∈ decl.requirements) (operand : p ∈ clause.arguments)
    (compiled : translate r.constructors interp (normalize p) = some code) :
    names code ⊆ decl.inputNames := by
  rw [actual_names (normalize p) compiled]
  intro name uses
  exact checked.scope.1 clause belongs name (member_variables (normalize_member operand) uses)

theorem all_where_names {r : Registry} {decl : Declaration} {clause : Clause}
    (checked : DeclarationChecked r.constructors r.roles decl) (belongs : clause ∈ decl.requirements)
    (compiled : SourceCodes r interp clause args outs) :
    namesMany args ⊆ decl.inputNames := by
  have aux {ps : List Pattern} {es : List Expr}
      (zip : All₂ (fun pat exp => translate r.constructors interp (normalize pat) = some exp) ps es)
      (inside : ps ⊆ clause.arguments) : namesMany es ⊆ decl.inputNames := by
    induction zip with
    | nil => intro _ h; cases h
    | cons first _ ih =>
      intro name used
      rcases List.mem_append.mp used with left|right
      · exact translated_where_names checked belongs (inside List.mem_cons_self) first left
      · exact ih (fun _ h => inside (List.mem_cons_of_mem _ h)) right
  exact aux compiled.arguments (fun _ h => h)

end Yulang.GeneralDeclarativeChildScope321
