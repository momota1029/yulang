import Yulang.GeneralDeclarativeModelStable324

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeNormalizeAssoc324
open GeneralDeclarations (Checked)
open GeneralDeclarativeHead320 (Equation State Models)
open GeneralDeclarativeEntailment320 (Entails Holds appendFacts model_append)
open GeneralDeclarativeModelStable324 (StableUnder appended_stable)
open GeneralDeclarativeAssocRule323 (SourceEquation)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralDeclarativeOutputs320 (bodyPattern bodyCapture)
open GeneralDeclarativeSubstitution320 (logical)
open GeneralDeclarativeBatch320 (collect)
open GeneralDictionaryAssociatedProvenance (lookup lookup_exact declared_covered)
open GeneralDeclarativeDefaultCoverage322 (supplies_covered)
open GeneralDeclarativeNormalizeCovered322 (normalize_covered)
open GeneralNominalCenteredHeadMatExpressions (translate translate_complete)
open GeneralDeclarationPatterns (normalize)
open GeneralNominalCenteredHeadWFSource (Coverage)
open GeneralSourceState (Output)

/-- Apply the source's independent associated rule to the given fixed
demand syntax. There is no dictionary/commit/engine argument. -/
def one (r : GeneralDeclarations.Registry) (interp : GeneralNominalInspection.Interpretation)
    (decl : GeneralDeclarations.Declaration) (d : GeneralDeclarativeDemand320.Demand)
    (capture : Nat → GeneralDeclarativeWhere319.Capture) (out : Output) : Option (List Equation) := do
  let body ← lookup r.roles decl out.name
  let form ← translate r.constructors interp (normalize (bodyPattern body))
  pure [⟨out.target,logical (bodyCapture d capture body) .actual form⟩]

theorem row_iff (checked : Checked r) (visible : decl ∈ r.declarations) :
    SourceEquation r interp d decl capture row ↔
      ∃ out ∈ d.outputs, one r interp decl d capture out = some [row] := by
  have unique := (checked.2 decl visible).identified.2.2.1
  constructor
  · rintro ⟨out,requested,body,actual,form,printed,rfl⟩
    exact ⟨out,requested,by simp [one,(lookup_exact r.roles decl unique out.name body).mpr actual,printed]⟩
  · rintro ⟨out,requested,generated⟩
    cases actual : lookup r.roles decl out.name with
    | none => simp [one,actual] at generated
    | some body =>
      cases printed : translate r.constructors interp (normalize (bodyPattern body)) with
      | none => simp [one,actual,printed] at generated
      | some form =>
        have rowEq : (⟨out.target,logical (bodyCapture d capture body) .actual form⟩ : Equation) = row := by
          simpa [one,actual,printed] using generated
        exact ⟨out,requested,body,(lookup_exact r.roles decl unique out.name body).mp actual,form,printed,rowEq.symm⟩

theorem one_total (checked : Checked r) (cover : Coverage r interp)
    (visible : decl ∈ r.declarations) (role : decl.role = d.role) (signature : Declared r d) :
    ∀ out ∈ d.outputs, ∃ row, one r interp decl d capture out = some [row] := by
  intro out requested
  have declared := role.symm ▸ signature out requested
  have rule := checked.2 decl visible
  obtain ⟨body,known⟩ := declared_covered r.roles decl rule.signature out.name declared
  obtain ⟨nf,printed⟩ := translate_complete (normalize_covered (supplies_covered (cover.1 decl visible) cover.2 known))
  exact ⟨⟨out.target,logical (bodyCapture d capture body) .actual nf⟩,by
    simp [one,(lookup_exact r.roles decl rule.identified.2.2.1 out.name body).mpr known,printed]⟩

theorem collects {f : Output → Option (List Equation)} {outs : List Output}
    (single : ∀ out ∈ outs, ∃ row, f out = some [row]) :
    ∃ rows, collect f outs = some rows ∧
      ∀ row, row ∈ rows ↔ ∃ out ∈ outs, f out = some [row] := by
  induction outs with
  | nil =>
    exact ⟨[],rfl,fun _ => by simp⟩
  | cons out more ih =>
    obtain ⟨first,printed⟩ := single out List.mem_cons_self
    obtain ⟨rows,other,exactRows⟩ := ih (fun x h => single x (List.mem_cons_of_mem _ h))
    refine ⟨first::rows,by simp [collect,printed,other],?_⟩
    intro row
    constructor
    · intro there
      rcases List.mem_cons.mp there with rfl|later
      · exact ⟨out,List.mem_cons_self,printed⟩
      · obtain ⟨it,mem,defined⟩ := (exactRows row).mp later
        exact ⟨it,List.mem_cons_of_mem _ mem,defined⟩
    · rintro ⟨it,mem,defined⟩
      rcases List.mem_cons.mp mem with rfl|later
      · have same := List.cons.inj (Option.some.inj (defined.symm.trans printed))
        exact List.mem_cons.mpr (Or.inl same.1)
      · exact List.mem_cons_of_mem _ ((exactRows row).mpr ⟨it,later,defined⟩)

/-- A genuine finite rule application: the ordered output list is
computed independently of the old state, and contains exactly the
source-associated rows for this declaration and actual capture. -/
theorem complete (checked : Checked r) (cover : Coverage r interp)
    (visible : decl ∈ r.declarations) (role : decl.role = d.role) (signature : Declared r d) :
    ∃ rows, collect (one r interp decl d capture) d.outputs = some rows ∧
      ∀ row, row ∈ rows ↔ SourceEquation r interp d decl capture row := by
  obtain ⟨rows,compiled,exactRows⟩ := collects (one_total (capture := capture) checked cover visible role signature)
  exact ⟨rows,compiled,fun row => (exactRows row).trans (row_iff checked visible).symm⟩

theorem applied_models {s : State} {rows : List Equation}
    (exactRows : ∀ row, row ∈ rows ↔ SourceEquation r interp d decl capture row) (m) :
    Models (appendFacts s rows) m ↔ Models s m ∧
      ∀ row, SourceEquation r interp d decl capture row → Holds m row := by
  rw [model_append]
  exact and_congr_right (fun _ =>
    ⟨fun facts row h => facts row ((exactRows row).mpr h),
      fun facts row h => facts row ((exactRows row).mp h)⟩)

theorem selected_rules_now_stable {s : State}
    (exactRows : ∀ row, row ∈ rows ↔ SourceEquation r interp d decl capture row) :
    StableUnder (appendFacts s rows) (SourceEquation r interp d decl capture) :=
  fun row h => appended_stable s rows row ((exactRows row).mpr h)

end Yulang.GeneralDeclarativeNormalizeAssoc324
