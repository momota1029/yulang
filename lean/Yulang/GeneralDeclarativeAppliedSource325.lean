import Yulang.GeneralDeclarativeVisibleCode325
import Yulang.GeneralDeclarativeApplyAssoc324

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeAppliedSource325
open GeneralDeclarations (Checked)
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeBatch320 (collect)
open GeneralDeclarativeNFNode324 (BodyCoverage)
open GeneralDeclarativeVisibleCode325 (code_was_covered)
open GeneralDeclarativeAssocRule323 (SourceEquation)
open GeneralDeclarativeNormalizeAssoc324 (one row_iff collects applied_models selected_rules_now_stable)
open GeneralDeclarativeOutputs320 (bodyPattern)
open GeneralDeclarativeEntailment320 (appendFacts Holds)
open GeneralDeclarativeModelStable324 (StableUnder stable_exact)
open GeneralDictionaryAssociatedProvenance (lookup lookup_exact Supplies)
open GeneralNominalCenteredHeadMatExpressions (translate)
open GeneralDeclarationPatterns (normalize)
open GeneralSourceState (Output)

theorem each_defined {f : Output → Option (List Equation)} {outs : List Output}
    (built : collect f outs = some rows) : ∀ out ∈ outs, ∃ rs, f out = some rs := by
  induction outs generalizing rows with
  | nil => intro out h; cases h
  | cons first rest ih =>
    cases selected : f first with
    | none => simp [collect,selected] at built
    | some written =>
      cases follow : collect f rest with
      | none => simp [collect,selected,follow] at built
      | some tail =>
        intro out member
        rcases List.mem_cons.mp member with rfl|later
        · exact ⟨written,selected⟩
        · exact ih follow _ later

theorem individual_shape
    (built : one r i impl d cap out = some rows) :
    ∃ row, rows = [row] := by
  cases b : lookup r.roles impl out.name with
  | none => simp [one,b] at built
  | some rhs =>
    cases t : translate r.constructors i (normalize (bodyPattern rhs)) with
    | none => simp [one,b,t] at built
    | some exp =>
      have h : [?row] = rows := by simpa [one,b,t] using built
      exact ⟨_,h.symm⟩

theorem supplied_was_read (checked : Checked r) (visible : impl ∈ r.declarations)
    (source : Supplies r.roles impl out.name body)
    (built : one r i impl d cap out = some rows) :
    ∃ expr, translate r.constructors i (normalize (bodyPattern body)) = some expr := by
  have read := (lookup_exact r.roles impl (checked.2 impl visible).identified.2.2.1 out.name body).mpr source
  cases found : translate r.constructors i (normalize (bodyPattern body)) with
  | none => simp [one,read,found] at built
  | some exp => exact ⟨exp,rfl⟩

/-- Actual successful emission removes both abstract body coverage and
redundant assumptions about surplus outputs. There is still an independent
obligation to identify this emission with the selected current source. -/
theorem output_read_and_exact (checked : Checked r) (visible : impl ∈ r.declarations)
    (built : collect (one r i impl d cap) d.outputs = some rows) :
    BodyCoverage r i d impl ∧
      ∀ row, row ∈ rows ↔ SourceEquation r i d impl cap row := by
  have each := each_defined built
  have singles : ∀ out ∈ d.outputs, ∃ row, one r i impl d cap out = some [row] := by
    intro out asked
    obtain ⟨rs,printed⟩ := each out asked
    obtain ⟨row,rfl⟩ := individual_shape printed
    exact ⟨row,printed⟩
  obtain ⟨rows',printed,found⟩ := collects singles
  cases Option.some.inj (printed.symm.trans built)
  refine ⟨?_,fun row => (found row).trans (row_iff checked visible).symm⟩
  intro out asked body source
  obtain ⟨rs,seen⟩ := each out asked
  obtain ⟨exp,written⟩ := supplied_was_read checked visible source seen
  exact code_was_covered written

theorem stable_after_written {s : State} (checked : Checked r) (visible : impl ∈ r.declarations)
    (built : collect (one r i impl d cap) d.outputs = some rows)
    (written : rows ⊆ s.equations) :
    BodyCoverage r i d impl ∧ StableUnder s (SourceEquation r i d impl cap) := by
  obtain ⟨cover,actual⟩ := output_read_and_exact checked visible built
  exact ⟨cover,stable_exact.mpr (fun row source m valid => valid.2 _ (written ((actual row).mpr source)))⟩

theorem exact_effect {s : State} (checked : Checked r) (visible : impl ∈ r.declarations)
    (built : collect (one r i impl d cap) d.outputs = some rows) (m) :
    Models (appendFacts s rows) m ↔ Models s m ∧
      ∀ row, SourceEquation r i d impl cap row → Holds m row :=
  applied_models (output_read_and_exact checked visible built).2 m

end Yulang.GeneralDeclarativeAppliedSource325
