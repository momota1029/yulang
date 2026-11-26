import Yulang.GeneralDeclarativeI65I74RefPositionRule441
import Yulang.GeneralDeclarativeI65I74NestedInvariantEntry440

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RefPositions441
open GeneralDeclarativeI65
open Checker408 (Problem Result)
open CommonRoleOutermostResolver (Dictionary Summarizes)
open GeneralDeclarations (Declaration)
open GeneralDeclarativeInspect321 (PatternK2)

/-- The new case stores the original selected structural trace.
No old classification, fixed dictionary constructor or report type is edited. -/
def R21 (s : I72.State) (q : Request) (r : CommonRoleOutermostResolver.Result) : Prop :=
  NestedInvariant440.R20 s q r ∨
  ∃ (d : Declaration) (_a : Original s q d), r = .selected (.node d.id [])

theorem dictionary_sound_R21 : ∀ s q d, R21 s q (.selected d) →
    ∀ m, I72.Fits s m → CompletedEntry438.DictionaryEvidence18 s m q d := by
  intro s q d classified m fit
  rcases classified with old|⟨row,a,e⟩
  · exact NestedInvariant440.dictionary_sound_R20 s q d old m fit
  · have eq := CommonRoleOutermostResolver.Result.selected.inj e
    subst d
    exact .previous (ref_only_dictionary_sound441 s q _ (actual_ref_classifies441 a) m fit)

def ClassifiedAs (s : I72.State) (q : Request) (r : Result) : Prop :=
  NestedInvariant440.ClassifiedAs s q r ∨
  ∃ (d : Declaration) (_source : Original s q d), r = leafReport d ∧
    I72.Classifies refLocal s q r.verdict

def ReportEvidence (s : I72.State) (m : I72.Model) (q : Request) (r : Result) : Prop :=
  NestedInvariant440.ReportEvidence s m q r ∨
  ∃ (d : Declaration) (a : Original s q d), r = leafReport d ∧
    I72.DictionaryEvidence s m q (.node d.id []) ∧ WindowMeaning a.window m ∧
    Binding.Denotes a.capture m a.rowBinding ∧ Binding.Denotes a.capture m a.valueBinding ∧
    m.nativeSyntax a.arg.lower = some (endpoint a.key a.rowName a.valueName)

inductive Witness where
  | previous (old : NestedInvariant440.Witness)
  | reference (source : Wire)
  | unsupported

def check (p : Problem) (r : Result) : Witness → Bool
  | .previous w => NestedInvariant440.check p r w
  | .reference w =>
    match scope : visible p.state.core p.root with
    | [d] =>
      (replay441 p d scope w).isSome &&
        Check408.matchesNoWrites r (leafReport d).tree (leafReport d).verdict
    | _ => false
  | .unsupported => false

theorem all_previous_R20_Bool_unchanged441 (p : Problem) (r : Result) (w : NestedInvariant440.Witness) :
    check p r (.previous w) = NestedInvariant440.check p r w := rfl

theorem checked_ref_returns_original_report441 {p : Problem} {r : Result} {w : Wire}
    (ok : check p r (.reference w) = true) :
    ∃ (d : Declaration) (scope : visible p.state.core p.root = [d]) (a : Original p.state p.root d),
      replay441 p d scope w = some a ∧ r = leafReport d := by
  simp only [check] at ok
  split at ok
  · rename_i d scope
    obtain ⟨found,report⟩ := GeneralDeclarativeWitnessProblem349.splitAnd ok
    cases replay : replay441 p d scope w with
    | none => simp [replay] at found
    | some a =>
      refine ⟨d,scope,a,replay,?_⟩
      obtain ⟨tree,verdict,writes⟩ := Check408.matchesNoWrites_exact408.mp report
      cases r
      simp only [leafReport,Check408.nullaryReport] at tree verdict writes
      subst_vars
      rfl
  · simp at ok

theorem check_sound (p : Problem) (r : Result) (w : Witness)
    (yes : check p r w = true) :
    ClassifiedAs p.state p.root r ∧
      ∀ m : I72.Model, I72.Fits p.state m → ReportEvidence p.state m p.root r := by
  cases w with
  | previous w =>
    obtain ⟨old,meaning⟩ := NestedInvariant440.check_sound p r w yes
    exact ⟨.inl old,fun m fit => .inl (meaning m fit)⟩
  | reference w =>
    obtain ⟨d,_,a,_,eq⟩ := checked_ref_returns_original_report441 yes
    subst r
    have source := actual_ref_classifies441 a
    refine ⟨.inr ⟨d,a,rfl,source⟩,fun m fit => .inr
      ⟨d,a,rfl,ref_only_dictionary_sound441 _ _ _ source m fit,?_⟩⟩
    have ⟨window,row,value⟩ := actual_typed_positions_mean_in_same_model441 a m fit
    exact ⟨window,row,value,a.actualOrigin m fit⟩
  | unsupported => simp [check] at yes

theorem verified_R21_result_classifies_in_same_State441 (p : Problem) (r : Result)
    (w : Witness) (ok : check p r w = true) :
    R21 p.state p.root r.verdict ∧
      ∀ m, I72.Fits p.state m → ReportEvidence p.state m p.root r := by
  refine ⟨?_,(check_sound p r w ok).2⟩
  cases w with
  | previous old => exact .inl (NestedInvariant440.verified_R20_result_classifies_in_same_State440 p r old ok).1
  | reference wire =>
    obtain ⟨d,_,a,_,same⟩ := checked_ref_returns_original_report441 ok
    exact .inr ⟨d,a,congrArg (fun out : Result => out.verdict) same⟩
  | unsupported => simp [check] at ok

theorem checked_ref_retains_raw_priority441 {p : Problem} {r : Result} {w : Wire}
    (yes : check p r (.reference w) = true) :
    ∃ (d : Declaration) (a : Original p.state p.root d),
      ¬RootCycle p.state p.root ∧
      ¬PatternK2 p.state.core.current.ordinary a.arg.lower (inspectionPattern a.key a.rowBinder a.valueBinder) := by
  obtain ⟨d,_,a,_,_⟩ := checked_ref_returns_original_report441 yes
  exact ⟨d,a,a.safe,no_raw_cycle_at_either_binder441 a⟩

theorem no_new_ref_selection_over_original_raw_root441 {p : Problem} {r : Result} {w : Wire}
    (cycle : RootCycle p.state p.root) : check p r (.reference w) = false := by
  cases k : check p r (.reference w) with
  | false => rfl
  | true =>
    obtain ⟨_,_,safe,_⟩ := checked_ref_retains_raw_priority441 k
    exact (safe cycle).elim


theorem original_raw_root_is_first_in_R21441 {s : I72.State} {q : Request}
    (cycle : RootCycle s q) :
    R21 s q .rejected ∧ ∀ d, ¬ R21 s q (.selected d) := by
  have inherited := CompletedEntry438.raw_root_K2_has_priority438
    (prior := PendingAssociated434.R17) cycle
  refine ⟨.inl (.inl (.inl inherited.1)),?_⟩
  intro d picked
  rcases picked with ((before|⟨impossible,_⟩)|⟨_,nested,_⟩)|⟨_,refInput,_⟩
  · exact inherited.2 d before
  · cases impossible
  · exact nested.rootSafe cycle
  · exact refInput.safe cycle

end Yulang.GeneralDeclarativeI65.I72.RefPositions441
