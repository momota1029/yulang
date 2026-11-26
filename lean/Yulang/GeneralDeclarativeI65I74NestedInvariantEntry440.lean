import Yulang.GeneralDeclarativeI65I74NestedInvariantRule440
import Yulang.GeneralDeclarativeI65I74MergedOutputEntry439

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.NestedInvariant440
open GeneralDeclarativeI65
open Checker408 (Problem Result)
open CommonRoleOutermostResolver (Dictionary Summarizes)
open GeneralDeclarations (Declaration)
open GeneralDeclarativeInspect321 (PatternK2)

/-- The new case stores the original selected structural trace.
No old classification, fixed dictionary constructor or report type is edited. -/
def R20 (s : I72.State) (q : Request) (r : CommonRoleOutermostResolver.Result) : Prop :=
  MergedOutput439.R19 s q r ∨
  ∃ (d : Declaration) (_a : Original s q d), r = .selected (.node d.id [])

theorem dictionary_sound_R20 : ∀ s q d, R20 s q (.selected d) →
    ∀ m, I72.Fits s m → CompletedEntry438.DictionaryEvidence18 s m q d := by
  intro s q d classified m fit
  rcases classified with old|⟨row,a,e⟩
  · exact MergedOutput439.dictionary_sound_R19 s q d old m fit
  · have eq := CommonRoleOutermostResolver.Result.selected.inj e
    subst d
    exact .previous (nested_only_dictionary_sound440 s q _ (actual_nested_classifies440 a) m fit)

def ClassifiedAs (s : I72.State) (q : Request) (r : Result) : Prop :=
  MergedOutput439.ClassifiedAs s q r ∨
  ∃ (d : Declaration) (_source : Original s q d), r = leafReport d ∧
    I72.Classifies nestedLocal s q r.verdict

def ReportEvidence (s : I72.State) (m : I72.Model) (q : Request) (r : Result) : Prop :=
  MergedOutput439.ReportEvidence s m q r ∨
  ∃ (d : Declaration) (a : Original s q d), r = leafReport d ∧
    I72.DictionaryEvidence s m q (.node d.id []) ∧ WindowMeaning a.window m ∧
    Binding.Denotes a.capture m a.binding ∧
    GeneralDeclarativeWhere319.InInterval (m.assignment a.low).1
      (m.assignment a.high).1 (m.assignment a.center).1 ∧
    m.nativeSyntax a.arg.lower = some (nestedEndpoint a.outer a.inner a.low a.high) ∧
    m.nativeSyntax a.site = some (nestedInner a.inner a.low a.high)

inductive Witness where
  | previous (old : MergedOutput439.Witness)
  | nested (source : Wire)
  | unsupported

def check (p : Problem) (r : Result) : Witness → Bool
  | .previous w => MergedOutput439.check p r w
  | .nested w =>
    match scope : visible p.state.core p.root with
    | [d] =>
      (replay440 p d scope w).isSome &&
        Check408.matchesNoWrites r (leafReport d).tree (leafReport d).verdict
    | _ => false
  | .unsupported => false

theorem all_previous_R19_Bool_unchanged440 (p : Problem) (r : Result) (w : MergedOutput439.Witness) :
    check p r (.previous w) = MergedOutput439.check p r w := rfl

theorem checked_nested_returns_original_report440 {p : Problem} {r : Result} {w : Wire}
    (ok : check p r (.nested w) = true) :
    ∃ (d : Declaration) (scope : visible p.state.core p.root = [d]) (a : Original p.state p.root d),
      replay440 p d scope w = some a ∧ r = leafReport d := by
  simp only [check] at ok
  split at ok
  · rename_i d scope
    obtain ⟨found,report⟩ := GeneralDeclarativeWitnessProblem349.splitAnd ok
    cases replay : replay440 p d scope w with
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
    obtain ⟨old,meaning⟩ := MergedOutput439.check_sound p r w yes
    exact ⟨.inl old,fun m fit => .inl (meaning m fit)⟩
  | nested w =>
    obtain ⟨d,_,a,_,eq⟩ := checked_nested_returns_original_report440 yes
    subst r
    have source := actual_nested_classifies440 a
    refine ⟨.inr ⟨d,a,rfl,source⟩,fun m fit => .inr
      ⟨d,a,rfl,nested_only_dictionary_sound440 _ _ _ source m fit,?_⟩⟩
    have ⟨window,bind,bounds⟩ := nested_captures_mean_in_same_model440 a m fit
    exact ⟨window,bind,bounds,a.allOriginalOrigins m fit⟩
  | unsupported => simp [check] at yes

theorem verified_R20_result_classifies_in_same_State440 (p : Problem) (r : Result)
    (w : Witness) (ok : check p r w = true) :
    R20 p.state p.root r.verdict ∧
      ∀ m, I72.Fits p.state m → ReportEvidence p.state m p.root r := by
  refine ⟨?_,(check_sound p r w ok).2⟩
  cases w with
  | previous old => exact .inl (MergedOutput439.verified_R19_result_classifies_in_same_State439 p r old ok).1
  | nested wire =>
    obtain ⟨d,_,a,_,same⟩ := checked_nested_returns_original_report440 ok
    exact .inr ⟨d,a,congrArg (fun out : Result => out.verdict) same⟩
  | unsupported => simp [check] at ok

theorem checked_nested_retains_raw_priority440 {p : Problem} {r : Result} {w : Wire}
    (yes : check p r (.nested w) = true) :
    ∃ (d : Declaration) (a : Original p.state p.root d),
      ¬RootCycle p.state p.root ∧
      ¬PatternK2 p.state.core.current.ordinary a.arg.lower (query a.outer a.inner a.binder) := by
  obtain ⟨d,_,a,_,_⟩ := checked_nested_returns_original_report440 yes
  exact ⟨d,a,a.rootSafe,a.visitedSafe⟩

theorem no_new_nested_selection_over_original_raw_root440 {p : Problem} {r : Result} {w : Wire}
    (cycle : RootCycle p.state p.root) : check p r (.nested w) = false := by
  cases k : check p r (.nested w) with
  | false => rfl
  | true =>
    obtain ⟨_,_,safe,_⟩ := checked_nested_retains_raw_priority440 k
    exact (safe cycle).elim

end Yulang.GeneralDeclarativeI65.I72.NestedInvariant440
