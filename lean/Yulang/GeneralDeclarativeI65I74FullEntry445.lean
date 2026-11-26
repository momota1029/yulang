import Yulang.GeneralDeclarativeI65I74RetainedFresh445

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RetainedFull445
open Yulang.GeneralDeclarativeI65
open Checker408 (Problem Result)
open MixedFixed442
open CommonRoleOutermostResolver (Dictionary)
open WhereAssociated432 (matchesAssociatedReport432 matches_associated_report_exact432)

structure FullProblem where
  state : FullState
  root : I72.Request

def FullProblem.old (p : FullProblem) : Problem := ⟨p.state.base,p.root⟩

def liftProblem (p : Problem) : FullProblem := ⟨liftState p.state,p.root⟩

/-- One local source rule, not the full language. An exact authored
selected event and the exact materialized row are independent of
the checker, reports, models and witnesses. Freshness is conservative. -/
structure LocalSelection (s : FullState) (q : I72.Request) where
  source : SourceSelection ⟨s.base,q⟩
  fresh : FreshOutput source
  kept : StoredSelection s source
  single : s.retained.length = 1

theorem LocalSelection.actual_single_row {s q} (a : LocalSelection s q) :
    s.retained = [a.kept.row] := by
  have count := a.single
  have member := a.kept.member
  generalize hs : s.retained = rows at count member ⊢
  cases rows with
  | nil => simp at count
  | cons r rest =>
    cases rest with
    | nil => exact congrArg (fun x => [x]) (List.mem_singleton.mp member).symm
    | cons x xs => simp at count

theorem LocalSelection.has_fit_of_old_fit {s q} (a : LocalSelection s q)
    (m : I72.Model) (base : Fits s.base m) : ∃ n, FitsFull s n :=
  matched_fresh_singleton_has_fit_if_old_fits445 a.fresh a.kept a.actual_single_row m base

def LocalSelection.report {s q} (a : LocalSelection s q) : Result :=
  ⟨.selected a.source.origin.decl.id [],.selected a.source.dictionary,
    Check408.encodedEventWrites a.source.origin.event⟩

def RLocalFull (s : FullState) (q : I72.Request) (r : CommonRoleOutermostResolver.Result) : Prop :=
  RefPositions441.R21 s.base q r ∨ ∃ a : LocalSelection s q, r = .selected a.source.dictionary

theorem local_R21_case_in_full (s : I72.State) (q : I72.Request)
    (r : CommonRoleOutermostResolver.Result) (old : RefPositions441.R21 s q r) :
    RLocalFull (liftState s) q r := .inl old

theorem dictionary_sound : ∀ s q d, RLocalFull s q (.selected d) →
    ∀ m, FitsFull s m → CompletedEntry438.DictionaryEvidence18 s.base m q d := by
  intro s q d picked m fit
  rcases picked with old | ⟨a,key⟩
  · exact RefPositions441.dictionary_sound_R21 s.base q d old m fit.1
  · have same := CommonRoleOutermostResolver.Result.selected.inj key
    subst d
    exact .previous (source_event_dictionary445 a.source m fit.1
      (stored_selection_fixed_targets445 a.kept m fit))

def ClassifiedAsFull (s : FullState) (q : I72.Request) (r : Result) : Prop :=
  RefPositions441.ClassifiedAs s.base q r ∨ ∃ a : LocalSelection s q, r = a.report

def ReportEvidenceFull (s : FullState) (m : I72.Model) (q : I72.Request) (r : Result) : Prop :=
  RefPositions441.ReportEvidence s.base m q r ∨
    ∃ a : LocalSelection s q, r = a.report ∧
      I72.DictionaryEvidence s.base m q a.source.dictionary ∧ FixedTargets m a.source.origin.event

def readSource (p : Problem) (w : RefPositions441.Wire) : Option (SourceSelection p) :=
  match hit : replay442 p w with
  | none => none
  | some source => source.readOwnRefOutput.map (fun own => ⟨source,replay_exact_selected_head445 hit,own⟩)

def matchesSelection (p : FullProblem) (source : SourceSelection p.old) : Bool :=
  checkFresh source &&
    (decide (p.state.retained.length = 1) &&
      p.state.retained.any (fun row => rowMatches row (eventKey source)))

theorem matches_selection_exact445 {p : FullProblem} {source : SourceSelection p.old}
    (ok : matchesSelection p source = true) :
    ∃ a : LocalSelection p.state p.root, a.source = source := by
  unfold matchesSelection at ok
  obtain ⟨fresh,rest⟩ := Bool.and_eq_true_iff.mp ok
  obtain ⟨one,hit⟩ := Bool.and_eq_true_iff.mp rest
  obtain ⟨kept⟩ := read_stored_selection445 hit
  exact ⟨⟨source,(check_fresh_exact445 _).mp fresh,kept,of_decide_eq_true one⟩,rfl⟩

def sourceReport {p : Problem} (source : SourceSelection p) : Result :=
  ⟨.selected source.origin.decl.id [],.selected source.dictionary,
    Check408.encodedEventWrites source.origin.event⟩

/-- The new witness contains only the existing raw input locator and
escape data. State supplies the original typed output and retained row;
the witness never supplies a semantic certificate or selected result. -/
inductive Witness where
  | previous (w : RefPositions441.Witness)
  | mixedOutput (input : RefPositions441.Wire)

def check_full (p : FullProblem) (r : Result) : Witness → Bool
  | .previous w => RefPositions441.check p.old r w
  | .mixedOutput w =>
    match readSource p.old w with
    | none => false
    | some source => matchesSelection p source && matchesAssociatedReport432 r (sourceReport source)

theorem all_R21_Bool_unchanged_on_lift445 (p : Problem) (r : Result) (w : RefPositions441.Witness) :
    check_full (liftProblem p) r (.previous w) = RefPositions441.check p r w := by
  cases p
  rfl

theorem check_full_sound (p : FullProblem) (r : Result) (w : Witness)
    (yes : check_full p r w = true) :
    ClassifiedAsFull p.state p.root r ∧
      ∀ m : I72.Model, FitsFull p.state m → ReportEvidenceFull p.state m p.root r := by
  cases w with
  | previous w =>
    have ⟨classifies,evidence⟩ := RefPositions441.check_sound p.old r w yes
    exact ⟨.inl classifies,fun m fit => .inl (evidence m fit.1)⟩
  | mixedOutput w =>
    simp only [check_full] at yes
    cases got : readSource p.old w with
    | none => simp [got] at yes
    | some source =>
      rw [got] at yes
      obtain ⟨matched,reported⟩ := Bool.and_eq_true_iff.mp yes
      obtain ⟨a,same⟩ := matches_selection_exact445 matched
      have report : r = a.report := by
        change r = sourceReport a.source
        rw [same]
        exact (matches_associated_report_exact432 _ _).mp reported
      refine ⟨.inr ⟨a,report⟩,fun m fit => ?_⟩
      have exactTargets := stored_selection_fixed_targets445 a.kept m fit
      exact .inr ⟨a,report,source_event_dictionary445 a.source m fit.1 exactTargets,exactTargets⟩

/-- Reification for the supported source-reader slice. The premises
are the independent local rule and actual input replay, not a proof
of the new checker, model existence, or caller's proposed report. -/
theorem actual_replay_reifies_local_witness445 (p : FullProblem)
    (a : LocalSelection p.state p.root)
    (w : RefPositions441.Wire) (read : readSource p.old w = some a.source) :
    check_full p a.report (.mixedOutput w) = true := by
  simp only [check_full,read]
  apply Bool.and_eq_true_iff.mpr
  refine ⟨?_,(matches_associated_report_exact432 _ _).mpr rfl⟩
  apply Bool.and_eq_true_iff.mpr
  refine ⟨(check_fresh_exact445 _).mpr a.fresh,?_⟩
  exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true a.single,stored_selection_matches445 a.kept⟩

end Yulang.GeneralDeclarativeI65.I72.RetainedFull445
