import Yulang.GeneralDeclarativeI65I74AuthoredNormalScope461
import Yulang.GeneralDeclarativeI65I74ActualRawNominalMode461
import Yulang.GeneralDeclarativeI65I74CompilerOperatorScope461
import Yulang.GeneralDeclarativeI65I74ExactCanonicalEligible461

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.EligibleFieldStart461
open WrittenPattern460
open GeneralDeclarationPatterns (Pattern)
open GeneralDeclarativeWitnessModeCoverage357 (Covers CoversList)
open AuthoredInspectQuery456 (AuthoredQuery)
open RecordTree455 (Written WrittenArgs ClosedTail)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralCandidateInspection (Primitive)
open InlineStructuralPolicy458 (policy)
open RecordTraversal455.MixedQA (ChildAt)

def ActualClosedSyntax (s : CoreState) (empty : Nat) (t : Term) : Prop :=
  Written empty (writeTerm t) ∧ Covers s.current.environment (writeTerm t)

theorem first_visible_child_remains_in_authored_closed_syntax {s empty l t u}
    (path : FirstField l t u) (source : ActualClosedSyntax s empty t) :
    ActualClosedSyntax s empty u := by
  induction path with
  | here =>
    obtain ⟨written,cover⟩ := source
    change Written empty (.record _ _ _) at written
    cases written with
    | record payload tail spine =>
      exact ⟨payload,cover.1⟩
  | later ne sub ih =>
    obtain ⟨written,cover⟩ := source
    change Written empty (.record _ _ _) at written
    cases written with
    | record payload tail spine =>
      exact ih ⟨tail,cover.2⟩

theorem actual_selected_child_stays_in_same_closed_source
    {s empty t addr u} (source : ActualClosedSyntax s empty t)
    (take : Step (queryKeys s) t addr u) : ActualClosedSyntax s empty u := by
  cases take with
  | field _ first => exact first_visible_child_remains_in_authored_closed_syntax first source
  | tag =>
    obtain ⟨written,cover⟩ := source
    change Written empty (.variant _ _) at written
    cases written with
    | variant payload => exact ⟨payload,cover⟩
  | pair0 key =>
    obtain ⟨written,cover⟩ := source
    change Written empty (.app _ (_ :: _)) at written
    cases written with
    | app args =>
      cases args with
      | cons p _ => exact ⟨p,cover.2.1⟩
  | pair1 key =>
    obtain ⟨written,cover⟩ := source
    change Written empty (.app _ (_ :: _ :: _)) at written
    cases written with
    | app args =>
      cases args with
      | cons _ tail =>
        cases tail with
        | cons q _ => exact ⟨q,cover.2.2.1⟩
  | point key =>
    obtain ⟨written,cover⟩ := source
    change Written empty (.app _ [_]) at written
    cases written with
    | app args =>
      cases args with
      | cons p _ => exact ⟨p,cover.2.1⟩

theorem old_closed_tail_has_current_compiler_empty_witness {s empty t}
    (actual : queryKeys s empty = .emptyRow) (h : ClosedTail empty (writeTerm t)) :
    ClosedSpine (queryKeys s) t := by
  cases t with
  | var | variant | join => cases h
  | record label p t =>
    change ClosedTail empty (.record label (writeTerm p) (writeTerm t)) at h
    cases h with
    | field tail =>
      exact .next (old_closed_tail_has_current_compiler_empty_witness actual tail)
  | app name args =>
    change ClosedTail empty (.app name (writeArgs args)) at h
    cases args with
    | nil =>
      cases h
      exact .empty actual
    | cons => cases h

private theorem pair_query_has_actual_pair_scope {s : CoreState} {t : Term} {op qs i next}
    (auth : AuthoredQuery s (writeTerm t) (.primitive op qs))
    (written : qs[i]? = some next) :
    CompiledOpening s t (.primitive op qs) (.primitive op i) := by
  have arity := actual_compiled_primitive_has_exact_primitive_arity auth
  have index := (List.getElem?_eq_some_iff.mp written).1
  cases op with
  | scalar _ | emptyRecord | exactEmpty =>
    simp [Primitive.parameters] at arity
    subst qs
    simp at index
  | pair =>
    have count : qs.length = 2 := arity
    have inRange : i = 0 ∨ i = 1 := by omega
    cases qs with
    | nil => cases count
    | cons p ps =>
      cases ps with
      | nil => cases count
      | cons q rest =>
        cases rest with
        | cons _ _ => simp at count
        | nil =>
          rcases inRange with rfl|rfl
          · exact .pair0
          · exact .pair1

private theorem closed_compiled_record_has_actual_field_scope {s : CoreState} {empty t l p tail f}
    (emptyActual : queryKeys s empty = .emptyRow)
    (source : ActualClosedSyntax s empty t)
    (auth : AuthoredQuery s (writeTerm t) (.record l p tail)) :
    CompiledOpening s t (.record l p tail) (.field f) := by
  cases t
  case var | variant | join => cases auth
  case app name args =>
    change AuthoredQuery s (.app name (writeArgs args)) _ at auth
    cases auth with
    | app _ actual =>
      rcases authored_application_keeps_ordered_args actual with ⟨_,wrong⟩ | ⟨_,wrong⟩ <;> cases wrong
  case record label pl rest =>
    change AuthoredQuery s (.record label (writeTerm pl) (writeTerm rest)) _ at auth
    cases auth with
    | record first right =>
      have plain := source.1
      change Written empty (.record _ (writeTerm pl) (writeTerm rest)) at plain
      cases plain with
      | record _ _ closedTail =>
        exact .field (closed_written_spine_compiles_closed
          (old_closed_tail_has_current_compiler_empty_witness emptyActual closedTail) right)

theorem actual_authorized_previous_raw_hop_has_same_written_scope
    {s : CoreState} {empty root t e addr child q use}
    (emptyActual : queryKeys s empty = .emptyRow)
    (source : ActualClosedSyntax s empty t)
    (auth : AuthoredQuery s (writeTerm t) e)
    (actual : AuthenticatedHop458.AtStep s.current.ordinary (policy s) root e addr child q use) :
    CompiledOpening s t e addr := by
  have factual := actual
  obtain ⟨row,_,sh,_,shape,pick,_⟩ := factual
  cases pick with
  | primitive raw code => exact pair_query_has_actual_pair_scope auth code
  | variant => exact .tag
  | field => exact closed_compiled_record_has_actual_field_scope emptyActual source auth
  | @nominal raw i child args q key got code =>
    obtain ⟨atZero,mode⟩ := actual_earlier_nominal_raw_hop_reads_the_same_declared_unary_operator actual
    obtain ⟨sub,done,orig,single,cov,authChild⟩ :=
      earlier_nominal_compiled_and_raw_modes_share_original_term source.2 auth mode
    have real : t = .app key (.cons (readTerm sub) .nil) := by
      rw [← read_write_term t,orig]
      rfl
    subst i args t
    exact .point cov

theorem old_raw_trail_has_authored_scope_without_extra_path_assumptions
    {s : CoreState} {empty root t e path terminal used}
    (originalEmpty : queryKeys s empty = .emptyRow)
    (source : ActualClosedSyntax s empty t)
    (auth : AuthoredQuery s (writeTerm t) e)
    (raw : AuthenticatedHop458.Trail s.current.ordinary (policy s) root e path terminal used) :
    ∃ last : Term, CompiledTrail s root t e path terminal last used := by
  induction raw generalizing t with
  | stop rigid => exact ⟨t,.stop auth rigid⟩
  | down safe step rest ih =>
    have scope := actual_authorized_previous_raw_hop_has_same_written_scope originalEmpty source auth step
    have proof := step
    obtain ⟨_,_,sh,_,_,actual,_⟩ := proof
    obtain ⟨u,written,decoded⟩ := compiled_scope_reflects_exact_selected_step auth scope actual
    obtain ⟨last,kept⟩ := ih (actual_selected_child_stays_in_same_closed_source source written) decoded
    exact ⟨last,.down auth safe step written kept⟩

open Checker408 (Problem)
open RetainedFull445 (FullProblem)
open RoutedReadyMixed457 (ReportAtField)
open RoutedNominalMixed456 (actualQueryDecoder)
open GeneralDeclarationPatterns (normalize)

theorem every_existing_homogeneous_derivation_has_its_original_inductive_grammar
    {p : Problem} (raw : HomogeneousClosedEntry459.FieldDerivation p) :
    LegacyScoped p raw.report := by
  have form := existing_homogeneous_header_normal_form_stays_closed_and_authored raw.source
  have source : ActualClosedSyntax p.state.core raw.source.emptyKey
      (normalized (readTerm raw.source.written)) := by
    simpa only [ActualClosedSyntax,normalized_reencodes_exactly,write_read_term] using form
  have empty : queryKeys p.state.core raw.source.emptyKey = .emptyRow :=
    query_empty_key_exact.mpr raw.source.actualEmpty
  have author := anchor_compiles_the_normalized_original (fromHomogeneous raw.source).anchor
  obtain ⟨last,sc⟩ := old_raw_trail_has_authored_scope_without_extra_path_assumptions empty source author raw.visited
  exact ⟨raw.declaration,raw.source,last,full_trace_reflects_exact_compiled_scope sc,
    raw.fieldEnd,raw.cycle,rfl⟩

/-- Exact already-installed C459 field arm (not every previous arm,
every source declaration, or a new branch). No separate scope premise:
it is recovered from the existing original header and actual raw opens. -/
theorem installed_homogeneous_field_exactly_reifies_independent_structural_scope
    (p : FullProblem) (r : ReportAtField) :
    (∃ w, HomogeneousClosedEntry459.check_full_homogeneous459 p (.fieldK2 r) (.fieldK2 w) = true)
      ↔ LegacyScoped p.old r := by
  constructor
  · rintro ⟨w,checked⟩
    obtain ⟨old,exact⟩ := (HomogeneousClosedEntry459.check_full_sound459 _ _ _ checked).1
    rw [← exact]
    exact every_existing_homogeneous_derivation_has_its_original_inductive_grammar old
  · exact legacy_scoped_case_passes_exact_existing_cumulative_check

end Yulang.GeneralDeclarativeI65.I72.EligibleFieldStart461
