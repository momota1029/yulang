import Yulang.GeneralDeclarativeI65I74ActualHeaderProtocol461

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.EligibleFieldStart461
open GeneralDeclarations (Declaration)
open WrittenPattern460
open Checker408 (Problem)
open RetainedFull445 (FullProblem)
open RoutedReadyMixed457 (ReportAtField)
open RoutedNominalMixed456 (actualQueryDecoder)
open RoutedMixed456 (endsAtField)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeGraphRows321 (observed)
open InlineStructuralPolicy458 (policy)

/-- The existing public homogeneous entry has an extra authentic-use
requirement. This narrower predicate deliberately keeps that stamp, as
well as the same original eligible header (no pre-existing Bool premise). -/
def LegacyScoped (p : Problem) (r : ReportAtField) : Prop :=
  ∃ (d : Declaration)
    (h : HomogeneousReadyHeader459.AuthoredHeader p (actualQueryDecoder p.state.core) d)
    (last : Term),
    ScopedRaw p.state.core h.arg.lower (normalized (readTerm h.written))
      h.query r.path r.terminal last true ∧
    endsAtField r.path r.terminal = true ∧
    AliasCycle p.state.core.current.ordinary (observed p.state.core.current.ordinary) r.terminal ∧
    exactReport (fromHomogeneous h).anchor r.path r.terminal = r

def AlignedLegacyDerivation (p : Problem) (r : ReportAtField) : Prop :=
  ∃ a : HomogeneousClosedEntry459.FieldDerivation p, a.report = r ∧
    ∃ terminalSyntax, CoordinateWalk (fun _ => queryKeys p.state.core) a.source.arg.lower
      (normalized (readTerm a.source.written)) a.path a.terminal terminalSyntax

theorem legacy_scope_matches_its_exact_prior_raw_derivation {p : Problem} {r : ReportAtField} :
    LegacyScoped p r ↔ AlignedLegacyDerivation p r := by
  constructor
  · rintro ⟨d,h,last,inScope,field,cycle,which⟩
    have t := exact_scope_reifies_full_trace_by_descent
      (anchor_compiles_the_normalized_original (fromHomogeneous h).anchor) inScope
    have joint := compiled_trace_has_structural_joint_trace t
    exact ⟨⟨d,h,r.path,r.terminal,joint_has_actual_raw_trace joint,cycle,field⟩,which,
      last,joint_has_exact_written_path joint⟩
  · rintro ⟨a,eq,last,written⟩
    have t := independently_aligned_lexical_and_raw_trails_compose
      (anchor_compiles_the_normalized_original (fromHomogeneous a.source).anchor) a.visited written
    have src := full_trace_reflects_exact_compiled_scope t
    have copy := eq
    subst r
    exact ⟨a.declaration,a.source,last,src,a.fieldEnd,a.cycle,rfl⟩

theorem legacy_scoped_case_is_read_by_uniform_eligible_reader {p : Problem} {r : ReportAtField}
    (src : LegacyScoped p r) :
    ∃ w, readEligibleField (exactHeaderReader (alreadyHomogeneous p)) w = some r := by
  obtain ⟨d,h,last,trace,field,cycle,eq⟩ := src
  apply (exact_eligible_scope_iff_independent_finite_route _ _).mpr
  exact ⟨fromHomogeneous h,last,true,⟨d,h,rfl⟩,trace,field,cycle,eq⟩

theorem legacy_scoped_case_passes_exact_existing_cumulative_check {p : FullProblem} {r : ReportAtField}
    (src : LegacyScoped p.old r) :
    ∃ w, HomogeneousClosedEntry459.check_full_homogeneous459 p (.fieldK2 r) (.fieldK2 w) = true := by
  obtain ⟨old,eq,_⟩ := legacy_scope_matches_its_exact_prior_raw_derivation.mp src
  exact HomogeneousClosedEntry459.independent_routed_field_derivation_has_cumulative_witness459 p r ⟨old,eq⟩

theorem legacy_scoped_case_keeps_exact_same_canonical_evidence {p : FullProblem} {r : ReportAtField}
    (src : LegacyScoped p.old r) (m : I72.Model) (fit : I72.FitsFull p.state m) :
    HomogeneousClosedEntry459.FieldEvidence p.old m r := by
  obtain ⟨w,accepted⟩ := legacy_scoped_case_passes_exact_existing_cumulative_check src
  exact (HomogeneousClosedEntry459.check_full_sound459 _ _ _ accepted).2 m fit

end Yulang.GeneralDeclarativeI65.I72.EligibleFieldStart461
