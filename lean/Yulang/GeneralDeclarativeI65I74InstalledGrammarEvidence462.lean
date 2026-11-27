import Yulang.GeneralDeclarativeI65I74SameRawProgram462

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.InstalledProtocolSum462
open EligibleFieldStart461 WrittenPattern460 IdenticalTagProjection459
open Checker408 (Problem)
open GeneralDeclarations (Declaration)
open GeneralDeclarationPatterns (Pattern normalize)
open RecordTree455 (Written WrittenArgs)
open GeneralDeclarativeWitnessModeCoverage357 (Covers CoversList)
open RoutedNominalMixed456 (actualQueryDecoder)

theorem ready457_normalized_original_head_preserves_closed_coverage
    {p : Problem} {d : Declaration}
    (h : RoutedReadyHeader457.AuthoredHeader p (actualQueryDecoder p.state.core) d) :
    Written h.emptyKey (normalize h.written) ∧ Covers p.state.core.current.environment (normalize h.written) := by
  have source := h.admissibleHead
  have coverage := h.preserved.covered.1
  rw [h.head] at source coverage
  cases source with
  | cons term rest => exact normalized_covered_written_source term coverage.1


private theorem prune_arity (xs : List Pattern) : (pruneRepeatedTagsArgs xs).length = xs.length := by
  induction xs <;> simp_all [pruneRepeatedTagsArgs]

mutual
  theorem binary_prune_retains_exact_source_modes {env : GeneralDeclarativeWitnessConstructorModes357.Environment}
      (p : Pattern) (ok : Covers env p) : Covers env (pruneRepeatedTags p) := by
    cases p with
    | var => exact ok
    | app k args =>
      exact ⟨(prune_arity args).symm ▸ ok.1,binary_prune_retains_exact_source_arg_modes args ok.2⟩
    | record label p t =>
      exact ⟨binary_prune_retains_exact_source_modes p ok.1,binary_prune_retains_exact_source_modes t ok.2⟩
    | variant k p => exact binary_prune_retains_exact_source_modes p ok
    | join p q =>
      unfold pruneRepeatedTags
      split
      · exact binary_prune_retains_exact_source_modes p ok.1
      · exact ⟨binary_prune_retains_exact_source_modes p ok.1,binary_prune_retains_exact_source_modes q ok.2⟩
  theorem binary_prune_retains_exact_source_arg_modes {env : GeneralDeclarativeWitnessConstructorModes357.Environment}
      (ps : List Pattern) (ok : CoversList env ps) : CoversList env (pruneRepeatedTagsArgs ps) := by
    cases ps with
    | nil => exact ok
    | cons p ps =>
      exact ⟨binary_prune_retains_exact_source_modes p ok.1,binary_prune_retains_exact_source_arg_modes ps ok.2⟩
end

theorem earlier_binary_projected_author_normal_form_keeps_closure
    {p : Problem} {d : Declaration}
    (h : ProjectedReadyHeader459.AuthoredHeader p (actualQueryDecoder p.state.core) d) :
    Written h.emptyKey (normalize h.written) ∧ Covers p.state.core.current.environment (normalize h.written) := by
  have source := h.admissibleHead
  have coverage := h.preserved.cover.1
  rw [h.head] at source coverage
  have e := same_normalization_under_every_capture459 h.written Pattern.var
  rw [identity_capture_spells_original459,identity_capture_spells_original459] at e
  rw [← e]
  change WrittenArgs _ [pruneRepeatedTags h.written] at source
  cases source with
  | cons term rest =>
    exact normalized_covered_written_source term (binary_prune_retains_exact_source_modes _ coverage.1)


theorem all_existing_provider_results_have_original_grammar
    {p : Problem} {i : Provider} {key : Nat} {a : EligibleStart p}
    (read : readActualHeader (provider p i) key = some a) : SourceGrammar a := by
  obtain ⟨d,h,rfl⟩ := (genuine_independent_start_iff_finite_header_ticket _ _).mp ⟨key,read⟩
  cases i with
  | plain =>
    refine ⟨h.emptyKey,query_empty_key_exact.mpr h.actualEmpty,?_⟩
    simpa only [ActualClosedSyntax,provider,alreadyReady,fromReady,normalized_reencodes_exactly,write_read_term] using
      ready457_normalized_original_head_preserves_closed_coverage h
  | projected =>
    refine ⟨h.emptyKey,query_empty_key_exact.mpr h.actualEmpty,?_⟩
    simpa only [ActualClosedSyntax,provider,alreadyProjected,fromProjected,normalized_reencodes_exactly,write_read_term] using
      earlier_binary_projected_author_normal_form_keeps_closure h
  | homogeneous =>
    refine ⟨h.emptyKey,query_empty_key_exact.mpr h.actualEmpty,?_⟩
    simpa only [ActualClosedSyntax,provider,alreadyHomogeneous,fromHomogeneous,normalized_reencodes_exactly,write_read_term] using
      existing_homogeneous_header_normal_form_stays_closed_and_authored h

end Yulang.GeneralDeclarativeI65.I72.InstalledProtocolSum462
