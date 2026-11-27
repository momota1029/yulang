import Yulang.GeneralDeclarativeI65I74PreviousStabilityFactorization461

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.EligibleFieldStart461
open GeneralDeclarationPatterns
open GeneralDeclarativeWitnessModeCoverage357 (Covers CoversList)
open RecordTree455 (Written WrittenArgs ClosedTail)
open Checker408 (Problem)
open RoutedNominalMixed456 (actualQueryDecoder)

private theorem projectedArity (xs : List Pattern) :
    (NestedIdenticalTagProjection459.projectedArgs xs).length = xs.length := by
  induction xs <;> simp_all [NestedIdenticalTagProjection459.projectedArgs]

private theorem normalizedArity (xs : List Pattern) : (normalizeArgs xs).length = xs.length := by
  induction xs <;> simp_all [normalizeArgs]

mutual
  theorem auxiliary_projection_retains_real_constructor_coverage {e : GeneralDeclarativeWitnessConstructorModes357.Environment}
      (p : Pattern) (source : Covers e p) :
      Covers e (NestedIdenticalTagProjection459.projected p) := by
    cases p with
    | var name => exact source
    | app k args =>
      exact ⟨(projectedArity args).symm ▸ source.1,auxiliary_projection_retains_covered_argument_vector args source.2⟩
    | record k p t => exact ⟨auxiliary_projection_retains_real_constructor_coverage p source.1,
        auxiliary_projection_retains_real_constructor_coverage t source.2⟩
    | variant k p => exact auxiliary_projection_retains_real_constructor_coverage p source
    | join a b =>
      unfold NestedIdenticalTagProjection459.projected
      split
      · exact auxiliary_projection_retains_real_constructor_coverage a source.1
      · exact ⟨auxiliary_projection_retains_real_constructor_coverage a source.1,
          auxiliary_projection_retains_real_constructor_coverage b source.2⟩
  theorem auxiliary_projection_retains_covered_argument_vector {e : GeneralDeclarativeWitnessConstructorModes357.Environment}
      (xs : List Pattern) (source : CoversList e xs) :
      CoversList e (NestedIdenticalTagProjection459.projectedArgs xs) := by
    cases xs with
    | nil => exact source
    | cons a xs => exact ⟨auxiliary_projection_retains_real_constructor_coverage a source.1,
        auxiliary_projection_retains_covered_argument_vector xs source.2⟩
end

theorem covered_hidden_row_preserves_existing_spine {e empty p}
    (written : Written empty p) (covered : Covers e p) (l : Nat) :
    Written empty (hide l p) ∧ Covers e (hide l p) := by
  cases written with
  | var => exact ⟨.var,covered⟩
  | app xs => exact ⟨.app xs,covered⟩
  | variant payload => exact ⟨.variant payload,covered⟩
  | @record body tail field left right tailClosed =>
    have ih := covered_hidden_row_preserves_existing_spine right covered.2 l
    by_cases eq : l = field
    · simpa [hide,eq] using ih
    · simpa [hide,eq] using
        (show Written empty (.record field body (hide l tail)) ∧
          Covers e (.record field body (hide l tail)) from
          ⟨.record left ih.1 (RecordTree455.hide_keeps_the_closed_tail tailClosed l),covered.1,ih.2⟩)

mutual
  theorem normalized_covered_written_source {e empty p}
      (written : Written empty p) (source : Covers e p) :
      Written empty (normalize p) ∧ Covers e (normalize p) := by
    cases written with
    | var => exact ⟨.var,source⟩
    | @app args key xs =>
      have con := normalized_covered_written_arguments xs source.2
      exact ⟨.app con.1,
        ⟨(normalizedArity args).symm ▸ source.1,con.2⟩⟩
    | @record body rest lab left right tail =>
      have b := normalized_covered_written_source left source.1
      have r := normalized_covered_written_source right source.2
      have antiShadow := covered_hidden_row_preserves_existing_spine r.1 r.2 lab
      exact ⟨.record b.1 antiShadow.1 (RecordTree455.hide_keeps_the_closed_tail
        (RecordTree455.normalization_keeps_the_closed_tail tail) lab),b.2,antiShadow.2⟩
    | variant body =>
      have b := normalized_covered_written_source body source
      exact ⟨.variant b.1,b.2⟩
  theorem normalized_covered_written_arguments {e empty xs}
      (written : WrittenArgs empty xs) (source : CoversList e xs) :
      WrittenArgs empty (normalizeArgs xs) ∧ CoversList e (normalizeArgs xs) := by
    cases written with
    | nil => exact ⟨.nil,source⟩
    | cons here rest =>
      have h := normalized_covered_written_source here source.1
      have r := normalized_covered_written_arguments rest source.2
      exact ⟨.cons h.1 r.1,h.2,r.2⟩
end

theorem existing_homogeneous_header_normal_form_stays_closed_and_authored {p : Problem} {d}
    (h : HomogeneousReadyHeader459.AuthoredHeader p (actualQueryDecoder p.state.core) d) :
    Written h.emptyKey (normalize h.written) ∧
      Covers p.state.core.current.environment (normalize h.written) := by
  have w := h.admissibleHead
  have c := h.preserved.cover.1
  rw [h.head] at w c
  have exact :
      Written h.emptyKey (NestedIdenticalTagProjection459.projected h.written) := by
    change WrittenArgs _ [NestedIdenticalTagProjection459.projected h.written] at w
    cases w with | cons first => exact first
  have same := NestedIdenticalTagProjection459.authored_projection_preserves_normalize_under_every_capture459
    h.written Pattern.var
  rw [IdenticalTagProjection459.identity_capture_spells_original459,
    IdenticalTagProjection459.identity_capture_spells_original459] at same
  rw [← same]
  exact normalized_covered_written_source exact (auxiliary_projection_retains_real_constructor_coverage _ c.1)

end Yulang.GeneralDeclarativeI65.I72.EligibleFieldStart461
