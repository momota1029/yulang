import Yulang.GeneralDeclarativeI65I74InstalledExactScope462
import Yulang.GeneralDeclarativeI65I74EmptyKeyContinuity459
import Yulang.GeneralDeclarativeI65I74PreviousStabilityFactorization461

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.InstalledProtocolSum462
open Yulang.GeneralDeclarativeI65
open EligibleFieldStart461 EmptyKeyContinuity459
open Checker408 (Problem)
open GeneralDeclarations (Declaration)
open RoutedNominalMixed456 (actualQueryDecoder)
open IdenticalTagProjection459 (pruneRepeatedTagsArgs)

private theorem plain_excludes_binary {p : Problem} {d e : Declaration}
    (h : RoutedReadyHeader457.AuthoredHeader p (actualQueryDecoder p.state.core) d)
    (j : ProjectedReadyHeader459.AuthoredHeader p (actualQueryDecoder p.state.core) e) : False := by
  have same := List.singleton_inj.mp (h.only.symm.trans j.only)
  subst e
  exact j.genuinelyRepeated (old_projection_is_identity_on_written_args459 h.admissibleHead)

private theorem plain_excludes_homogeneous {p : Problem} {d e : Declaration}
    (h : RoutedReadyHeader457.AuthoredHeader p (actualQueryDecoder p.state.core) d)
    (j : HomogeneousReadyHeader459.AuthoredHeader p (actualQueryDecoder p.state.core) e) : False := by
  have same := List.singleton_inj.mp (h.only.symm.trans j.only)
  subst e
  exact new_original_header_excludes_an_old_binary_spelling_at_any_key459 j h.emptyKey
    ((old_projection_is_identity_on_written_args459 h.admissibleHead).symm ▸ h.admissibleHead)

private theorem binary_excludes_homogeneous {p : Problem} {d e : Declaration}
    (h : ProjectedReadyHeader459.AuthoredHeader p (actualQueryDecoder p.state.core) d)
    (j : HomogeneousReadyHeader459.AuthoredHeader p (actualQueryDecoder p.state.core) e) : False := by
  have same := List.singleton_inj.mp (h.only.symm.trans j.only)
  subst e
  exact new_original_header_excludes_an_old_binary_spelling_at_any_key459 j h.emptyKey h.admissibleHead

/-- Distinct original author tags cannot authenticate the same problem,
even at different empty keys. A shared reader therefore need not guess. -/
theorem successful_same_problem_has_only_one_existing_provider {p : Problem}
    {i j : Provider} {a b : EligibleStart p}
    (ha : actualHeaderAuthority (provider p i) a)
    (hb : actualHeaderAuthority (provider p j) b) : i = j := by
  obtain ⟨_,h,_⟩ := ha
  obtain ⟨_,k,_⟩ := hb
  cases i <;> cases j
  · rfl
  · exact (plain_excludes_binary h k).elim
  · exact (plain_excludes_homogeneous h k).elim
  · exact (plain_excludes_binary k h).elim
  · rfl
  · exact (binary_excludes_homogeneous h k).elim
  · exact (plain_excludes_homogeneous k h).elim
  · exact (binary_excludes_homogeneous k h).elim
  · rfl

theorem same_original_problem_keeps_actual_header_and_provider {p : Problem}
    {s t : Ticket} {a b : EligibleStart p}
    (first : pickHeader p s = some a) (second : pickHeader p t = some b) :
    s.author = t.author ∧ a = b := by
  have i := (genuine_independent_start_iff_finite_header_ticket (provider p s.author) a).mp ⟨s.key,first⟩
  have j := (genuine_independent_start_iff_finite_header_ticket (provider p t.author) b).mp ⟨t.key,second⟩
  exact ⟨successful_same_problem_has_only_one_existing_provider i j,
    same_eligible_original_anchor_keeps_all_start_data
      (actual_source_anchor_is_determined_by_its_positions_in_same_problem rfl)⟩

end Yulang.GeneralDeclarativeI65.I72.InstalledProtocolSum462
