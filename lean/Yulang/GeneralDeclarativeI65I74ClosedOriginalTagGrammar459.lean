import Yulang.GeneralDeclarativeI65I74NestedIdenticalTagProjection459
import Yulang.GeneralDeclarativeI65I74HomogeneousReadyHeader459

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.ClosedOriginalTagGrammar459
open GeneralDeclarationPatterns
open HomogeneousWrittenTags459 (Family read)
open NestedIdenticalTagProjection459
open RecordTree455 (Written WrittenArgs ClosedTail checkTrees checkTrees_exact)

theorem entire_exact_written_family_projects_to_its_original_variant459
    {p : Pattern} {tag payload count} (family : Family p tag payload count) :
    projected p = .variant tag (projected payload) := by
  induction family with
  | leaf => rfl
  | @join first tag payload n last m a b ihA ihB =>
    have present : (read (.join first last)).isSome = true :=
      (exact_original_family_presence459 _).mpr ⟨tag,payload,n+m,.join a b⟩
    simpa only [projected,present,ite_true] using ihA

theorem underlying_original_payload_smaller459 {p tag payload count}
    (family : Family p tag payload count) : sizeOf payload < sizeOf p := by
  induction family with
  | leaf => simp; omega
  | join first _ left _ =>
    simp
    omega

theorem auxiliary_projection_never_creates_a_closed_tail459
    (empty : Nat) (p : Pattern) :
    ClosedTail empty (projected p) ↔ ClosedTail empty p := by
  constructor
  · intro valid
    cases p with
    | var => cases valid
    | app k args =>
      change ClosedTail empty (.app k (projectedArgs args)) at valid
      cases args
      · exact valid
      · cases valid
    | variant k p => cases valid
    | record l q t =>
      change ClosedTail empty (.record l (projected q) (projected t)) at valid
      cases valid with
      | field last =>
        exact .field ((auxiliary_projection_never_creates_a_closed_tail459 empty t).mp last)
    | join f l =>
      by_cases same : (read (.join f l)).isSome = true
      · obtain ⟨tag,payload,count,all⟩ := (exact_original_family_presence459 _).mp same
        rw [entire_exact_written_family_projects_to_its_original_variant459 all] at valid
        cases valid
      · simp only [projected,ite_eq_right same] at valid
        cases valid
  · intro valid
    induction valid with
    | closed => exact .closed
    | field rest ih => exact .field ih
termination_by sizeOf p

mutual
  inductive WrittenOriginal (empty : Nat) : Pattern → Prop where
    | var : WrittenOriginal empty (.var n)
    | app : WrittenOriginalArgs empty args → WrittenOriginal empty (.app key args)
    | record : WrittenOriginal empty payload → WrittenOriginal empty tail → ClosedTail empty tail →
        WrittenOriginal empty (.record label payload tail)
    | variant : WrittenOriginal empty payload → WrittenOriginal empty (.variant tag payload)
    | exactFamily : Family (.join first last) tag payload count → WrittenOriginal empty payload →
        WrittenOriginal empty (.join first last)
  inductive WrittenOriginalArgs (empty : Nat) : List Pattern → Prop where
    | nil : WrittenOriginalArgs empty []
    | cons : WrittenOriginal empty hd → WrittenOriginalArgs empty tl →
      WrittenOriginalArgs empty (hd::tl)
end

mutual
  theorem actual_original_tree_has_auxiliary_closed_proof459
      {empty} : ∀ {p}, WrittenOriginal empty p → Written empty (projected p)
    | _,.var => .var
    | _,.app args => .app (actual_original_args_have_auxiliary_closed_proof459 args)
    | _,.variant p => .variant (actual_original_tree_has_auxiliary_closed_proof459 p)
    | _,.record f r tail =>
      .record (actual_original_tree_has_auxiliary_closed_proof459 f)
        (actual_original_tree_has_auxiliary_closed_proof459 r)
        ((auxiliary_projection_never_creates_a_closed_tail459 _ _).mpr tail)
    | _,.exactFamily same p => by
      rw [entire_exact_written_family_projects_to_its_original_variant459 same]
      exact .variant (actual_original_tree_has_auxiliary_closed_proof459 p)
  theorem actual_original_args_have_auxiliary_closed_proof459
      {empty} : ∀ {ps}, WrittenOriginalArgs empty ps → WrittenArgs empty (projectedArgs ps)
    | _,.nil => .nil
    | _,.cons h t => .cons (actual_original_tree_has_auxiliary_closed_proof459 h)
        (actual_original_args_have_auxiliary_closed_proof459 t)
end

mutual
  theorem auxiliary_closed_proof_reflects_actual_original_grammar459 (empty : Nat)
      : ∀ p : Pattern, Written empty (projected p) → WrittenOriginal empty p
    | .var _, _ => .var
    | .app _ args, accepted => by
      cases accepted with
      | app argsOK => exact .app (auxiliary_closed_args_reflect_actual_original459 empty args argsOK)
    | .variant _ payload, accepted => by
      cases accepted with
      | variant good => exact .variant (auxiliary_closed_proof_reflects_actual_original_grammar459 empty payload good)
    | .record _ p q, accepted => by
      cases accepted with
      | record hp hq tail =>
        exact .record (auxiliary_closed_proof_reflects_actual_original_grammar459 empty p hp)
          (auxiliary_closed_proof_reflects_actual_original_grammar459 empty q hq)
          ((auxiliary_projection_never_creates_a_closed_tail459 empty q).mp tail)
    | .join a b, accepted => by
      by_cases same : (read (.join a b)).isSome = true
      · obtain ⟨tag,payload,count,original⟩ := (exact_original_family_presence459 _).mp same
        have smaller := underlying_original_payload_smaller459 original
        rw [entire_exact_written_family_projects_to_its_original_variant459 original] at accepted
        cases accepted with
        | variant good =>
          exact .exactFamily original
            (auxiliary_closed_proof_reflects_actual_original_grammar459 empty payload good)
      · simp only [projected,ite_eq_right same] at accepted
        cases accepted
    termination_by p => sizeOf p
  theorem auxiliary_closed_args_reflect_actual_original459 (empty : Nat)
      : ∀ ps : List Pattern, WrittenArgs empty (projectedArgs ps) → WrittenOriginalArgs empty ps
    | [], _ => .nil
    | p::ps, accepted => by
      cases accepted with
      | cons h t =>
        exact .cons (auxiliary_closed_proof_reflects_actual_original_grammar459 empty p h)
          (auxiliary_closed_args_reflect_actual_original459 empty ps t)
    termination_by ps => sizeOf ps
end

theorem finite_auxiliary_head_check_iff_original_closed_grammar459 (empty : Nat) (head : List Pattern) :
    checkTrees empty (projectedArgs head) = true ↔ WrittenOriginalArgs empty head := by
  constructor
  · exact fun yes => auxiliary_closed_args_reflect_actual_original459 empty head ((checkTrees_exact ..).mp yes)
  · exact fun original => (checkTrees_exact ..).mpr (actual_original_args_have_auxiliary_closed_proof459 original)

end Yulang.GeneralDeclarativeI65.I72.ClosedOriginalTagGrammar459
