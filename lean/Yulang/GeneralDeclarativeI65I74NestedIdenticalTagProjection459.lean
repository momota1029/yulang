import Yulang.GeneralDeclarativeI65I74HomogeneousWrittenTags459
import Yulang.GeneralDeclarativeI65I74IdenticalTagProjection459

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.NestedIdenticalTagProjection459
open GeneralDeclarationPatterns
open HomogeneousWrittenTags459 (Family read exact_independent_literal_family459
  exact_homogeneous_house_normalizes_after_every_capture459)

def ActualFamily (p : Pattern) : Prop := ∃ tag payload count, Family p tag payload count

theorem exact_original_family_presence459 (p : Pattern) :
    (read p).isSome = true ↔ ActualFamily p := by
  constructor
  · intro ok
    cases found : read p with
    | none => simp [found] at ok
    | some result =>
      obtain ⟨tag,payload,n⟩ := result
      exact ⟨tag,payload,n,exact_independent_literal_family459.mp found⟩
  · rintro ⟨tag,payload,n,author⟩
    rw [exact_independent_literal_family459.mpr author]
    rfl

mutual
  def projected : Pattern → Pattern
    | .var n => .var n
    | .app c args => .app c (projectedArgs args)
    | .record label f t => .record label (projected f) (projected t)
    | .variant tag payload => .variant tag (projected payload)
    | .join left right =>
      if (read (.join left right)).isSome then projected left
      else .join (projected left) (projected right)
  def projectedArgs : List Pattern → List Pattern
    | [] => []
    | head::tail => projected head::projectedArgs tail
end

mutual
  inductive Projection : Pattern → Pattern → Prop where
  | var : Projection (.var n) (.var n)
  | app : ProjectionArgs args out → Projection (.app key args) (.app key out)
  | record : Projection f x → Projection tail t → Projection (.record label f tail) (.record label x t)
  | variant : Projection payload out → Projection (.variant tag payload) (.variant tag out)
  | duplicates : ActualFamily (.join a b) → Projection a out → Projection (.join a b) out
  | residual : ¬ ActualFamily (.join a b) → Projection a f → Projection b l →
        Projection (.join a b) (.join f l)
  inductive ProjectionArgs : List Pattern → List Pattern → Prop where
  | nil : ProjectionArgs [] []
  | cons : Projection p q → ProjectionArgs rest out → ProjectionArgs (p::rest) (q::out)
end

mutual
  theorem projection_preserves_its_exact_data_read459 :
      ∀ {p q}, Projection p q → projected p = q
    | _,_,.var => rfl
    | _,_,.app args => by simp [projected,projection_args_preserve_their_exact_data_read459 args]
    | _,_,.variant p => by simp [projected,projection_preserves_its_exact_data_read459 p]
    | _,_,.record p r => by
       simp [projected,projection_preserves_its_exact_data_read459 p,projection_preserves_its_exact_data_read459 r]
    | _,_,.duplicates same p => by
      simp only [projected,(exact_original_family_presence459 _).mpr same,ite_true]
      exact projection_preserves_its_exact_data_read459 p
    | _,_,.residual keep f l => by
      have no := mt (exact_original_family_presence459 _).mp keep
      simp [projected,no,projection_preserves_its_exact_data_read459 f,projection_preserves_its_exact_data_read459 l]
  theorem projection_args_preserve_their_exact_data_read459 :
      ∀ {p q}, ProjectionArgs p q → projectedArgs p = q
    | _,_,.nil => rfl
    | _,_,.cons p args => by
       simp [projectedArgs,projection_preserves_its_exact_data_read459 p,projection_args_preserve_their_exact_data_read459 args]
end

mutual
  theorem projected_real_source_has_independent_derivation459 : ∀ p, Projection p (projected p)
    | .var _ => .var
    | .app _ args => .app (projected_real_source_arguments_have_derivation459 args)
    | .record _ p q => .record (projected_real_source_has_independent_derivation459 p)
        (projected_real_source_has_independent_derivation459 q)
    | .variant _ p => .variant (projected_real_source_has_independent_derivation459 p)
    | .join p q => by
      by_cases found : (read (.join p q)).isSome = true
      · simp only [projected,found,ite_true]
        exact .duplicates ((exact_original_family_presence459 _).mp found)
           (projected_real_source_has_independent_derivation459 p)
      · simp only [projected,ite_eq_right found]
        exact .residual (mt (exact_original_family_presence459 _).mpr found)
           (projected_real_source_has_independent_derivation459 p)
           (projected_real_source_has_independent_derivation459 q)
  theorem projected_real_source_arguments_have_derivation459 : ∀ args, ProjectionArgs args (projectedArgs args)
    | [] => .nil
    | p::ps => .cons (projected_real_source_has_independent_derivation459 p)
        (projected_real_source_arguments_have_derivation459 ps)
end

theorem projected_args_iff_actual_independent_occurrences459 (args out : List Pattern) :
    projectedArgs args = out ↔ ProjectionArgs args out := by
  constructor
  · rintro rfl; exact projected_real_source_arguments_have_derivation459 args
  · exact projection_args_preserve_their_exact_data_read459

theorem actual_join_same_as_first_written459 {a b : Pattern} (f : ActualFamily (.join a b))
    (capture : Nat → Pattern) :
    normalize (a.subst capture) = normalize ((Pattern.join a b).subst capture) := by
  obtain ⟨tag,payload,n,joined⟩ := f
  have j := exact_homogeneous_house_normalizes_after_every_capture459 joined capture
  cases joined with
  | join f _ =>
    exact (exact_homogeneous_house_normalizes_after_every_capture459 f capture).trans j.symm

mutual
  theorem authored_projection_preserves_normalize_under_every_capture459 :
      ∀ (p : Pattern) (c : Nat → Pattern), normalize ((projected p).subst c) = normalize (p.subst c)
    | .var _, _ => rfl
    | .app _ args, c =>
      by simp [projected,Pattern.subst,normalize,authored_args_projection_normalizes_under_every_capture459 args c]
    | .record _ p q, c => by
      simp [projected,Pattern.subst,normalize,authored_projection_preserves_normalize_under_every_capture459 p c,
        authored_projection_preserves_normalize_under_every_capture459 q c]
    | .variant _ p, c =>
      by simp [projected,Pattern.subst,normalize,authored_projection_preserves_normalize_under_every_capture459 p c]
    | .join p q, c => by
      by_cases found : (read (.join p q)).isSome = true
      · simp only [projected,found,ite_true]
        exact (authored_projection_preserves_normalize_under_every_capture459 p c).trans
          (actual_join_same_as_first_written459 ((exact_original_family_presence459 _).mp found) c)
      · simp [projected,found,Pattern.subst,normalize,authored_projection_preserves_normalize_under_every_capture459 p c,
          authored_projection_preserves_normalize_under_every_capture459 q c]
  theorem authored_args_projection_normalizes_under_every_capture459 :
      ∀ (ps : List Pattern) (c : Nat → Pattern),
        normalizeArgs (substArgs c (projectedArgs ps)) = normalizeArgs (substArgs c ps)
    | [], _ => rfl
    | p::ps,c => by
      simp [projectedArgs,substArgs,normalizeArgs,authored_projection_preserves_normalize_under_every_capture459 p c,
        authored_args_projection_normalizes_under_every_capture459 ps c]
end

theorem original_capture_counts_are_preserved459 (ps : List Pattern) (cap : Nat → Pattern) :
    counted (substArgs cap (projectedArgs ps)) = counted (substArgs cap ps) := by
  unfold counted
  rw [authored_args_projection_normalizes_under_every_capture459]

theorem original_normal_counts_are_preserved459 (ps : List Pattern) :
    counted (projectedArgs ps) = counted ps := by
  simpa only [IdenticalTagProjection459.identity_args_capture_spells_original459] using original_capture_counts_are_preserved459 ps Pattern.var

end Yulang.GeneralDeclarativeI65.I72.NestedIdenticalTagProjection459
