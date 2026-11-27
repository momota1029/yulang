import Yulang.GeneralDeclarativeI65I74IndependentHomogeneousField459
import Yulang.GeneralDeclarativeI65I74InductiveTagProjection459

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.EmptyKeyContinuity459
open GeneralDeclarationPatterns
open RecordTree455 (ClosedTail Written WrittenArgs)
open IdenticalTagProjection459 (pruneRepeatedTags pruneRepeatedTagsArgs isRepeatedTag)
open InductiveTagProjection459 (Projects ProjectsArgs exactly_written_duplicate_test459)
open NestedIdenticalTagProjection459 (ActualFamily projected projectedArgs exact_original_family_presence459)
open ClosedOriginalTagGrammar459 (auxiliary_projection_never_creates_a_closed_tail459)
open HomogeneousWrittenTags459 (Family read)

mutual
  def Anchor (key : Nat) : Pattern → Prop
    | .var _ => False
    | .app _ args => Anchors key args
    | .record _ f t => ClosedTail key t ∨ Anchor key f ∨ Anchor key t
    | .variant _ p => Anchor key p
    | .join p q => Anchor key p ∨ Anchor key q
  def Anchors (key : Nat) : List Pattern → Prop
    | [] => False
    | p::ps => Anchor key p ∨ Anchors key ps
end

theorem old_projection_preserves_terminal_literal459 (key : Nat) (p : Pattern) :
    ClosedTail key (pruneRepeatedTags p) ↔ ClosedTail key p := by
  constructor
  · intro tail
    cases p with
    | var => cases tail
    | app k args =>
      cases args
      · exact tail
      · cases tail
    | variant k p => cases tail
    | record l f t =>
      cases tail with
      | field x => exact .field ((old_projection_preserves_terminal_literal459 key t).mp x)
    | join f t =>
      by_cases yes : isRepeatedTag f t = true
      · obtain ⟨k,value,rfl,rfl⟩ := (exactly_written_duplicate_test459 ..).mp yes
        simp only [pruneRepeatedTags,yes,ite_true] at tail
        cases tail
      · simp only [pruneRepeatedTags,ite_eq_right yes] at tail
        cases tail
  · intro tail
    induction tail with
    | closed => exact .closed
    | field _ ih => exact .field ih
termination_by sizeOf p

mutual
  theorem old_projection_preserves_anchor459 (key : Nat) :
      ∀ p : Pattern, Anchor key (pruneRepeatedTags p) ↔ Anchor key p
    | .var _ => Iff.rfl
    | .app _ ps => by
      simpa only [pruneRepeatedTags,Anchor] using old_projection_preserves_anchors459 key ps
    | .variant _ p => by
      simpa only [pruneRepeatedTags,Anchor] using old_projection_preserves_anchor459 key p
    | .record _ p q => by
      simp only [pruneRepeatedTags,Anchor,old_projection_preserves_terminal_literal459 key q,
        old_projection_preserves_anchor459 key p,old_projection_preserves_anchor459 key q]
    | .join p q => by
      by_cases yes : isRepeatedTag p q = true
      · obtain ⟨tag,body,pEq,qEq⟩ := (exactly_written_duplicate_test459 ..).mp yes
        have eq : p = q := pEq.trans qEq.symm
        clear pEq qEq
        subst q
        have prior := old_projection_preserves_anchor459 key p
        simp only [pruneRepeatedTags,yes,ite_true,Anchor,or_self]
        exact prior
      · simp only [pruneRepeatedTags,ite_eq_right yes,Anchor,old_projection_preserves_anchor459 key p,
          old_projection_preserves_anchor459 key q]
  theorem old_projection_preserves_anchors459 (key : Nat) :
      ∀ ps : List Pattern, Anchors key (pruneRepeatedTagsArgs ps) ↔ Anchors key ps
    | [] => Iff.rfl
    | p::ps => by simp only [pruneRepeatedTagsArgs,Anchors,old_projection_preserves_anchor459 key p,
        old_projection_preserves_anchors459 key ps]
end

theorem exact_original_family_repeats_only_same_anchors459 {p tag body count}
    (all : Family p tag body count) (key : Nat) :
    Anchor key p ↔ Anchor key body := by
  induction all with
  | leaf => exact Iff.rfl
  | join a b left right => simp [Anchor,left,right]

theorem exact_family_first_anchors_match_original459 {p q}
    (same : ActualFamily (.join p q)) (key : Nat) :
    Anchor key p ↔ Anchor key (.join p q) := by
  obtain ⟨_,_,_,a⟩ := same
  have all := exact_original_family_repeats_only_same_anchors459 a key
  cases a with
  | join first _ =>
    exact (exact_original_family_repeats_only_same_anchors459 first key).trans all.symm

mutual
  theorem homogeneous_projection_preserves_anchor459 (key : Nat) :
      ∀ p : Pattern, Anchor key (projected p) ↔ Anchor key p
    | .var _ => Iff.rfl
    | .app _ ps => by
      simpa only [projected,Anchor] using homogeneous_projection_preserves_anchors459 key ps
    | .variant _ p => by
      simpa only [projected,Anchor] using homogeneous_projection_preserves_anchor459 key p
    | .record _ p q => by
      simp only [projected,Anchor,auxiliary_projection_never_creates_a_closed_tail459 key q,
        homogeneous_projection_preserves_anchor459 key p,homogeneous_projection_preserves_anchor459 key q]
    | .join p q => by
      by_cases yes : (read (.join p q)).isSome = true
      · simp only [projected,yes,ite_true]
        exact (homogeneous_projection_preserves_anchor459 key p).trans
          (exact_family_first_anchors_match_original459 ((exact_original_family_presence459 _).mp yes) key)
      · simp only [projected,ite_eq_right yes,Anchor,homogeneous_projection_preserves_anchor459 key p,
          homogeneous_projection_preserves_anchor459 key q]
  theorem homogeneous_projection_preserves_anchors459 (key : Nat) :
      ∀ ps : List Pattern, Anchors key (projectedArgs ps) ↔ Anchors key ps
    | [] => Iff.rfl
    | p::ps => by simp only [projectedArgs,Anchors,homogeneous_projection_preserves_anchor459 key p,
        homogeneous_projection_preserves_anchors459 key ps]
end

theorem original_closed_tail_has_one_literal_key459 {key other : Nat} {t : Pattern}
    (first : ClosedTail key t) (last : ClosedTail other t) : key = other := by
  induction first with
  | closed => cases last; rfl
  | field f ih => cases last with | field l => exact ih l

mutual
  theorem written_anchors_are_exact_constant459 {e : Nat}
      : ∀ {p}, Written e p → ∀ k, Anchor k p → k = e
    | _,.var,_,h => h.elim
    | _,.app ps,_,h => written_argument_anchors_are_exact_constant459 ps _ h
    | _,.variant p,_,h => written_anchors_are_exact_constant459 p _ h
    | _,.record p q t,_,h => by
      rcases h with atTail | atPayload | further
      · exact original_closed_tail_has_one_literal_key459 atTail t
      · exact written_anchors_are_exact_constant459 p _ atPayload
      · exact written_anchors_are_exact_constant459 q _ further
  theorem written_argument_anchors_are_exact_constant459 {e : Nat}
      : ∀ {ps}, WrittenArgs e ps → ∀ k, Anchors k ps → k = e
    | _,.nil,_,h => h.elim
    | _,.cons p ps,_,h => by
      rcases h with first | rest
      · exact written_anchors_are_exact_constant459 p _ first
      · exact written_argument_anchors_are_exact_constant459 ps _ rest
end

mutual
  theorem exact_new_key_when_all_original_anchors_agree459 {e other : Nat} :
      ∀ {p}, Written e p → (∀ k, Anchor k p → k = other) → Written other p
    | _,.var,_ => .var
    | _,.app ps,all => .app (exact_new_key_in_args_when_anchors_agree459 ps all)
    | _,.variant p, all => .variant (exact_new_key_when_all_original_anchors_agree459 p all)
    | _,.record p q t,all => by
      refine .record (exact_new_key_when_all_original_anchors_agree459 p fun k a => all k (.inr (.inl a)))
        (exact_new_key_when_all_original_anchors_agree459 q fun k a => all k (.inr (.inr a))) ?_
      exact all e (.inl t) ▸ t
  theorem exact_new_key_in_args_when_anchors_agree459 {e other : Nat} :
      ∀ {ps}, WrittenArgs e ps → (∀ k, Anchors k ps → k = other) → WrittenArgs other ps
    | _,.nil,_ => .nil
    | _,.cons p ps,all =>
      .cons (exact_new_key_when_all_original_anchors_agree459 p fun k a => all k (.inl a))
        (exact_new_key_in_args_when_anchors_agree459 ps fun k a => all k (.inr a))
end

/-- If both projections read their respective real closed source, the older
binary projection can use the homogeneous checker’s key. No assumption of a
unique empty primitive in the original registry is needed. -/
theorem old_closed_projection_transports_to_new_original_key459 {oldKey newKey : Nat} {ps}
    (old : WrittenArgs oldKey (pruneRepeatedTagsArgs ps)) (fresh : WrittenArgs newKey (projectedArgs ps)) :
    WrittenArgs newKey (pruneRepeatedTagsArgs ps) := by
  refine exact_new_key_in_args_when_anchors_agree459 old ?_
  intro key seen
  have original := (old_projection_preserves_anchors459 key ps).mp seen
  exact written_argument_anchors_are_exact_constant459 fresh key
    ((homogeneous_projection_preserves_anchors459 key ps).mpr original)


open Yulang.GeneralDeclarativeI65
open Checker408 (Problem)
open RetainedFull445 (FullProblem)
open RoutedReadyMixed457 (ReportAtField)
open GeneralDeclarations (Declaration)
open RecordTree455 (checkTrees_exact)

mutual
  theorem old_projection_is_identity_on_already_written459 {empty : Nat}
    : ∀ {p}, Written empty p → pruneRepeatedTags p = p
    | _,.var => rfl
    | _,.app args => by simp [pruneRepeatedTags,old_projection_is_identity_on_written_args459 args]
    | _,.variant p => by simp [pruneRepeatedTags,old_projection_is_identity_on_already_written459 p]
    | _,.record p q _ => by
      simp [pruneRepeatedTags,old_projection_is_identity_on_already_written459 p,
        old_projection_is_identity_on_already_written459 q]
  theorem old_projection_is_identity_on_written_args459 {empty : Nat}
    : ∀ {ps}, WrittenArgs empty ps → pruneRepeatedTagsArgs ps = ps
    | _,.nil => rfl
    | _,.cons p ps => by simp [pruneRepeatedTagsArgs,old_projection_is_identity_on_already_written459 p,
      old_projection_is_identity_on_written_args459 ps]
end

theorem new_original_header_excludes_an_old_binary_spelling_at_any_key459
    {p q d} (new : HomogeneousReadyHeader459.AuthoredHeader p q d) (key : Nat)
    (old : WrittenArgs key (pruneRepeatedTagsArgs d.head)) : False := by
  have available := (checkTrees_exact ..).mpr
    (old_closed_projection_transports_to_new_original_key459 old new.admissibleHead)
  rw [new.oldWrittenSpellingUnavailable] at available
  cases available

theorem homogeneous_exact_branch_cannot_overlap_older_binary_exact_branch459
    (p : FullProblem) (nreport oldreport : ReportAtField)
    (nw : HomogeneousClosedEntry459.FieldWire) (ow : ProjectedClosedEntry459.FieldWire)
    (found : HomogeneousClosedEntry459.check_full_homogeneous459 p (.fieldK2 nreport) (.fieldK2 nw) = true) :
    ProjectedClosedEntry459.check_full_projected459 p (.fieldK2 oldreport) (.fieldK2 ow) = false := by
  cases other : ProjectedClosedEntry459.check_full_projected459 p (.fieldK2 oldreport) (.fieldK2 ow)
  · rfl
  · exfalso
    obtain ⟨new,same⟩ := (HomogeneousClosedEntry459.check_full_sound459 p _ _ found).1
    obtain ⟨old,oldSame⟩ := (ProjectedClosedEntry459.check_full_sound459 p _ _ other).1
    have d := congrArg Declaration.head (List.singleton_inj.mp (old.source.only.symm.trans new.source.only))
    have oldSyntax := old.source.admissibleHead
    rw [d] at oldSyntax
    exact new_original_header_excludes_an_old_binary_spelling_at_any_key459 new.source _ oldSyntax

theorem homogeneous_exact_branch_cannot_overlap_adopted_c458_exact_branch459
    (p : FullProblem) (nreport oldreport : ReportAtField)
    (nw : HomogeneousClosedEntry459.FieldWire) (ow : RoutedInlineStructural458.FieldWire)
    (found : HomogeneousClosedEntry459.check_full_homogeneous459 p (.fieldK2 nreport) (.fieldK2 nw) = true) :
    RoutedInlineStructural458.check_full_structural458 p (.fieldK2 oldreport) (.fieldK2 ow) = false := by
  cases other : RoutedInlineStructural458.check_full_structural458 p (.fieldK2 oldreport) (.fieldK2 ow)
  · rfl
  · exfalso
    obtain ⟨new,same⟩ := (HomogeneousClosedEntry459.check_full_sound459 p _ _ found).1
    obtain ⟨old,oldSame⟩ := (RoutedInlineStructural458.check_full_sound458 p _ _ other).1
    have d := congrArg Declaration.head (List.singleton_inj.mp (old.source.only.symm.trans new.source.only))
    have oldSyntax := old.source.admissibleHead
    have known : WrittenArgs old.source.emptyKey (pruneRepeatedTagsArgs old.declaration.head) :=
      (old_projection_is_identity_on_written_args459 oldSyntax).symm ▸ oldSyntax
    rw [d] at known
    exact new_original_header_excludes_an_old_binary_spelling_at_any_key459 new.source _ known

end Yulang.GeneralDeclarativeI65.I72.EmptyKeyContinuity459
