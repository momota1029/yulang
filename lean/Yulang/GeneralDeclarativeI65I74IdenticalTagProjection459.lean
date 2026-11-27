import Yulang.GeneralDeclarativeI65I74RoutedInlineStructuralEntry458

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.IdenticalTagProjection459
open GeneralDeclarationPatterns
open GeneralDeclarations (Declaration Clause)

def isRepeatedTag (first last : Pattern) : Bool :=
  match first with
  | .variant _ _ => decide (first = last)
  | _ => false

theorem only_identically_written_tag459 {a b : Pattern} (h : isRepeatedTag a b = true) :
    ∃ key child, a = .variant key child ∧ b = .variant key child := by
  cases a <;> simp [isRepeatedTag] at h
  rename_i tag child
  exact ⟨tag,child,rfl,h.symm⟩

mutual
  def pruneRepeatedTags : Pattern → Pattern
    | .var n => .var n
    | .app k args => .app k (pruneRepeatedTagsArgs args)
    | .record k p tail => .record k (pruneRepeatedTags p) (pruneRepeatedTags tail)
    | .variant t child => .variant t (pruneRepeatedTags child)
    | .join a b =>
      if isRepeatedTag a b then pruneRepeatedTags a
      else .join (pruneRepeatedTags a) (pruneRepeatedTags b)
  def pruneRepeatedTagsArgs : List Pattern → List Pattern
    | [] => []
    | t :: ts => pruneRepeatedTags t :: pruneRepeatedTagsArgs ts
end

mutual
  theorem same_normalization_under_every_capture459 :
      ∀ (p : Pattern) (capture : Nat → Pattern),
        normalize ((pruneRepeatedTags p).subst capture) = normalize (p.subst capture)
    | .var _, _ => rfl
    | .app _ ps, c => by
      simp [pruneRepeatedTags,Pattern.subst,normalize,same_args_normalization_under_every_capture459 ps c]
    | .record _ f t, c => by
      simp [pruneRepeatedTags,Pattern.subst,normalize,same_normalization_under_every_capture459 f c,
        same_normalization_under_every_capture459 t c]
    | .variant _ t, c => by
      simp [pruneRepeatedTags,Pattern.subst,normalize,same_normalization_under_every_capture459 t c]
    | .join a b, c => by
      by_cases isDup : isRepeatedTag a b = true
      · obtain ⟨tag,term,first,last⟩ := only_identically_written_tag459 isDup
        have together := first.trans last.symm
        clear first last
        subst b
        simp [pruneRepeatedTags,isDup,Pattern.subst,normalize,merge,same_normalization_under_every_capture459 a c]
      · simp [pruneRepeatedTags,isDup,
          Pattern.subst,normalize,same_normalization_under_every_capture459 a c,
          same_normalization_under_every_capture459 b c]
  theorem same_args_normalization_under_every_capture459 :
      ∀ (ps : List Pattern) (capture : Nat → Pattern),
        normalizeArgs (substArgs capture (pruneRepeatedTagsArgs ps)) = normalizeArgs (substArgs capture ps)
    | [], _ => rfl
    | p::ps,c => by
      simp [pruneRepeatedTagsArgs,substArgs,normalizeArgs,same_normalization_under_every_capture459 p c,
        same_args_normalization_under_every_capture459 ps c]
end

theorem prune_keeps_every_captured_count459 (ps : List Pattern) (cap : Nat → Pattern) :
    counted (substArgs cap (pruneRepeatedTagsArgs ps)) = counted (substArgs cap ps) := by
  unfold counted
  rw [same_args_normalization_under_every_capture459]

theorem different_tag_duplicates_are_not_erased459 (k l : Nat) (a b : Pattern) (different : k ≠ l) :
    pruneRepeatedTags (.join (.variant k a) (.variant l b)) =
      .join (pruneRepeatedTags (.variant k a)) (pruneRepeatedTags (.variant l b)) := by
  have nope : isRepeatedTag (.variant k a) (.variant l b) = false := by
    simp [isRepeatedTag,different]
  simp [pruneRepeatedTags,nope]

theorem projection_keeps_captured_original_smaller459
    (d : Declaration) (whereClause : Clause) (capture : Nat → Pattern) :
    Smaller (substArgs capture (pruneRepeatedTagsArgs d.head)) (substArgs capture whereClause.arguments) ↔
      Smaller (substArgs capture d.head) (substArgs capture whereClause.arguments) := by
  unfold Smaller
  rw [prune_keeps_every_captured_count459]


mutual
  theorem identity_capture_spells_original459 : ∀ p : Pattern, p.subst Pattern.var = p
    | .var _ => rfl
    | .app _ args => by simp [Pattern.subst,identity_args_capture_spells_original459 args]
    | .record _ f t => by simp [Pattern.subst,identity_capture_spells_original459 f,identity_capture_spells_original459 t]
    | .variant _ p => by simp [Pattern.subst,identity_capture_spells_original459 p]
    | .join p q => by simp [Pattern.subst,identity_capture_spells_original459 p,identity_capture_spells_original459 q]
  theorem identity_args_capture_spells_original459 : ∀ args : List Pattern, substArgs Pattern.var args = args
    | [] => rfl
    | p::ps => by simp [substArgs,identity_capture_spells_original459 p,identity_args_capture_spells_original459 ps]
end

theorem exact_original_query_is_unchanged_by_prune459 (p : Pattern) :
    normalize (pruneRepeatedTags p) = normalize p := by
  simpa only [identity_capture_spells_original459] using same_normalization_under_every_capture459 p Pattern.var

theorem exact_original_counts_are_unchanged_by_prune459 (ps : List Pattern) :
    counted (pruneRepeatedTagsArgs ps) = counted ps := by
  simpa only [identity_args_capture_spells_original459] using prune_keeps_every_captured_count459 ps Pattern.var

open GeneralDeclarativeWitnessDeclaredState357 (Current authoredRegistry)
open GeneralDeclarativeWitnessClassifyVariance357 (DeclarationReady)
open GeneralDeclarativeWitnessModeCoverage357 (DeclarationCovered)
open RecordTrail455 (localAuthorBits local_author_bits_exact455)
open RecordTree455

/-- Scope, evidence and DeclarationReady talk about the real unchanged
declaration. Projected spelling is a stable auxiliary witness only. -/
structure ExactProjectedHeader (cur : Current) (d : Declaration) (c : Clause) (empty : Nat) : Prop where
  original : d.requirements = [c]
  cover : DeclarationCovered cur.environment d
  sig : d.Signature (authoredRegistry cur).roles
  identified : d.Identified
  produced : d.Produced
  outputs : d.OutputOnly
  scope : d.Scoped
  head : WrittenArgs empty (pruneRepeatedTagsArgs d.head)
  body : WrittenArgs empty c.arguments
  small : Smaller d.head c.arguments

def checkProjectedHeader (cur : Current) (d : Declaration) (c : Clause) (key : Nat) : Bool :=
  localAuthorBits cur.environment d && checkTrees key (pruneRepeatedTagsArgs d.head) &&
    checkTrees key c.arguments && checkSmaller d.head c.arguments

theorem projected_header_is_finite_exact459 {cur d c empty} (same : d.requirements = [c]) :
    checkProjectedHeader cur d c empty = true ↔ ExactProjectedHeader cur d c empty := by
  constructor
  · intro ok
    simp only [checkProjectedHeader,Bool.and_eq_true] at ok
    obtain ⟨⟨⟨source,head⟩,body⟩,small⟩ := ok
    obtain ⟨covered,sig,id,prod,only,scope⟩ := (local_author_bits_exact455 ..).mp source
    exact ⟨same,covered,sig,id,prod,only,scope,(checkTrees_exact ..).mp head,
      (checkTrees_exact ..).mp body,(checkSmaller_exact ..).mp small⟩
  · intro found
    simp only [checkProjectedHeader,Bool.and_eq_true]
    exact ⟨⟨⟨(local_author_bits_exact455 ..).mpr ⟨found.cover,found.sig,found.identified,found.produced,found.outputs,found.scope⟩,
      (checkTrees_exact ..).mpr found.head⟩,(checkTrees_exact ..).mpr found.body⟩,(checkSmaller_exact ..).mpr found.small⟩

theorem projected_header_proves_actual_original_ready459 {cur d c empty}
    (found : ExactProjectedHeader cur d c empty) :
    DeclarationReady (authoredRegistry cur) d := by
  refine ⟨found.sig,found.identified,found.produced,found.outputs,found.scope,
    GeneralDeclarativeWitnessModeDeclaration357.scoped_decl found.cover,?_⟩
  intro k chosen
  rw [found.original] at chosen
  cases List.mem_singleton.mp chosen
  refine ⟨found.small,?_⟩
  have smaller : Smaller (pruneRepeatedTagsArgs d.head) c.arguments := by
    unfold Smaller
    rw [exact_original_counts_are_unchanged_by_prune459 d.head]
    exact found.small
  have stable := written_tree_paterson_stable_under_all_captures455 found.head found.body smaller
  intro capture
  exact (projection_keeps_captured_original_smaller459 d c capture).mp (stable capture)



end Yulang.GeneralDeclarativeI65.I72.IdenticalTagProjection459
