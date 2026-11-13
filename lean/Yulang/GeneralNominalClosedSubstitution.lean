import Yulang.GeneralNominalCanonicalTemplates

/-! Simultaneous finite capture values survive supported template filling.
The final normalization is justified from its closed canonical query. -/
namespace Yulang.GeneralNominalClosedSubstitution
open GeneralDeclarationPatterns GeneralNominalInspection GeneralNominalHeadMatchMass
open GeneralNominalTemplateSubstitution GeneralPatternNormalForm
open GeneralNominalOriginTerms GeneralNominalCompoundReadback GeneralNominalReadbackFunctionality
open GeneralNominalClosedPatternNormal GeneralNominalGroundAccessibility

mutual
  theorem translated_covered (pattern : Pattern)
      (known : ClosedQuery (translate constructors interpretation pattern)) : covered pattern = true := by
    cases pattern with
    | var => rfl
    | join => simp only [translate,ClosedQuery] at known
    | variant tag payload =>
      simp only [translate,ClosedQuery] at known
      have child := known.2.2 _ (List.mem_singleton_self _)
      split at child
      · simp only [ClosedQuery] at child
      · exact translated_covered payload child
    | app key arguments =>
      rw [translate.eq_def] at known
      dsimp only at known
      split at known
      · rfl
      · rfl
      · rfl
      · simp only [ClosedQuery] at known
        have first := translated_covered _ (known.2.2 _ (List.mem_cons_self ..))
        have last := translated_covered _ (known.2.2 _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
        simp only [covered,coveredArgs,first,last,Bool.and_self]
      · split at known
        · split at known
          · simp only [ClosedQuery] at known
            exact translated_args_covered _ (fun argument member =>
              known _ (List.mem_map.mpr ⟨⟨argument,member⟩,List.mem_attach ..,rfl⟩))
          · simp only [ClosedQuery] at known
        · simp only [ClosedQuery] at known
    | record label payload tail =>
      simp only [translate] at known
      split at known
      · rename_i labels children tailQuery
        have parts := sorted_fields label _ labels children (record_length tail tailQuery) known
        have one := translated_covered payload parts.1
        have rest := translated_covered tail (by rw [tailQuery]; exact parts.2.1)
        simp only [covered,one,rest,Bool.and_self]
      · simp only [ClosedQuery] at known
    termination_by sizeOf pattern
  theorem translated_args_covered (patterns : List Pattern)
      (known : ∀ pattern ∈ patterns, ClosedQuery (translate constructors interpretation pattern)) : coveredArgs patterns = true := by
    cases patterns with
    | nil => rfl
    | cons head tail =>
      simp only [coveredArgs,translated_covered head (known head (List.mem_cons_self ..)),
        translated_args_covered tail (fun pattern member => known pattern (List.mem_cons_of_mem _ member)),Bool.and_self]
    termination_by sizeOf patterns
end

theorem quote_bind (term : Expr Nat) (substitution : Nat → Expr Nat) :
    quote (term.bind substitution) = fill (fun name => quote (substitution name)) (quote term) := by
  induction term with
  | leaf name => simp only [Expr.bind,quote,fill]
  | node test children ih =>
    cases test <;> simp only [Expr.bind,quote,fill,List.map_ofFn,Function.comp_def,ih]

theorem canonical_bind (term : Expr Nat) (canonical : Canonical term) (substitution : Nat → Expr Nat)
    (images : ∀ name ∈ term.leaves, Canonical (substitution name)) : Canonical (term.bind substitution) := by
  induction term with
  | leaf name => exact images name (List.mem_singleton_self _)
  | node test children ih =>
    refine ⟨canonical.1,fun index => ih index (canonical.2 index) ?_⟩
    intro name member
    apply images name
    simp only [Expr.leaves,List.mem_flatten,List.mem_ofFn]
    exact ⟨_,⟨index,rfl⟩,member⟩

theorem closed_bind (term : Expr Nat) (substitution : Nat → Expr Nat)
    (images : ∀ name ∈ term.leaves, (substitution name).leaves = []) : (term.bind substitution).leaves = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro name member
  obtain ⟨binder,present,member⟩ := (leaves_bind term substitution name).mp member
  rw [images binder present] at member
  cases member

theorem filled_closed (pattern : Pattern) (covered : GeneralDeclarationPatterns.covered pattern = true)
    (complete : Complete (translate context.state.constructors context.interpretation pattern))
    (capture : Nat → Pattern) (replacement : Nat → Expr Nat) (term : Expr Nat)
    (translated : translate context.state.constructors context.interpretation pattern = quote term)
    (canonical : Canonical term)
    (imagesCovered : ∀ name, GeneralDeclarationPatterns.covered (capture name) = true)
    (imagesTranslated : ∀ name, translate context.state.constructors context.interpretation (capture name) = quote (replacement name))
    (imagesClosed : ∀ name ∈ term.leaves, (replacement name).leaves = [])
    (imagesCanonical : ∀ name ∈ term.leaves, Canonical (replacement name)) :
    ClosedTerm context (pattern.subst capture) (term.bind replacement) := by
  have filled := translate_substitution pattern covered complete capture imagesCovered
  rw [translated] at filled
  have aligned : (fun name => translate context.state.constructors context.interpretation (capture name)) =
      (fun name => quote (replacement name)) := funext imagesTranslated
  rw [aligned,← quote_bind] at filled
  have closed := closed_bind term replacement imagesClosed
  have canonical := canonical_bind term canonical replacement imagesCanonical
  have normal := translated_normal (pattern.subst capture) (by rw [filled]; exact quote_closed _ closed canonical)
  exact ⟨by rw [normal]; exact filled,closed,canonical⟩

end Yulang.GeneralNominalClosedSubstitution
