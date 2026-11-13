import Yulang.GeneralNominalCanonicalPacketTransport

/-! A reversible source-syntax codec for the elimination inventory. These
codes are bookkeeping trees, not semantic type readbacks. Record markers
retain the source key and both children, including the tail. -/
set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralNominalPatternInventory
open GeneralDeclarationPatterns GeneralNominalOriginTerms GeneralNominalRecursiveInspection
open GeneralNominalOpenPatternLabels GeneralNominalHoleElimination

private def two (first last : α) (index : Fin 2) : α := if index.val = 0 then first else last

mutual
  def encode : Pattern → Expr Nat
    | .var name => .leaf name
    | .app key arguments => .node (.nominal key 1) (fun _ => encodeList arguments)
    | .record label payload tail => .node (.structural (.record [label,label])) (two (encode payload) (encode tail))
    | .variant tag payload => .node (.structural (.variant tag)) (fun _ => encode payload)
    | .join first last => .node (.structural .pair) (two (encode first) (encode last))
  def encodeList : List Pattern → Expr Nat
    | [] => .node (.scalar .int) Fin.elim0
    | head :: tail => .node (.structural .pair) (two (encode head) (encodeList tail))
end

mutual
  def decode : Expr Nat → Pattern
    | .leaf name => .var name
    | .node test children => match test with
      | .nominal name 1 => .app name (decodeList (children ⟨0,by simp [arity]⟩))
      | .structural (.record [label,_]) => .record label (decode (children ⟨0,by simp [arity,GeneralNormalizedObservation.Shape.arity]⟩)) (decode (children ⟨1,by simp [arity,GeneralNormalizedObservation.Shape.arity]⟩))
      | .structural (.variant tag) => .variant tag (decode (children ⟨0,by simp [arity,GeneralNormalizedObservation.Shape.arity]⟩))
      | .structural .pair => .join (decode (children ⟨0,by simp [arity,GeneralNormalizedObservation.Shape.arity]⟩)) (decode (children ⟨1,by simp [arity,GeneralNormalizedObservation.Shape.arity]⟩))
      | _ => .var 0
  def decodeList : Expr Nat → List Pattern
    | .leaf _ => []
    | .node test children => match test with
      | .structural .pair => decode (children ⟨0,by simp [arity,GeneralNormalizedObservation.Shape.arity]⟩) :: decodeList (children ⟨1,by simp [arity,GeneralNormalizedObservation.Shape.arity]⟩)
      | _ => []
end

mutual
  theorem decode_encode (pattern : Pattern) : decode (encode pattern) = pattern := by
    cases pattern with
    | var => rfl
    | app key arguments => simp only [encode,decode,decode_encode_list arguments]
    | record label payload tail =>
      simp only [encode,decode,two,ite_true,Nat.one_ne_zero,ite_false,
        decode_encode payload,decode_encode tail]
    | variant tag payload => simp only [encode,decode,decode_encode payload]
    | join first last =>
      simp only [encode,decode,two,ite_true,Nat.one_ne_zero,ite_false,
        decode_encode first,decode_encode last]
  theorem decode_encode_list (patterns : List Pattern) : decodeList (encodeList patterns) = patterns := by
    cases patterns with
    | nil => rfl
    | cons head tail =>
      simp only [encodeList,decodeList,two,ite_true,Nat.one_ne_zero,ite_false,
        decode_encode head,decode_encode_list tail]
end

mutual
  theorem encode_subst (pattern : Pattern) (substitution : Nat → Pattern) :
      encode (pattern.subst substitution) = (encode pattern).bind (fun name => encode (substitution name)) := by
    cases pattern with
    | var => rfl
    | app key arguments => simp only [Pattern.subst,encode,Expr.bind,encode_list_subst arguments substitution]
    | record label payload tail =>
      simp only [Pattern.subst,encode,Expr.bind]
      congr 1
      funext i
      simp only [two]
      split <;> simp only [encode_subst payload substitution,encode_subst tail substitution]
    | variant tag payload => simp only [Pattern.subst,encode,Expr.bind,encode_subst payload substitution]
    | join first last =>
      simp only [Pattern.subst,encode,Expr.bind]
      congr 1
      funext i
      simp only [two]
      split <;> simp only [encode_subst first substitution,encode_subst last substitution]
  theorem encode_list_subst (patterns : List Pattern) (substitution : Nat → Pattern) :
      encodeList (substArgs substitution patterns) = (encodeList patterns).bind (fun name => encode (substitution name)) := by
    cases patterns with
    | nil =>
      simp only [substArgs,encodeList,Expr.bind]
      congr 1
      funext i
      exact Fin.elim0 i
    | cons head tail =>
      simp only [substArgs,encodeList,Expr.bind]
      congr 1
      funext i
      simp only [two]
      split <;> simp only [encode_subst head substitution,encode_list_subst tail substitution]
end

/-- Supported source labels have complete record tails, so substitution does
not expose a hidden source field on a tail spine. -/
theorem label_subst_normal (known : Label context pattern term)
    (substitution : Nat → Pattern) (replacement : Nat → Expr Nat)
    (images : ∀ name, Label context (substitution name) (replacement name)) :
    normalize (pattern.subst substitution) = pattern.subst substitution := by
  have translated := GeneralNominalTemplateSubstitution.translate_substitution pattern known.1
    (by rw [known.2.1]; exact quote_complete term) substitution (fun name => (images name).1)
  rw [known.2.1] at translated
  have aligned : (fun name => GeneralNominalInspection.translate context.state.constructors context.interpretation (substitution name)) =
      (fun name => GeneralNominalCompoundReadback.quote (replacement name)) := funext (fun name => (images name).2.1)
  rw [aligned,← GeneralNominalClosedSubstitution.quote_bind] at translated
  exact translated_normal _ (GeneralNominalTemplateSubstitution.subst_covered pattern known.1 substitution (fun name => (images name).1))
    (by
      rw [translated]
      exact quote_open _ (GeneralNominalClosedSubstitution.canonical_bind term known.2.2 replacement (fun name _ => (images name).2.2)))

theorem supported_list_normal (patterns : List Pattern)
    (known : ∀ pattern ∈ patterns, ∃ term, Label context pattern term)
    (substitution : Nat → Pattern) (replacement : Nat → Expr Nat)
    (images : ∀ name, Label context (substitution name) (replacement name)) :
    normalizeArgs (substArgs substitution patterns) = substArgs substitution patterns := by
  induction patterns with
  | nil => rfl
  | cons head tail ih =>
    obtain ⟨term,label⟩ := known head (List.mem_cons_self ..)
    simp only [substArgs,normalizeArgs,label_subst_normal label substitution replacement images,
      ih (fun pattern member => known pattern (List.mem_cons_of_mem _ member))]

theorem substituted_root_code (patterns : List Pattern)
    (known : ∀ pattern ∈ patterns, ∃ term, Label context pattern term)
    (substitution : Nat → Pattern) (replacement : Nat → Expr Nat)
    (images : ∀ name, Label context (substitution name) (replacement name)) :
    encodeList (normalizeArgs (substArgs substitution patterns)) =
      (encodeList patterns).bind (fun name => encode (substitution name)) := by
  rw [supported_list_normal patterns known substitution replacement images]
  exact encode_list_subst patterns substitution

end Yulang.GeneralNominalPatternInventory
