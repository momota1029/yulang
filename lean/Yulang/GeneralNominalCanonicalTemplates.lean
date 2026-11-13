import Yulang.GeneralPatternVariableProvenance
import Yulang.GeneralNominalRequestCompleteness

/-! Complete normalized templates quote finite canonical trees, retaining
source variable identities and record field order. -/
set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralNominalCanonicalTemplates
open GeneralDeclarationPatterns GeneralNominalInspection GeneralNominalHeadMatchMass
open GeneralNominalTemplateSubstitution GeneralPatternNormalForm
open GeneralNominalOriginTerms GeneralNominalCompoundReadback GeneralNominalReadbackFunctionality

def Good (allowed : Nat → Prop) : Query → Prop
  | .variables [name] => allowed name
  | .variables _ | .deferred _ => False
  | .scalar _ => True
  | .node shape children => shape.Canonical ∧ children.length = shape.arity ∧ ∀ child ∈ children, Good allowed child
  | .nominal _ children => ∀ child ∈ children, Good allowed child

mutual
  theorem quoted (query : Query) (good : Good allowed query) :
      ∃ term : Expr Nat, quote term = query ∧ Canonical term ∧ ∀ name ∈ term.leaves, allowed name := by
    cases query with
    | variables names =>
      cases names with
      | nil => simp only [Good] at good
      | cons name rest =>
        cases rest with
        | nil => exact ⟨.leaf name,rfl,trivial,by intro x member; cases List.mem_singleton.mp member; exact (show allowed name from by simpa only [Good] using good)⟩
        | cons => simp only [Good] at good
    | deferred => simp only [Good] at good
    | scalar base =>
      exact ⟨.node (.scalar base) Fin.elim0,rfl,⟨trivial,fun index => Fin.elim0 index⟩,by
        intro name member; simp [Expr.leaves,arity] at member⟩
    | node shape children =>
      simp only [Good] at good
      obtain ⟨terms,translated,canonical,allowedTerms⟩ := quoted_list children good.2.2
      have length : terms.length = shape.arity := by rw [← List.length_map (f := quote),translated,good.2.1]
      let args : Fin shape.arity → Expr Nat := fun i => terms[i.val]'(by rw [length]; exact i.isLt)
      refine ⟨.node (.structural shape) args,?_,⟨good.1,?_⟩,?_⟩
      · simp only [quote]
        congr 1
        have same : List.ofFn args = terms := List.ext_get (by simp [args,length]) (by intro i a b; simp [args])
        simpa only [arity,List.map_ofFn,Function.comp_def] using (congrArg (List.map quote) same).trans translated
      · intro i; exact canonical _ (List.getElem_mem ..)
      · intro name member
        obtain ⟨leaves,present,contained⟩ := List.mem_flatten.mp member
        obtain ⟨i,rfl⟩ := List.mem_ofFn.mp present
        exact allowedTerms _ (List.getElem_mem ..) name contained
    | nominal name children =>
      simp only [Good] at good
      obtain ⟨terms,translated,canonical,allowedTerms⟩ := quoted_list children good
      let args : Fin terms.length → Expr Nat := fun i => terms[i]
      refine ⟨.node (.nominal name terms.length) args,?_,⟨trivial,?_⟩,?_⟩
      · simp only [quote]
        congr 1
        have same : List.ofFn args = terms := List.ext_get (by simp [args]) (by intro i a b; simp [args])
        simpa only [arity,List.map_ofFn,Function.comp_def] using (congrArg (List.map quote) same).trans translated
      · intro i; exact canonical _ (List.getElem_mem ..)
      · intro binder member
        obtain ⟨leaves,present,contained⟩ := List.mem_flatten.mp member
        obtain ⟨i,rfl⟩ := List.mem_ofFn.mp present
        exact allowedTerms _ (List.getElem_mem ..) binder contained
    termination_by sizeOf query
  theorem quoted_list (queries : List Query) (good : ∀ query ∈ queries, Good allowed query) :
      ∃ terms : List (Expr Nat), terms.map quote = queries ∧
        (∀ term ∈ terms, Canonical term) ∧ ∀ term ∈ terms, ∀ name ∈ term.leaves, allowed name := by
    cases queries with
    | nil => exact ⟨[],rfl,by simp,by simp⟩
    | cons head tail =>
      obtain ⟨first,translated,canonical,variables⟩ := quoted head (good head (List.mem_cons_self ..))
      obtain ⟨rest,translations,canonicals,vars⟩ := quoted_list tail (fun q member => good q (List.mem_cons_of_mem _ member))
      refine ⟨first :: rest,by simp [translated,translations],?_,?_⟩
      · intro term member; rcases List.mem_cons.mp member with rfl | member
        · exact canonical
        · exact canonicals term member
      · intro term member; rcases List.mem_cons.mp member with rfl | member
        · exact variables
        · exact vars term member
    termination_by sizeOf queries
end

theorem record_fields (pattern : Pattern)
    (translated : translate constructors interpretation pattern = .node (.record labels) children) :
    labels.Perm (fields pattern) := by
  cases pattern with
  | var | join | variant => simp only [translate] at translated; cases translated
  | app key arguments =>
    rw [translate.eq_def] at translated
    dsimp only at translated
    split at translated
    · cases translated
    · cases translated; exact List.Perm.refl []
    · cases translated
    · cases translated
    · split at translated
      · split at translated <;> cases translated
      · cases translated
  | record label payload tail =>
    simp only [translate] at translated
    split at translated
    · rename_i names queries found
      cases translated
      have length := GeneralNominalClosedPatternNormal.record_length tail found
      have perm := (List.mergeSort_perm ((label,translate constructors interpretation payload) :: names.zip queries)
        (fun a b => a.1 ≤ b.1)).map Prod.fst
      simp only [List.map_cons,List.map_fst_zip (Nat.le_of_eq length.symm)] at perm
      exact perm.trans (List.Perm.cons label (record_fields tail found))
    · cases translated

theorem sorted_good (label : Nat) (payload : Query) (labels : List Nat) (children : List Query)
    (one : Good allowed payload) (rest : Good allowed (.node (.record labels) children))
    (unique : (label :: labels).Nodup) :
    Good allowed (.node (.record
      ((((label,payload) :: labels.zip children).mergeSort (fun a b => a.1 ≤ b.1)).map Prod.fst))
      ((((label,payload) :: labels.zip children).mergeSort (fun a b => a.1 ≤ b.1)).map Prod.snd)) := by
  simp only [Good] at rest ⊢
  refine ⟨?_,by simp [GeneralNormalizedObservation.Shape.arity],?_⟩
  · have perm := (List.mergeSort_perm ((label,payload) :: labels.zip children) (fun a b => a.1 ≤ b.1)).map Prod.fst
    have length : children.length = labels.length := rest.2.1
    simp only [List.map_cons,List.map_fst_zip (Nat.le_of_eq length.symm)] at perm
    have distinct := perm.nodup_iff.mpr unique
    have sorted := List.pairwise_mergeSort (le := fun a b : Nat × Query => a.1 ≤ b.1)
      (fun a b c ab bc => by simp only [decide_eq_true_eq] at *; exact Nat.le_trans ab bc)
      (fun a b => by simp only [Bool.or_eq_true,decide_eq_true_eq]; exact Nat.le_total _ _) ((label,payload) :: labels.zip children)
    have ordered : (((label,payload) :: labels.zip children).mergeSort (fun a b => a.1 ≤ b.1)).map Prod.fst |>.Pairwise (· ≤ ·) := by
      rw [List.pairwise_map]
      exact sorted.imp (fun h => of_decide_eq_true h)
    exact (ordered.and distinct).imp (fun h => Nat.lt_of_le_of_ne h.1 h.2)
  · intro child member
    obtain ⟨field,sortedMember,equal⟩ := List.mem_map.mp member
    rw [← equal]
    rcases List.mem_cons.mp (List.mem_mergeSort.mp sortedMember) with same | member
    · exact same ▸ one
    · exact rest.2.2 field.2 (List.of_mem_zip member).2

mutual
  theorem translated_good (pattern : Pattern) (normal : Normal pattern)
      (complete : Complete (translate constructors interpretation pattern))
      (variables : GeneralPatternVariableProvenance.Uses allowed pattern) :
      Good allowed (translate constructors interpretation pattern) := by
    cases pattern with
    | var name => simpa only [translate,Good] using variables name (List.mem_singleton_self _)
    | join => simp only [Normal] at normal
    | variant tag payload =>
      simp only [Normal] at normal
      rw [variant_query payload (covered_normal payload normal)] at complete ⊢
      simp only [Complete] at complete
      simp only [Good]
      refine ⟨trivial,rfl,?_⟩
      intro q member
      cases List.mem_singleton.mp member
      exact translated_good payload normal (complete _ (List.mem_singleton_self _)) variables
    | app key arguments =>
      rw [translate.eq_def] at complete ⊢
      dsimp only at complete ⊢
      split at complete
      · simp_all only [Good]
      · simp only [Good]; exact ⟨List.Pairwise.nil,rfl,by simp⟩
      · simp_all only [Good,GeneralNormalizedObservation.Shape.Canonical,List.length_nil,GeneralNormalizedObservation.Shape.arity,List.not_mem_nil,false_implies,implies_true,and_self]
      · rename_i first last primitive
        simp only [Complete] at complete
        simp only [Normal] at normal
        simp only [Good]
        refine ⟨trivial,rfl,?_⟩
        intro q member
        rcases List.mem_cons.mp member with same | member
        · exact same ▸ translated_good first (normal _ (List.mem_cons_self ..))
            (complete _ (List.mem_cons_self ..)) (fun n mem => variables n (List.mem_append_left _ mem))
        · cases List.mem_singleton.mp member
          exact translated_good last (normal _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
            (complete _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
            (fun n mem => variables n (List.mem_append_right _ (List.mem_append_left _ mem)))
      · split at complete
        · split at complete
          · rename_i accepted
            simp only [accepted,ite_true,Good]
            simp only [Complete] at complete
            simp only [Normal] at normal
            intro q member
            obtain ⟨⟨p,present⟩,_,rfl⟩ := List.mem_map.mp member
            apply translated_good p (normal p present) (complete _ (List.mem_map.mpr ⟨⟨p,present⟩,List.mem_attach ..,rfl⟩))
            exact fun n mem => variables n (argument_variables _ p present mem)
          · simp only [Complete] at complete
        · simp only [Complete] at complete
    | record label payload tail =>
      simp only [Normal] at normal
      rw [translate.eq_def] at complete ⊢
      dsimp only at complete ⊢
      split at complete
      · rename_i labels children tailQuery
        have length := GeneralNominalClosedPatternNormal.record_length tail tailQuery
        have supported := record_complete label _ labels children length complete
        have one := translated_good payload normal.1 supported.1 (fun n mem => variables n (List.mem_append_left _ mem))
        have rest := translated_good tail normal.2.1 (by rw [tailQuery]; exact supported.2)
          (fun n mem => variables n (List.mem_append_right _ mem))
        rw [tailQuery] at rest
        apply sorted_good label _ labels children one rest
        exact (List.Perm.cons label (record_fields tail tailQuery)).nodup_iff.mpr
          (List.nodup_cons.mpr ⟨normal.2.2,fields_unique tail normal.2.1⟩)
      · simp only [Complete] at complete
    termination_by sizeOf pattern
  theorem argument_variables (patterns : List Pattern) (pattern : Pattern) (member : pattern ∈ patterns)
      (variableMember : name ∈ pattern.variables) : name ∈ variablesArgs patterns := by
    cases patterns with
    | nil => cases member
    | cons head tail =>
      rcases List.mem_cons.mp member with same | member
      · exact List.mem_append_left _ (same ▸ variableMember)
      · exact List.mem_append_right _ (argument_variables tail pattern member variableMember)
    termination_by sizeOf patterns
end

end Yulang.GeneralNominalCanonicalTemplates
