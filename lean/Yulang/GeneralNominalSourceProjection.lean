import Yulang.GeneralNominalRecordInversion

/-! Actual canonical record and variant projections yield closed source
Patterns with strictly smaller checker mass. Source constructor keys survive. -/
namespace Yulang.GeneralNominalSourceProjection
open GeneralNominalRecursiveInspection GeneralNominalOriginTerms GeneralNominalFiniteMeaning
open GeneralNominalReadbackFunctionality GeneralNominalGroundAccessibility
open GeneralNominalClosedPatternNormal GeneralNominalClosedPatternMass
open GeneralNominalSourcePatternParts GeneralNominalRecordInversion
open GeneralDeclarationPatterns
open GeneralNominalPatersonLineage (mass)

private theorem member_sum (numbers : List Nat) (member : value ∈ numbers) : value ≤ numbers.sum := by
  induction numbers with
  | nil => cases member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with rfl | member
    · simp only [List.sum_cons]; omega
    · have bound := ih member
      simp only [List.sum_cons]; omega

theorem child_weight (test : Test) (children : Fin (arity test) → Expr Nat)
    (index : Fin (arity test)) : weight (children index) < weight (.node test children) := by
  have bound := member_sum (List.ofFn fun position => weight (children position)) (List.mem_ofFn.mpr ⟨index,rfl⟩)
  cases test with
  | scalar base => exact Fin.elim0 index
  | nominal name count =>
    simp only [weight,GeneralNominalCompoundReadback.quote,queryMass,List.map_ofFn,Function.comp_def] at *
    omega
  | structural shape =>
    cases shape <;>
      simp only [weight,GeneralNominalCompoundReadback.quote,queryMass,List.map_ofFn,Function.comp_def] at * <;> omega

theorem followed_weight (path : Follows root term endpoint part) : weight part ≤ weight term := by
  induction path with
  | root => exact Nat.le_refl _
  | child test children index prior ih => exact Nat.le_trans (Nat.le_of_lt (child_weight test children index)) ih

variable {model : GeneralNominalCommonBridge.Assignment}

theorem followed_pattern (path : Follows root term endpoint part)
    (closed : ClosedTerm context pattern term)
    (meaning : At model .actual root (denote (fun _ => .bottom) term)) :
    ∃ source, Part (normalize pattern) source ∧ ClosedTerm context source part ∧
      At model .actual endpoint (denote (fun _ => .bottom) part) ∧ mass [source] ≤ mass [pattern] := by
  obtain ⟨source,member,_,reified⟩ := closed_reification path closed
  have projected := followed_readback path closed.2.2 (fun _ => .bottom) meaning
  exact ⟨source,member,reified,projected.2,by rw [closed_mass reified,closed_mass closed]; exact followed_weight path⟩

theorem actual_record_pattern (labels readLabels : List Nat)
    (children : Fin labels.length → Expr Nat)
    (closed : ClosedTerm context pattern (.node (.structural (.record labels)) children))
    (meaning : At model .actual root (denote (fun _ => .bottom) (.node (.structural (.record labels)) children)))
    (readCanonical : readLabels.Pairwise (· < ·))
    (observed : Observes model (.structural root (.record readLabels) index) actual) :
    ∃ source part, Part (normalize pattern) source ∧ ClosedTerm context source part ∧
      At model .actual (.structural root (.record readLabels) index) (denote (fun _ => .bottom) part) ∧
      mass [source] < mass [pattern] := by
  obtain ⟨position,sameIndex,sameLabels,_⟩ := record_projection labels readLabels
    (fun index => denote (fun _ => .bottom) (children index)) closed.2.2.1 readCanonical meaning observed
  subst readLabels
  have path : Follows root (.node (.structural (.record labels)) children)
      (.structural root (.record labels) position.val) (children position) := .child (.structural (.record labels)) children position .root
  obtain ⟨source,member,reified,readback,_⟩ := followed_pattern path closed meaning
  refine ⟨source,children position,member,reified,?_,?_⟩
  · simpa only [sameIndex] using readback
  · rw [closed_mass reified,closed_mass closed]
    exact child_weight (.structural (.record labels)) children position

theorem actual_variant_pattern (tag readTag : Nat) (children : Fin 1 → Expr Nat)
    (closed : ClosedTerm context pattern (.node (.structural (.variant tag)) children))
    (meaning : At model .actual root (denote (fun _ => .bottom) (.node (.structural (.variant tag)) children)))
    (observed : Observes model (.structural root (.variant readTag) index) actual) :
    ∃ source part, Part (normalize pattern) source ∧ ClosedTerm context source part ∧
      At model .actual (.structural root (.variant readTag) index) (denote (fun _ => .bottom) part) ∧
      mass [source] < mass [pattern] := by
  have rootMeaning : At model .actual root
      (CommonNominalFullCarrier.variant tag (denote (fun _ => .bottom) (children 0))) := by
    simpa [denote,build,shapeValue,GeneralNormalizedObservation.Shape.term,
      Core.PresenceGeneration.TyTerm.eval,CommonNominalFullCarrier.model,arity,GeneralNormalizedObservation.Shape.arity] using meaning
  obtain ⟨sameTag,sameIndex,_⟩ := variant_projection tag readTag _ rootMeaning observed
  subst readTag
  subst index
  have path : Follows root (.node (.structural (.variant tag)) children)
      (.structural root (.variant tag) 0) (children 0) := .child (.structural (.variant tag)) children (0 : Fin 1) .root
  obtain ⟨source,member,reified,readback,_⟩ := followed_pattern path closed meaning
  refine ⟨source,children 0,member,reified,readback,?_⟩
  rw [closed_mass reified,closed_mass closed]
  exact child_weight (.structural (.variant tag)) children (0 : Fin 1)

end Yulang.GeneralNominalSourceProjection
