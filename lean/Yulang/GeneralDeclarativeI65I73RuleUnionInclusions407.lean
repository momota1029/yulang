import Yulang.GeneralDeclarativeI65I73RuleUnion407

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72
open GeneralDeclarativeI65
open GeneralDeclarationPatterns (Pattern)
open GeneralDeclarativeK2Graph321 (View)
open CommonRoleOutermostResolver (Dictionary Result Summarizes Tree)

/-- Embedding preserves requests, tree/event indices, dictionary
summaries, receipts and where order. Smaller exact output proofs do
not have to be re-found in the target rule family. -/
noncomputable def include_fixed_family_trace_R0 {R : SourcePrimitives}
    (family : FixedEvidenceFamily407 R) {s q t e} (trace : SourceTrace R s q t e) :
    SourceTrace R0 s q t e := by
  exact SourceTrace.rec (R := R) (s := s)
    (motive_1 := fun q t e _ => SourceTrace R0 s q t e)
    (motive_2 := fun qs ts _ => WhereForest R0 s qs ts)
    (motive_3 := fun needs _ => SupportForest R0 s needs)
    (fun cycle => .rootK2 cycle)
    (fun verdict safe localHyp _ lower => .other verdict safe ⟨R,family,localHyp⟩ lower)
    (fun event safe localHyp _ _ lower children => .selected event safe ⟨R,family,localHyp⟩ lower children)
    .nil
    (fun _ _ a b => .cons a b)
    .nil
    (fun _ done emit _ lower rest => .cons lower done emit rest)
    trace

theorem include_fixed_family_classifies_R0 {R : SourcePrimitives}
    (family : FixedEvidenceFamily407 R) {s q verdict} :
    Classifies R s q verdict → Classifies R0 s q verdict := by
  rintro ⟨t,e,⟨trace⟩,done⟩
  exact ⟨t,e,⟨include_fixed_family_trace_R0 family trace⟩,done⟩

def OriginalRuleAt407 {s q} (event : Event s q) : Prop :=
  (visible s.core q = [event.frame.decl] ∧
    ∀ d ∈ visible s.core q, ∀ p ∈ d.head, ∃ n, p = Pattern.var n ∧
      ∀ (v : View) (root site : Nat), ¬ GeneralDeclarativeInspect321.Visit v root (.variable n) site) ∨
  Nonempty (AuthoredNativeSelected405 event)

private theorem ordinary_shape407 {s : State} {q : Request}
    (whole : ∀ d ∈ visible s.core q, ∀ p ∈ d.head, ∃ n, p = Pattern.var n) :
    ∀ d ∈ visible s.core q, ∀ p ∈ d.head, ∃ n, p = Pattern.var n ∧
      ∀ (v : View) (root site : Nat), ¬ GeneralDeclarativeInspect321.Visit v root (.variable n) site := by
  intro d incl p present
  obtain ⟨n,literal⟩ := whole d incl p present
  exact ⟨n,literal,fun _ _ _ => GeneralDeclarativeInspect321.variable_has_no_visit⟩

private theorem repeated_shapes407 {s : State} {q : Request}
    (all : ∀ d ∈ visible s.core q, RepeatedRow403 q d) :
    ∀ d ∈ visible s.core q, ∀ p ∈ d.head, ∃ n, p = Pattern.var n := by
  intro d incl p present
  rw [(all d incl).literal] at present
  obtain ⟨n,_,rfl⟩ := List.mem_map.mp present
  exact ⟨n,rfl⟩

private theorem original_R0_rule_shape407 {R : SourcePrimitives}
    (family : FixedEvidenceFamily407 R) {s q} (event : Event s q) {needs}
    (proof : R.elected s q event needs) :
    OriginalRuleAt407 event := by
  have fromWhere : Nonempty (VariableWhereReadback403 event) → OriginalRuleAt407 event := by
    rintro ⟨one⟩
    exact .inl ⟨one.elected.sole,ordinary_shape407 (repeated_shapes407 one.elected.scope.allVisible)⟩
  have fromSupported : supportedVariableSource404.elected s q event needs → OriginalRuleAt407 event := by
    intro before
    rcases before with old|fresh
    · exact fromWhere old.2.1
    · obtain ⟨read⟩ := fresh.1
      exact .inl ⟨read.choice.sole,ordinary_shape407 (repeated_shapes407 read.choice.rowShape)⟩
  cases family with
  | variableOnly =>
    obtain ⟨read⟩ := proof.2.1
    refine .inl ⟨read.one,ordinary_shape407 ?_⟩
    intro d incl p pos
    let localRow := read.scope.allVisible d incl
    rw [localRow.literal] at pos
    obtain ⟨n,_,rfl⟩ := List.mem_map.mp pos
    exact ⟨n,rfl⟩
  | repeated =>
    obtain ⟨read⟩ := proof.2.1
    exact .inl ⟨read.elected.sole,ordinary_shape407 (repeated_shapes407 read.elected.scope.allVisible)⟩
  | whereTree | nativeK2 => exact fromWhere proof.2.1
  | supported | supportedK2 | supportedAmbiguity => exact fromSupported proof
  | authoredNative =>
    exact proof.elim fromSupported (fun native => .inr native.2.1)

theorem R0_selection_uses_independent_original_rule407 {s q}
    (event : Event s q) {needs} (localRule : R0.elected s q event needs) :
    OriginalRuleAt407 event := by
  obtain ⟨_,f,exact⟩ := localRule
  exact original_R0_rule_shape407 f event exact

theorem R0_raw_root_priority407 {s q} (raw : RootCycle s q) :
    Classifies R0 s q .rejected ∧ ∀ d, ¬ Classifies R0 s q (.selected d) :=
  ⟨root_k2_is_rejected_for_every_primitive_system raw,fun _ => root_k2_never_selects raw⟩

theorem R0_mixed_producer_retains_literal_original_output407 {s q t e d}
    (trace : SourceTrace R0 s q t (some e))
    (done : Summarizes t (.selected d)) (i : Fin q.demand.outputs.length) :
    ∃ _dependency : SupportForest R0 s [⟨q,d,i,(e.outputs i).receipt⟩],
      Nonempty (ExactOutputSupport R0 s ⟨q,d,i,(e.outputs i).receipt⟩) := by
  let dependency : SupportForest R0 s [⟨q,d,i,(e.outputs i).receipt⟩] := .cons trace done rfl .nil
  exact ⟨dependency,⟨dependency.atOriginal 0 rfl⟩⟩

end Yulang.GeneralDeclarativeI65.I72
