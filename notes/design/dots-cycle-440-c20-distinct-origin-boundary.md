# C440 — 実際に異なる二端点の比較と、現行の同一 binder 捕捉は別

**同じ外側の元 endpoint を読む scoped C20 は閉じた。別々の元 endpoint が重なる場合の一般入口は閉じていない。** この実例は unchecked を言語診断に昇格させない。仕様や定理を変更していない。

- 任意の State・捕捉関数・宣言 key・used unary mode・四 leaf slots に対し、`DeepRead ... true (.app key [.var binder])` で二つの inner interval を読むと、現在の固定ルールの反転により同じ `ValueBind` の capture が両方に必要。任意の同じ適合モデルで、**二つの実 lower 意味は同値、二つの実 upper 意味も同値** と従う。これは上下の比較交差条件が全て真という条件より強い。等価性はモデル内での型であり、名前の一致を要求しない。
- 原点 0 の `Outer(Inner(Int..Int|Bool))` と原点 5 の `Outer(Inner(Int|Bool..Int|Bool))` を一つの実 request の上下端（0,0,5）として持つ元の Problem/Profile を構成。原点の両方と raw nominal 行は実レコード、外側 invariant・内側 declared covariant、実際の適合モデルあり。既存の `ContextDerives` では交差を比較可能。それでも `Int|Bool ≤ Int` は偽なので、任意の capture と任意の Binding リストについて、この形の現行の単一 binder の `DeepRead` は存在しない。狭い入口がより広い選択／捕捉までカバーしない正確な理由であって、ユーザーのソースの不正を主張しない。
- X14 の literal Float frontier と X17 の関数 source simplifier も別（正本 `lean/SpecExamples.lean` L28–35）。次に一般化するときは、上記の現行の比較と捕捉を混同しない。今周は新しい証拠形式を入れていない。

## 独立検証の再現

公式 Lean 4.35.0 `--trust=0 -DwarningAsError=true`、元の production-only search path で exit 0。下の最初の import を immutable C440 [EndToEnd source](../../lean/Audit/Cycle440I74NestedInvariantEndToEnd.lean) の先頭に足し、残りを同じ一つの source の末尾へ連結（Audit 同士の import はしない）。既存 8 行に加えて下の四つの `#print axioms` は全て `propext, Classical.choice, Quot.sound`。追加 QA は公開 Lean コード・公開の 45 Audit 件には加えない。

```lean
import Yulang.GeneralDeclarativeI65I74NestedInvariantDepth440

set_option backward.isDefEq.respectTransparency false
namespace Yulang.C440DeepCaptureBoundaryQA
open GeneralDeclarativeI65
open GeneralDeclarativeI65.I72.NestedInvariant440
open GeneralDeclarativeWhere319 (Capture)
open CommonRecursiveNominalIntervals (Endpoint)
open CommonDeclaredNominalInspection (Parameter)
open CommonNominalFullCarrier (Equivalent)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_symm eqv_trans)

theorem same_fixed_deep_capture_realizes_both_endpoint_pairs440
    {s : State} {capture : Nat → Capture} {key binder a b c d : Nat}
    {p : Parameter} (metadata : s.modes[key]? = some [p]) (used : validInner p)
    {found} (read : DeepRead s capture true (.app key [.var binder])
      (nestedInner key a b) (nestedInner key c d) found) :
    ValueBind s (capture binder) (.var a) (.var b) ∧
    ValueBind s (capture binder) (.var c) (.var d) := by
  cases read with
  | nominal _ _ readAt body =>
    have params := Option.some.inj (readAt.symm.trans metadata)
    cases params
    cases body with
    | cons one _ =>
      have mode := inherited_value440 used
      rw [mode.1,mode.2] at one
      cases one with
      | invariantValue left right =>
        cases left with
        | bind left =>
          cases right with
          | bind right => exact ⟨left,right⟩

theorem same_fixed_deep_capture_forces_actual_endpoint_equivalence440
    {s : State} {capture : Nat → Capture} {key binder a b c d : Nat}
    {p : Parameter} (metadata : s.modes[key]? = some [p]) (used : validInner p)
    {found} (read : DeepRead s capture true (.app key [.var binder])
      (nestedInner key a b) (nestedInner key c d) found)
    (m : Model) (fit : Fits s m) :
    Equivalent (m.assignment a).1 (m.assignment c).1 ∧
    Equivalent (m.assignment b).1 (m.assignment d).1 := by
  have bound := same_fixed_deep_capture_realizes_both_endpoint_pairs440 metadata used read
  have one := value_binding_sound bound.1 m fit
  have two := value_binding_sound bound.2 m fit
  exact ⟨eqv_trans one.1 (eqv_symm two.1),eqv_trans one.2 (eqv_symm two.2)⟩

#print axioms same_fixed_deep_capture_realizes_both_endpoint_pairs440
#print axioms same_fixed_deep_capture_forces_actual_endpoint_equivalence440
end Yulang.C440DeepCaptureBoundaryQA

namespace Yulang.GeneralDeclarativeI65.I72.NestedInvariant440.SplitOriginalQA
open GeneralDeclarativeI65
open Yulang.GeneralDeclarativeI65.I72.NestedInvariant440.ScopedExample
open Yulang.C440DeepCaptureBoundaryQA
open CommonNominalFullCarrier (Equivalent nominal subtype_refl)
open GeneralDeclarativeWitnessFullIntervals357 (ContextDerives)
open CommonRecursiveNominalIntervals (ContextWellFormed)
open CommonDeclaredNominalInspection (Parameter)
open GeneralDeclarativeWitnessRecordWindowFixture358 (payload integer_to_payload strict_original_payload_bounds)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open GeneralDeclarativeWhere319 (Capture)
open Checker408 (Problem)

def splitOrdinary : GeneralDeclarativeHead320.State :=
  ⟨⟨atoms ++ [atomAt 0 5,atomAt 3 3],[]⟩,
    rawRows .listBox ++ [rawNominal 5 9 6,rawNominal 6 20 3]⟩

def splitOrigins : List Origin := endpoints .listBox ++
  [⟨5,[71],nestedEndpoint 9 20 3 4⟩,⟨6,[71],nestedInner 20 3 4⟩]

def twoOriginal : Option Problem := do
  let raw ← build .listBox splitOrdinary table splitOrigins
  let root : Request := ⟨[71],⟨7,[⟨0,0,5⟩],[]⟩⟩
  pure {raw with root}

def sameFit : I72.Model :=
  let one := model .listBox true
  ⟨(fun n => if n = 5 then one.assignment 0 else if n = 6 then one.assignment 1 else one.assignment n),
    one.authoredValues,
    fun n => if n = 5 then some (nestedEndpoint 9 20 3 4) else if n = 6 then some (nestedInner 20 3 4)
      else one.nativeSyntax n⟩

theorem genuine_distinct_origins_fit_same_model440 {p : Problem} (got : twoOriginal = some p) :
    I72.Fits p.state sameFit ∧ p.state.core.modes = table ∧
      p.root.demand.arguments = [⟨0,0,5⟩] ∧
      (⟨0,[71],nestedEndpoint 9 20 2 4⟩ : Origin) ∈ p.state.core.origins ∧
      (⟨5,[71],nestedEndpoint 9 20 3 4⟩ : Origin) ∈ p.state.core.origins := by
  unfold twoOriginal build at got
  cases graph : GeneralDeclarativeWitnessSparseVariance357.compile GeneralDeclarativeWitnessVarianceFixtures357.source with
  | none => simp [graph] at got
  | some sem =>
    cases source : GeneralSourceMetadataBareBundle291.compile (surface .listBox [actual .listBox]) with
    | none => simp [graph,source] at got
    | some s =>
      simp only [graph,source,Option.pure_def,bind,Option.bind] at got
      cases got
      refine ⟨?_,rfl,rfl,?_,?_⟩
      · refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
        · intro a used
          change a ∈ atoms ++ [atomAt 0 5,atomAt 3 3] at used
          simp only [atoms,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at used
          rcases used with rfl|rfl|rfl|rfl|rfl|rfl|rfl
          · exact subtype_refl _
          · exact subtype_refl _
          · exact integer_to_payload
          · exact integer_to_payload
          · exact subtype_refl _
          · exact subtype_refl _
          · exact subtype_refl _
        · intro _ h; cases h
        · intro e used
          change e ∈ rawRows .listBox ++ [rawNominal 5 9 6,rawNominal 6 20 3] at used
          simp only [rawRows,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at used
          rcases used with rfl|rfl|rfl|rfl|rfl|rfl <;> exact eqv_refl _
        · intro _ h; cases h
        · intro o used
          change o ∈ splitOrigins at used
          simp only [splitOrigins,endpoints,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at used
          rcases used with rfl|rfl|rfl|rfl <;> rfl
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

theorem two_fitting_windows_overlap_but_fixed_read_cannot_capture_them440 :
    ∃ p, twoOriginal = some p ∧ I72.Fits p.state sameFit ∧
      p.root.demand.arguments = [⟨0,0,5⟩] ∧
      (⟨0,[71],nestedEndpoint 9 20 2 4⟩ : Origin) ∈ p.state.core.origins ∧
      (⟨5,[71],nestedEndpoint 9 20 3 4⟩ : Origin) ∈ p.state.core.origins ∧
      ContextDerives p.state.core.modes sameFit.assignment false
        (nestedEndpoint 9 20 2 4) (nestedEndpoint 9 20 3 4) ∧
      (∀ (cap : Nat → Capture) found,
        DeepRead p.state.core cap true (.app 20 [.var 6])
          (nestedInner 20 2 4) (nestedInner 20 3 4) found → False) := by
  have has : twoOriginal.isSome = true := by decide +kernel
  cases got : twoOriginal with
  | none => simp [got] at has
  | some p =>
    obtain ⟨fit,metadata,atArg,originLo,originHi⟩ := genuine_distinct_origins_fit_same_model440 got
    let mode : Parameter := ⟨.value,.covariant⟩
    have used : validInner mode := .inr (.inl rfl)
    have outMode : p.state.core.modes[9]? = some [inv] := metadata.symm ▸ rfl
    have inMode : p.state.core.modes[20]? = some [mode] := metadata.symm ▸ rfl
    have empty : UnaryUsedModes p.state.core.modes [] := by intro _ h; cases h
    have comparison := (arbitrary_used_nominal_prefix_semantic_four_crossings440
      empty outMode inMode used 2 4 3 4 sameFit.assignment).mpr
      ⟨integer_to_payload,integer_to_payload,subtype_refl _,subtype_refl _⟩
    refine ⟨p,rfl,fit,atArg,originLo,originHi,comparison.2.2,?_⟩
    intro _ _ read
    have equal := same_fixed_deep_capture_forces_actual_endpoint_equivalence440 inMode used read sameFit fit
    exact strict_original_payload_bounds equal.1.2

#print axioms genuine_distinct_origins_fit_same_model440
#print axioms two_fitting_windows_overlap_but_fixed_read_cannot_capture_them440
end Yulang.GeneralDeclarativeI65.I72.NestedInvariant440.SplitOriginalQA
```
