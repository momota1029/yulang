# C440 — 検証された immutable source、実入口と独立 Audit

## Source / scope audit

- 科学 pin: `edaebd19d22cd90ee6b7ae7cfce675ae4b2eb578`（Lean tree `5d57993d91ace99c523aaca4b6d8804d4b1498aa`）。正本の入力: `integration/m1-final@1d2084ac7278aa7b9eb29eea86caaf740a7bc567`（C439 exact 採用を確認）。古い `work/dots-main@c80ddd2768633850f783f8ab7fdd4120a27b1bf9` の Lean tree は `3fa551ff461d24ab106f9dca1f55cdefd742b49e`。
- 別の検証で、Git から再取得した今回の全 15 blob を `git hash-object --stdin` で再照合し、実ファイルによる別プロセスで再実行。既存の focused import closure は、使った 4,089 source 全ての provenance をその正本の Git bytes と照合し、同じ source の既存コンパイル結果を再利用。一部の旧比較 oracle だけの試験モジュール（この closure の数に不算入）は新しい入口の依存ではない。
- 既存 production 7,675 個、既存 standalone Audit 2,061 個は blob 不変、既存 Lean 直下他ファイルも同一。barrel の元の 375,527 bytes は保持、追加 7 imports だけ。`lean/Audit.lean` と `lean/README.md` は tree metadata の blob ID (`97dd1cfaded3e3abc3fd8caa98a64843d6f7a3d9`、`9fd6842bcc00c5bc5c00a196d9ccb328c6b0c94a`) のみ確認、本文未参照・未変更。
- Audit の import: `Yulang.*` 以外 0 件。全 8 本は各々別の clean directory / 本体の olean のみの search path / Audit olean なし。公式 Lean 4.35.0 (commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`) で 7 production を依存順に、8 Audit を個別に照合。全 exit 0、警告なし。全 45 declarations の公理は標準 `propext`、`Classical.choice`、`Quot.sound` の部分集合（1 件は公理なし）。

```sh
LEAN_PATH=<対象の production oleans> lean --trust=0 -DwarningAsError=true -o <対象 root>/<対応する Yulang module>.olean <production source>
# 各 Audit は 1 本だけの clean directory で; Audit olean は入れない
LEAN_PATH=<同じ production oleans> lean --trust=0 -DwarningAsError=true <standalone audit file>
```

全 `lake build`、全 `tools/verify-lean.sh` と Rust 実機はこの dot では走らせていない（監督役の全体検証と別）。

| immutable path | blob | Audit 宣言数 |
| --- | --- | ---: |
| `lean/Yulang/GeneralDeclarativeI65I74NestedInvariantSource440.lean` | `5c1455d90c018653f3af7867a69d90562c67b033` | — |
| `lean/Audit/Cycle440I74NestedInvariantSource.lean` | `13b894cd57af4a8736fd07b5825913b69f8e4a77` | 7 |
| `lean/Yulang/GeneralDeclarativeI65I74NestedInvariantRead440.lean` | `f40901aaef86c3da453b3b2b9fb56f81abbd198b` | — |
| `lean/Audit/Cycle440I74NestedInvariantRead.lean` | `f22b70311f62057b15d08f5c46c4111f9c1fec8a` | 3 |
| `lean/Yulang/GeneralDeclarativeI65I74NestedInvariantRule440.lean` | `6a7e0c1e9d6c515911ec8f234f765b62af5178a2` | — |
| `lean/Audit/Cycle440I74NestedInvariantRule.lean` | `bdfdf367b4172937518d5d83af7fd1dac28f6a27` | 6 |
| `lean/Yulang/GeneralDeclarativeI65I74NestedInvariantEntry440.lean` | `4fe402e2429331113a5dc83f73aaac53a82cc3fc` | — |
| `lean/Audit/Cycle440I74NestedInvariantEntry.lean` | `c61b9d645b7dcd40edbe5cb4f811326ba29810c0` | 7 |
| `lean/Audit/Cycle440I74NestedInvariantEndToEnd.lean` | `ac1c2b5ce72b0fbe455e42fd31bd36018c7fc072` | 8 |
| `lean/Yulang/GeneralDeclarativeI65I74NestedInvariantCrossings440.lean` | `32a9e4951c9424c206d0808555d4ebce9cd4d671` | — |
| `lean/Audit/Cycle440I74NestedInvariantCrossings.lean` | `fd291117a78b69392448b5b4589f9615611832ff` | 5 |
| `lean/Yulang/GeneralDeclarativeI65I74NestedInvariantCoherence440.lean` | `49f43799f832678bd1d5135623bdd84a8c3b4a56` | — |
| `lean/Audit/Cycle440I74NestedInvariantCoherence.lean` | `73e0040005d06bf40e3a6dd16a14fcf1060f2865` | 4 |
| `lean/Yulang/GeneralDeclarativeI65I74NestedInvariantDepth440.lean` | `1ad197e6bb5c240da6e5a1cf299bd50186c5aa99` | — |
| `lean/Audit/Cycle440I74NestedInvariantDepth.lean` | `afc229992dbe3174029993f9ee0af98b5534d045` | 5 |

## Actual `R20.check` 実行と対照

- 正例（実際の .listList / .listBox / .listArrow 宣言、二つの元の origin、元の raw 行、選択された辞書を検査） = `[true,true,true]`。上段で指定される同じ元の範囲に、実際に異なる値を中心とする二つの適合モデルがある。
- 順に、偽の mode table、明示 crossing atom を除く、issuer が違う、report が違う、raw 行が違う、実際に訪れる inner の raw cycle、新入口の raw root cycle、従来入口の raw root cycle、別の raw alias-class outer 読み、実際に見える二候補 = `[false,false,false,false,false,false,false,true,false,false]`。明示 crossing atom については、他の二つの上下界から推移的に成り立つ場合でも、この版の証明書 replayer はそこまで閉路探索をしない。その false を言語診断にしない。
- 個別 QA (下記): 同一元状態の二つの raw locator で capture の中心**名**は 3 と 5 だが、どちらも同じ辞書 report で受理され、その元状態の具体的な適合モデルがある。一般定理では同じ適合モデル内の中心値の同値のみ主張。別々の適合モデル間で中心値を固定しない。
- 個別 QA: 訪れる inner の raw cycle で正の証明検査が通らない対照に加え、変数で捕捉するだけの葉に `μ = :{8 μ}` があり、その外側の根 0・inner 1 自体は循環上にない入力は正に検証された。実際の適合モデル・辞書あり、捕捉は strict `μ < μ | Int` の区間のまま。この正例の `true` を言語の一般停止性とはしない。
- 個別 QA: 既存 compiler に余分の三 declared unary 中間型を与えたときに `some 1024` で、組合せは 4 種の比較項目だけ。定理は任意有限の共有接頭辞。literal source と checker の深さの範囲を広げない。

新規チェッカー分岐は where と固定出力なしの scoped leaf。元の ordinal / center を保持するための raw 表を証明書で照合するが、区間の型比較は中心値を使わない。元の二つの authored origins と照合に使った元の raw 行の整合性が必要、未だ不明な中心を一般に拒む実装ではない。

## Lean の axiom 出力（上の 8 standalone Audit）

```text
lean/Audit/Cycle440I74NestedInvariantSource.lean exit 0
'Yulang.GeneralDeclarativeI65.I72.NestedInvariant440.inherited_value440' does not depend on any axioms
'Yulang.GeneralDeclarativeI65.I72.NestedInvariant440.nested_raw_visit440' depends on axioms: [propext]
'Yulang.GeneralDeclarativeI65.I72.NestedInvariant440.visit_nested_scope440' depends on axioms: [propext]
'Yulang.GeneralDeclarativeI65.I72.NestedInvariant440.nested_has_no_raw_pattern_K2440' depends on axioms: [propext]
'Yulang.GeneralDeclarativeI65.I72.NestedInvariant440.Original.compare' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.NestedInvariant440.Original.head' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.NestedInvariant440.nested_captures_mean_in_same_model440' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

lean/Audit/Cycle440I74NestedInvariantRead.lean exit 0
'Yulang.GeneralDeclarativeI65.I72.NestedInvariant440.raw_cover_reflects_every_actual_visit440' depends on axioms: [propext,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.NestedInvariant440.rawBounds_exact' depends on axioms: [propext]
'Yulang.GeneralDeclarativeI65.I72.NestedInvariant440.replay440' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

lean/Audit/Cycle440I74NestedInvariantRule.lean exit 0
'Yulang.GeneralDeclarativeI65.I72.NestedInvariant440.Original.picked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.NestedInvariant440.Original.allOriginalOrigins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.NestedInvariant440.Local.evidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.NestedInvariant440.nested_only_dictionary_sound440' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.NestedInvariant440.actual_nested_selected_trace440' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.NestedInvariant440.actual_nested_classifies440' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

lean/Audit/Cycle440I74NestedInvariantEntry.lean exit 0
'Yulang.GeneralDeclarativeI65.I72.NestedInvariant440.dictionary_sound_R20' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.NestedInvariant440.all_previous_R19_Bool_unchanged440' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.NestedInvariant440.checked_nested_returns_original_report440' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.NestedInvariant440.check_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.NestedInvariant440.verified_R20_result_classifies_in_same_State440' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.NestedInvariant440.checked_nested_retains_raw_priority440' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.NestedInvariant440.no_new_nested_selection_over_original_raw_root440' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

lean/Audit/Cycle440I74NestedInvariantEndToEnd.lean exit 0
'Yulang.GeneralDeclarativeI65.I72.NestedInvariant440.ScopedExample.exact_original_nested_entry_all_three_modes440' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.NestedInvariant440.ScopedExample.actual_declared_inner_changes_when_inherited440' depends on axioms: [propext,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.NestedInvariant440.ScopedExample.wrong_modes_missing_explicit_cross_bad_origin_and_report_fail440' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.NestedInvariant440.ScopedExample.real_entered_inner_cycle_is_not_raw_root440' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.NestedInvariant440.ScopedExample.actual_root_K2_remains_on_previous_entry440' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.NestedInvariant440.ScopedExample.raw_outer_alternate_and_actual_visible_rival_cannot_be_ignored440' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.NestedInvariant440.ScopedExample.fitted_nonpoint440' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.NestedInvariant440.ScopedExample.same_original_nonpoint_selects_fixed_dictionary_with_two_centers440' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

lean/Audit/Cycle440I74NestedInvariantCrossings.lean exit 0
'Yulang.GeneralDeclarativeI65.I72.NestedInvariant440.inner_inspect_exact440' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.NestedInvariant440.wrapped_inspect_exact440' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.NestedInvariant440.wellformed_inherited_inner440' depends on axioms: [propext]
'Yulang.GeneralDeclarativeI65.I72.NestedInvariant440.declared_two_original_windows_compile_to_exact_four_families440' depends on axioms: [propext,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.NestedInvariant440.no_nested_int_float_comparison_in_same_full_assignment440' depends on axioms: [propext,
 Quot.sound]

lean/Audit/Cycle440I74NestedInvariantCoherence.lean exit 0
'Yulang.GeneralDeclarativeI65.I72.NestedInvariant440.original_nested_same_visible_selection440' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.NestedInvariant440.original_nested_same_fitting_bounds440' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.NestedInvariant440.original_nested_fitting_center_values_agree440' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.NestedInvariant440.two_accepted_nested_wires_agree440' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

lean/Audit/Cycle440I74NestedInvariantDepth.lean exit 0
'Yulang.GeneralDeclarativeI65.I72.NestedInvariant440.arbitrary_declared_unary_prefix_preserves_inherited_admission440' depends on axioms: [propext]
'Yulang.GeneralDeclarativeI65.I72.NestedInvariant440.compile_in_context_through_arbitrary_used_nominal_prefix440' depends on axioms: [propext,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.NestedInvariant440.every_depth_has_same_four_distinct_crossing_conditions440' depends on axioms: [propext]
'Yulang.GeneralDeclarativeI65.I72.NestedInvariant440.actual_emitted_row_count440' depends on axioms: [propext,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.NestedInvariant440.arbitrary_used_nominal_prefix_semantic_four_crossings440' depends on axioms: [propext,
 Quot.sound]
```

## 追加の独立対照の再現

最初の二つは、この pin の `lean/Audit/Cycle440I74NestedInvariantEndToEnd.lean` の完全な単一 source の後ろに、以下の対象 namespace を一つずつ連結し、production-only imports で `lean --trust=0 -DwarningAsError=true --stdin`。Audit 間の import は使わない。各対照の exit 0、標準のみ。いずれも上の 45 公開 Audit 行には加算しない。

### 別 locator / 同じ意味
```lean
open Yulang.GeneralDeclarativeI65.I72.NestedInvariant440
open Yulang.GeneralDeclarativeI65.I72.NestedInvariant440.ScopedExample
namespace Yulang.GeneralDeclarativeI65.I72.NestedInvariant440.ScopedAltQA
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeI65 (Origin visible)
open Checker408 (Problem)
open CommonNominalFullCarrier (Equivalent)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)

def extraOrdinary : GeneralDeclarativeHead320.State :=
  ⟨⟨atoms ++ [atomAt 2 5,atomAt 5 4],[]⟩,rawRows .listBox ++ [rawNominal 1 20 5]⟩

def actualWire : Wire := ⟨0,1,0,1,⟨[0,1,2,3,5,4],[0,1,1,1,1,1]⟩,
  ⟨[0,1,2,3,5,4],[2,0,1,1,1,1]⟩⟩
def alternateWire : Wire := {actualWire with innerRow := 4}

def observedCenter (p : Problem) (w : Wire) : Option Nat :=
  match scope : visible p.state.core p.root with
  | [d] => (replay440 p d scope w).map (fun a => a.center)
  | _ => none
def alternateProblem := build .listBox extraOrdinary

theorem both_original_wires_check440 :
    test .listBox alternateProblem (report .listBox) (.nested actualWire) = true ∧
    test .listBox alternateProblem (report .listBox) (.nested alternateWire) = true := by
  decide +kernel

theorem exact_original_centers_are_different_names440 :
    (alternateProblem.bind fun p => observedCenter p actualWire) = some 3 ∧
    (alternateProblem.bind fun p => observedCenter p alternateWire) = some 5 := by
  decide +kernel

def alternateModel (upper : Bool) : I72.Model :=
  {model .listBox upper with assignment := fun n =>
    if n = 5 then (model .listBox upper).assignment 3 else (model .listBox upper).assignment n}

theorem alternate_raw_original_input_really_fits440 (upper : Bool) {p : Problem}
    (got : alternateProblem = some p) :
    I72.Fits p.state (alternateModel upper) := by
  unfold alternateProblem build at got
  cases graph : GeneralDeclarativeWitnessSparseVariance357.compile GeneralDeclarativeWitnessVarianceFixtures357.source with
  | none => simp [graph] at got
  | some sem =>
    cases source : GeneralSourceMetadataBareBundle291.compile (surface .listBox [actual .listBox]) with
    | none => simp [graph,source] at got
    | some src =>
      simp only [graph,source,Option.pure_def] at got
      cases got
      refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
      · intro a used
        change a ∈ atoms ++ [atomAt 2 5,atomAt 5 4] at used
        simp only [atoms,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at used
        rcases used with rfl|rfl|rfl|rfl|rfl|rfl|rfl
        · exact CommonNominalFullCarrier.subtype_refl _
        · exact CommonNominalFullCarrier.subtype_refl _
        · exact GeneralDeclarativeWitnessRecordWindowFixture358.integer_to_payload
        · cases upper
          · exact CommonNominalFullCarrier.subtype_refl _
          · exact GeneralDeclarativeWitnessRecordWindowFixture358.integer_to_payload
        · cases upper
          · exact GeneralDeclarativeWitnessRecordWindowFixture358.integer_to_payload
          · exact CommonNominalFullCarrier.subtype_refl _
        · cases upper
          · exact CommonNominalFullCarrier.subtype_refl _
          · exact GeneralDeclarativeWitnessRecordWindowFixture358.integer_to_payload
        · cases upper
          · exact GeneralDeclarativeWitnessRecordWindowFixture358.integer_to_payload
          · exact CommonNominalFullCarrier.subtype_refl _
      · intro _ nil; cases nil
      · intro e seen
        change e ∈ rawRows .listBox ++ [rawNominal 1 20 5] at seen
        simp only [rawRows,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at seen
        rcases seen with rfl|rfl|rfl|rfl|rfl <;> exact eqv_refl _
      · intro _ nil; cases nil
      · intro o seen
        change o ∈ endpoints .listBox at seen
        simp only [endpoints,List.mem_cons,List.not_mem_nil,or_false] at seen
        rcases seen with rfl|rfl <;> rfl

theorem both_names_are_backed_in_the_same_original_fitting_State440 :
    ∃ p, alternateProblem = some p ∧
      I72.Fits p.state (alternateModel false) ∧
      observedCenter p actualWire = some 3 ∧ observedCenter p alternateWire = some 5 ∧
      ReportEvidence p.state (alternateModel false) p.root (report .listBox) := by
  cases ready : alternateProblem with
  | none =>
    have good := both_original_wires_check440.1
    simp [test,ready] at good
  | some p =>
    have a := exact_original_centers_are_different_names440.1
    have b := exact_original_centers_are_different_names440.2
    rw [ready] at a b
    have yes : check p (report .listBox) (.nested actualWire) = true := by
      simpa [test,ready] using both_original_wires_check440.1
    have fit := alternate_raw_original_input_really_fits440 false ready
    exact ⟨p,rfl,fit,a,b,(check_sound p _ _ yes).2 _ fit⟩

#print axioms both_original_wires_check440
#print axioms exact_original_centers_are_different_names440
#print axioms alternate_raw_original_input_really_fits440
#print axioms both_names_are_backed_in_the_same_original_fitting_State440
end Yulang.GeneralDeclarativeI65.I72.NestedInvariant440.ScopedAltQA
```

### 訪れない葉の循環 / 実際の適合モデル
```lean
namespace Yulang.GeneralDeclarativeI65.I72.NestedInvariant440.OffPathQA
open GeneralDeclarativeI65 (Origin)
open Yulang.GeneralDeclarativeI65.I72.NestedInvariant440.ScopedExample
open CommonNominalFullCarrier (Ty Subtype Equivalent nominal variant subtype_refl)
open CommonNominalFullDemand (Environment producerLe_iff_probe)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open GeneralDeclarativeHead320 (Equation)
open Checker408 (Problem)

def muLoop : Ty := .variant 8 (.block [.variant 8 (.inl 0)] 0)

theorem unfolding_at_every_depth440 (depth : Nat) :
    CommonNominalFullCarrier.observeTy depth muLoop =
      CommonNominalFullCarrier.observeTy depth (variant 8 muLoop) := by
  cases depth <;> rfl

theorem equivalent_to_its_unfolding440 : Equivalent muLoop (variant 8 muLoop) := by
  constructor
  · intro rank
    rw [←unfolding_at_every_depth440 rank]
    exact CommonNominalFullDemand.producerLe_refl _
  · intro rank
    rw [←unfolding_at_every_depth440 rank]
    exact CommonNominalFullDemand.producerLe_refl _

def higher : Ty := .union muLoop (.base .int)

theorem actual_loop_payload_strictly_inside440 :
    Subtype muLoop higher ∧ ¬ Subtype higher muLoop := by
  constructor
  · exact ((CommonNominalFullCarrier.common_union_is_join _ _ _).mp (subtype_refl higher)).1
  · intro h
    have badInt := ((CommonNominalFullCarrier.common_union_is_join _ _ _).mp h).2
    let e : Environment Common.Row := ⟨fun _ => .bottom,fun _ => []⟩
    have bad := (producerLe_iff_probe _ _).mp (badInt 0) 0 e (.variant 8 .trivial) ⟨rfl,trivial⟩
    exact bad

def raw : GeneralDeclarativeHead320.State :=
  ⟨⟨atoms,[]⟩,[rawNominal 0 9 1,rawNominal 1 20 3,
    ⟨2,.variant 8 (.variable 2)⟩,⟨4,.join (.variable 2) (.primitive (.scalar .int) [])⟩,
    ⟨3,.variant 8 (.variable 3)⟩]⟩

def leafWire : GeneralDeclarativeWitnessCycle350.Wire := ⟨0,⟨4,.same,3⟩,[],.same⟩

theorem genuinely_cyclic_uninspected_binder_is_supported440 :
    GeneralDeclarativePriority321.RootRecurs raw ⟨7,[⟨3,3,3⟩],[]⟩ ∧
    test .listBox (build .listBox raw) = true := by
  exact ⟨GeneralDeclarativeWitnessCycle350.rooted (w := leafWire) (by decide +kernel), by decide +kernel⟩

def installed : I72.Model :=
  {model .listBox false with assignment := fun n => ((match n with
      | 0 => nominal 9 [.inl (nominal 20 [.inl muLoop])]
      | 1 => nominal 20 [.inl muLoop]
      | 2 | 3 => muLoop
      | 4 => higher
      | _ => .bottom),Common.rowEmpty)}

theorem verified_hidden_cycle_fits_original_nested_meaning440 {p : Problem}
    (got : build .listBox raw = some p) : I72.Fits p.state installed := by
  unfold build at got
  cases graph : GeneralDeclarativeWitnessSparseVariance357.compile GeneralDeclarativeWitnessVarianceFixtures357.source with
  | none => simp [graph] at got
  | some sem =>
    cases source : GeneralSourceMetadataBareBundle291.compile (surface .listBox [actual .listBox]) with
    | none => simp [graph,source] at got
    | some s =>
      simp only [graph,source,Option.pure_def] at got
      cases got
      refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
      · intro a used
        change a ∈ atoms at used
        simp only [atoms,List.mem_cons,List.not_mem_nil,or_false] at used
        rcases used with rfl|rfl|rfl|rfl|rfl
        · exact subtype_refl _
        · exact subtype_refl _
        · exact actual_loop_payload_strictly_inside440.1
        · exact subtype_refl _
        · exact actual_loop_payload_strictly_inside440.1
      · intro _ h; cases h
      · intro e used
        change e ∈ [rawNominal 0 9 1,rawNominal 1 20 3,⟨2,.variant 8 (.variable 2)⟩,
          ⟨4,.join (.variable 2) (.primitive (.scalar .int) [])⟩,⟨3,.variant 8 (.variable 3)⟩] at used
        simp only [List.mem_cons,List.not_mem_nil,or_false] at used
        rcases used with rfl|rfl|rfl|rfl|rfl
        · exact eqv_refl _
        · exact eqv_refl _
        · exact equivalent_to_its_unfolding440
        · exact eqv_refl _
        · exact equivalent_to_its_unfolding440
      · intro _ h; cases h
      · intro o seen
        change o ∈ endpoints .listBox at seen
        simp only [endpoints,List.mem_cons,List.not_mem_nil,or_false] at seen
        rcases seen with rfl|rfl <;> rfl

theorem actual_nested_checker_and_dictionary_in_fitting_payload_cycle440 :
    ∃ p, build .listBox raw = some p ∧ I72.Fits p.state installed ∧
      check p (report .listBox) (.nested wire) = true ∧
      ReportEvidence p.state installed p.root (report .listBox) := by
  have accepted := genuinely_cyclic_uninspected_binder_is_supported440.2
  cases ready : build .listBox raw with
  | none => simp [test,ready] at accepted
  | some p =>
    have yes : _ := (show check p (report .listBox) (.nested wire) = true from by
      simpa [test,ready] using accepted)
    have fit := verified_hidden_cycle_fits_original_nested_meaning440 ready
    exact ⟨p,rfl,fit,yes,(check_sound p _ _ yes).2 _ fit⟩

#print axioms actual_loop_payload_strictly_inside440
#print axioms genuinely_cyclic_uninspected_binder_is_supported440
#print axioms verified_hidden_cycle_fits_original_nested_meaning440
#print axioms actual_nested_checker_and_dictionary_in_fitting_payload_cycle440
end Yulang.GeneralDeclarativeI65.I72.NestedInvariant440.OffPathQA
```

### 既存比較 compiler の実際の multiplicity
```lean
import Yulang.GeneralDeclarativeI65I74NestedInvariantDepth440

namespace C440ConcreteCompilerQA
open Yulang.GeneralDeclarativeI65.I72.NestedInvariant440
open Yulang.CommonRecursiveNominalIntervals (compileInContext)
open Yulang.CommonDeclaredNominalInspection (Registry)
open Yulang.PresenceNormalForm (Atom)

def table : Registry := [[inv],[⟨.value,.covariant⟩],[⟨.value,.contravariant⟩]]
def nestedRows : Option (List (Atom Nat)) :=
  compileInContext table false (pointWrap 0 (wrapMany [1,2,0] (nestedInner 2 1 2)))
    (pointWrap 0 (wrapMany [1,2,0] (nestedInner 2 3 4)))

theorem actual_1024_rows_with_only_four_atoms440 :
    nestedRows.map List.length = some 1024 ∧ ∃ generated, nestedRows = some generated ∧
      ∀ atom, atom ∈ generated ↔ atom ∈ finiteRows 1 2 3 4 := by
  have variants : UnaryUsedModes table [1,2,0] := by
    intro k found
    simp only [List.mem_cons,List.not_mem_nil,or_false] at found
    rcases found with rfl|rfl|rfl
    · exact ⟨_,rfl,.inr (.inl rfl)⟩
    · exact ⟨_,rfl,.inr (.inr rfl)⟩
    · exact ⟨_,rfl,.inl rfl⟩
  have semantic : nestedRows = some (inheritedRows 4 1 2 3 4) :=
    compile_in_context_through_arbitrary_used_nominal_prefix440 variants rfl rfl
      (.inr (.inr rfl)) 1 2 3 4
  refine ⟨?_,_,semantic,every_depth_has_same_four_distinct_crossing_conditions440 4 1 2 3 4⟩
  rw [semantic]
  exact congrArg some (actual_emitted_row_count440 4 1 2 3 4)

#eval nestedRows.map List.length
#print axioms actual_1024_rows_with_only_four_atoms440
end C440ConcreteCompilerQA
```

## 補足（cycle 440）: body からの分散と従来入口の実行確認

1. variant/body の明示分類を付けず、外側まで body から derive。nil 代替・実 payload・再帰 nominal tail を持つ list の body が invariant を算出。共変/反変の内側宣言も実 body から算出し、すべての source metadata classification は `.unclassified`。これを同じ実入口に読ませて三種類とも true。legacy metadata の flag だけが出た結論ではない。関数型 source simplifier を実装したという意味ではない。
2. [C439 の元の actual Audit](../../lean/Audit/Cycle439I74MergedOutputEndToEnd.lean) を同じ新入口の `.previous` から実行し、元の併合子の報告が true、元の raw root K2 が true、cycle のない入力の raw 証明書が false も確認。独立な元の適合モデルで C439 の report evidence が同じ新 R20 から得られる。
3. 明示 crossing の atom だけを落とした concrete Problem にも元の適合モデルがある。すべての fit で元の 2→3・3→4 から 2→4 を得る比較は正しいが、現在の証明書再生分岐は false。この未対応の証明を言語診断にしない。

再現手順: (1) は C440 EndToEnd single source の末尾に下記を連結。(2) は C439 EndToEnd の先頭に `import Yulang.GeneralDeclarativeI65I74NestedInvariantEntry440`、末尾に下記の対応する namespace を連結。(3) は C440 EndToEnd の先頭に `import Yulang.GeneralDeclarativeI65I74NestedInvariantDepth440`、末尾に下記 namespace を連結。三本いずれも個別の production-only Lean 4.35.0 `--trust=0 -DwarningAsError=true`、exit 0。これら 9 QA audit 行は公開 45 件には加えない。
 
### (1) body-derived current modes
```lean
namespace Yulang.GeneralDeclarativeI65.I72.NestedInvariant440.DerivedTableQA
open GeneralDeclarativeI65
open Yulang.GeneralDeclarativeI65.I72.NestedInvariant440.ScopedExample
open GeneralDeclarativeWitnessSparseVariance357 (Source compile lookup)
open GeneralDeclarativeWitnessConstructorModes357 (Environment readUse)
open GeneralDeclarativeWitnessSparseIntervals357 (names)
open GeneralSourceMetadataBareBundle291 (InputBundle)
open GeneralSourceMetadataRows291 (Row)
open Checker408 (Problem)

set_option maxRecDepth 15000
set_option maxHeartbeats 10000000

/-- The source includes a nil alternative, a live element and a
    recursive nominal tail at index 1. No invariant classification
    is supplied in its published metadata rows below. -/
def authoredBodies : Source 5 3 0 :=
  ⟨[⟨9,[(.value,0)]⟩,⟨20,[(.value,1)]⟩,⟨42,[(.value,2)]⟩,⟨90,[]⟩],
    fun i => match i.val with
      | 0 => .union .emptyRecord (.pair (.inr 0) (.inl 1))
      | 1 => .nominal 9 [.inl (.inr 0)]
      | 2 => .parameter 1
      | 3 => .arrow (.inr 2) .empty (.inl 4) .empty
      | _ => .base .int,
    fun p => match p.val with | 0 => 0 | 1 => 2 | _ => 3⟩

def surface (l : Lane) : InputBundle :=
  let rows : List Row := [⟨9,some ⟨[.type],9⟩,.unclassified⟩,
    ⟨20,some ⟨[.type],20⟩,.unclassified⟩,⟨42,some ⟨[.type],42⟩,.unclassified⟩,
    ⟨90,some ⟨[],90⟩,.unclassified⟩]
  ⟨⟨.absent,rows⟩,⟨.absent,rows⟩,⟨0,[⟨7,1,[]⟩]⟩,[actual l]⟩

def fromBody (l : Lane) : Option Problem := do
  let compiled ← compile authoredBodies
  let book ← GeneralSourceMetadataBareBundle291.compile (surface l)
  let env : Environment := ⟨5,3,0,authoredBodies,compiled,book⟩
  let s : GeneralDeclarativeI65.State := ⟨⟨env,ordinary l,[]⟩,table,endpoints l,[]⟩
  let b6 : B6OccurrenceAtlas401 s := ⟨fun _ _ _ _ => none⟩
  pure ⟨⟨s,b6⟩,⟨[71],roleDemand⟩⟩

theorem recursive_and_directional_modes_come_from_actual_body440 :
    ((compile authoredBodies).bind fun proof => lookup proof 9) = some [inv] ∧
    ((compile authoredBodies).bind fun proof => lookup proof 20) = some [⟨.value,.covariant⟩] ∧
    ((compile authoredBodies).bind fun proof => lookup proof 42) = some [⟨.value,.contravariant⟩] := by
  decide +kernel

theorem actual_public_R20_accepts_source_derived_outer_mode440 (l : Lane) :
    test l (fromBody l) = true := by
  cases l <;> decide +kernel

#print axioms recursive_and_directional_modes_come_from_actual_body440
#print axioms actual_public_R20_accepts_source_derived_outer_mode440
end Yulang.GeneralDeclarativeI65.I72.NestedInvariant440.DerivedTableQA
```

### (2) prior C439 actual entry through the R20 wrapper
```lean
namespace Yulang.C440OldBranchQA
open GeneralDeclarativeI65.I72
open C439MergedAudit

theorem real_C439_report_still_checks_at_R20440 :
    NestedInvariant440.check problem expected (.previous (.mergedOutput witness)) = true := by
  exact real_public_check_rejects_only_at_the_merged_child439

theorem raw_root_follows_existing_cycle_at_R20440 :
    NestedInvariant440.check actualRawCycle Check408.rawReport (.previous oldRawRoot) = true ∧
    NestedInvariant440.check problem Check408.rawReport (.previous oldRawRoot) = false := by
  decide +kernel

theorem prior_report_has_original_C439_meaning_under_R20440 :
    NestedInvariant440.R20 problem.state problem.root expected.verdict ∧
    NestedInvariant440.ReportEvidence problem.state originalModel problem.root expected := by
  have out := NestedInvariant440.verified_R20_result_classifies_in_same_State440
    problem expected _ real_C439_report_still_checks_at_R20440
  exact ⟨out.1,out.2 originalModel original_separate_output_cells_have_a_real_model439⟩

#print axioms real_C439_report_still_checks_at_R20440
#print axioms raw_root_follows_existing_cycle_at_R20440
#print axioms prior_report_has_original_C439_meaning_under_R20440
end Yulang.C440OldBranchQA
```

### (3) logical entailment versus scoped literal replay
```lean
namespace Yulang.GeneralDeclarativeI65.I72.NestedInvariant440.EntailedMissingQA
open GeneralDeclarativeI65
open Yulang.GeneralDeclarativeI65.I72.NestedInvariant440.ScopedExample
open CommonNominalFullCarrier (Subtype subtype_trans)
open GeneralDeclarativeWitnessFullIntervals357 (ContextDerives)
open CommonDeclaredNominalInspection (Parameter)
open Checker408 (Problem)

def finiteSlice : Option Problem := build .listBox (missingCross .listBox)

theorem genuine_no_literal_cross440 {p : Problem} (h : finiteSlice = some p) :
    p.state.core.current.ordinary = missingCross .listBox ∧ p.state.core.modes = table := by
  unfold finiteSlice build at h
  cases graph : GeneralDeclarativeWitnessSparseVariance357.compile GeneralDeclarativeWitnessVarianceFixtures357.source with
  | none => simp [graph] at h
  | some semi =>
    cases source : GeneralSourceMetadataBareBundle291.compile (surface .listBox [actual .listBox]) with
    | none => simp [graph,source] at h
    | some book =>
      simp only [graph,source,Option.pure_def] at h
      cases h
      exact ⟨rfl,rfl⟩

theorem absent_atom_still_follows_in_every_source_fit440 {p : Problem} (h : finiteSlice = some p) :
    check p (report .listBox) (.nested wire) = false ∧
      atomAt 2 4 ∉ p.state.core.current.ordinary.normal.ordinary ∧
      ∀ m, I72.Fits p.state m →
        ContextDerives p.state.core.modes m.assignment false
          (nestedEndpoint 9 20 2 4) (nestedEndpoint 9 20 2 4) := by
  have ⟨source,mode⟩ := genuine_no_literal_cross440 h
  have miss := wrong_modes_missing_explicit_cross_bad_origin_and_report_fail440.2.1
  change test .listBox finiteSlice = false at miss
  have noDirect : atomAt 2 4 ∉ p.state.core.current.ordinary.normal.ordinary := by
    rw [source]
    decide +kernel
  refine ⟨by simpa [test,h] using miss,noDirect,?_⟩
  intro m fit
  have hLo : Subtype (m.assignment 2).1 (m.assignment 3).1 :=
    fit.1.1.1.1 (atomAt 2 3) (by rw [source]; decide +kernel)
  have hHi : Subtype (m.assignment 3).1 (m.assignment 4).1 :=
    fit.1.1.1.1 (atomAt 3 4) (by rw [source]; decide +kernel)
  have compare := subtype_trans hLo hHi
  let param : Parameter := ⟨.value,.covariant⟩
  have used : validInner param := .inr (.inl rfl)
  have outMode : p.state.core.modes[9]? = some [inv] := mode.symm ▸ rfl
  have inMode : p.state.core.modes[20]? = some [param] := mode.symm ▸ rfl
  have empty : UnaryUsedModes p.state.core.modes [] := by intro _ impossible; cases impossible
  exact ((arbitrary_used_nominal_prefix_semantic_four_crossings440 empty outMode inMode used
    2 4 2 4 m.assignment).mpr ⟨compare,compare,compare,compare⟩).2.2

#print axioms genuine_no_literal_cross440
#print axioms absent_atom_still_follows_in_every_source_fit440

theorem no_direct_atom_input_has_a_real_model440 {p : Problem} (h : finiteSlice = some p) :
    I72.Fits p.state (model .listBox true) := by
  unfold finiteSlice build at h
  cases graph : GeneralDeclarativeWitnessSparseVariance357.compile GeneralDeclarativeWitnessVarianceFixtures357.source with
  | none => simp [graph] at h
  | some sem =>
    cases authored : GeneralSourceMetadataBareBundle291.compile (surface .listBox [actual .listBox]) with
    | none => simp [graph,authored] at h
    | some source =>
      simp only [graph,authored,Option.pure_def] at h
      cases h
      have t := fitted_nonpoint440 .listBox true (by
        simp only [build,graph,authored,Option.pure_def,bind,Option.bind] <;> rfl)
      refine ⟨⟨⟨⟨?_,fun _ bad => False.elim (List.not_mem_nil bad)⟩,t.1.1.2⟩,t.1.2⟩,t.2⟩
      intro a present
      change a ∈ [atomAt 2 2,atomAt 4 4,atomAt 2 3,atomAt 3 4] at present
      apply t.1.1.1.1 a
      change a ∈ atoms
      simp only [List.mem_cons,List.not_mem_nil,or_false] at present
      rcases present with rfl|rfl|rfl|rfl <;> decide +kernel

theorem actual_unread_certificate_is_not_inconsistent_input440 :
    ∃ p, finiteSlice = some p ∧ I72.Fits p.state (model .listBox true) ∧
      check p (report .listBox) (.nested wire) = false ∧
      ContextDerives p.state.core.modes (model .listBox true).assignment false
        (nestedEndpoint 9 20 2 4) (nestedEndpoint 9 20 2 4) := by
  have someProof : finiteSlice.isSome = true := by decide +kernel
  cases found : finiteSlice with
  | none => simp [found] at someProof
  | some p =>
    have fit := no_direct_atom_input_has_a_real_model440 found
    have entailed := absent_atom_still_follows_in_every_source_fit440 found
    exact ⟨p,rfl,fit,entailed.1,entailed.2.2 _ fit⟩

#print axioms no_direct_atom_input_has_a_real_model440
#print axioms actual_unread_certificate_is_not_inconsistent_input440

end Yulang.GeneralDeclarativeI65.I72.NestedInvariant440.EntailedMissingQA
```
