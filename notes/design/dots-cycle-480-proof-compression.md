# C480: 累積入口と Audit の短縮設計（設計だけ、削除なし）

基準: `integration/m1-final@68a3ab36cc67cc11fb0882fb1bd8c44559905fcf`, C479 の Lean tree `a24cabe42861ba7813214b35d5a6fcd419ba7578`、I-96 inbox `fc8efdbd0ecbd4530103467a11adba9933030fbf`。I-95 §3 の計画。下表は旧 public Bool の実 dispatch と、狭い事例の移行候補を区別する。置き換え・import 変更・削除は今回しない。

## I-96 を先に確認

`g04_producer_iff_eventwise_exists480` で、関数をひとつ存在させる `G04Producer` と、元の typed event・正確な prior phase ごとに忠実な有限 wire が存在する命題は古典的に同値。以前残った一文: **元の source 順序が保存されていない authored event で、同じ選択済み物理 root を最初に読む有限の raw/author 列を構成し、その列で独立な旧 `Read` と全く同じ報告が成り立つこと。** C480 では、実 root の既存 raw ordinal と実 authored ordinal を先頭に置き、残りの authored facts の既存 ordinal を写し、`GeneralDeclarativeInlineFootprint331.trace` の有限 footprint で `Read` を輸送することでこのケースも証明した。既記録 source 順は変更せず、released 枝には前から根拠のある exact completion 対応が要る。したがって **event-wise 存在と `G04Producer` 自体はこの範囲で証明済み**。この証明は実 compiler の生成関数や消去した履歴の逆算ではない。

別に、I-83 の既存累積入口は新しい I-93 型商報告をまだ処理しない。C459 の最新 `.fieldK2` は `RoutedReadyMixed457.ReportAtField` を受け、旧 `FieldDerivation` は raw `AliasCycle` と terminal-true の `Trail` を要求する。C479 の `SamePhaseInputObservation478` は元 `Pose`、選ばれた既存場所、最小型商の正負を持つ別の report で、旧 report へ data-only に押し込める既存枝は確認できない。例えば `Audit/Cycle476I74NamedQuotientActual.lean` の `selected_unrolled_sources_have_no_raw_cycle_but_exact_quotient_k2476` は raw の戻りがない実場所で型商の K2=true を示す。C479/C480 のデータ読取と局所経路の反映、独立な source 根拠つき同じ `FitsFull` の検証は得たが、**現在の累積 `check_full` に対して、新しい枝の exact report・根拠反映を既存外形の `check_full_sound` と同時に結ぶ仕事**は残る。残っていることを実 compiler の不存在とは取り違えない。単独の幾何 adapter の成功を source の発行証明にしない。今回 G04 全行や全 NoFalseRejection を決着済みとは数えない。

## 1. 一つの入口と正確な置き換え表

現行の累積トップは `HomogeneousClosedEntry459.check_full_homogeneous459`。C460 以降の局所 `read…` を累積トップと混同しない。`InstalledProtocolSum462.factorExisting`（`InstalledSameBoolean462.lean`） はそのトップの **全入力の Bool** と一致しているが、下位をまだ委譲する。これを最初の展開証明として使う。提案は互換アダプタと単一の `check_full_flat`:

1. 元の `Report × Witness` を、同じ枝のタグが一致する場合だけ平坦化し、その枝の元 report とデータを **無損失**に持つ一層の直和へ。旧 `.previous` は変換層だけで剥がす。対応しない組には `none`、新入口は `false`。初期 C447〜C450 は report が旧 `Checker408.Result` のままなので report を追加包装しない。成熟後の G03 や field のタグは report/wire の両方にあるため、双方の一致を検査する。
2. 新入口は `def check_full_flat (p : FullProblem) (r : FlatReport) (w : FlatWitness) : Bool` 一つでタグを選び、下表の現行 leaf checker に委ねる。既存の origin・構文・準備・安全条件を選び直さない。最初の移行では A の完全性や探索順を変えない。タグ不整合の `false` は旧入力の照合失敗であり、言語の診断 `.rejected` を合成しない。
3. 各旧エントリに変換と定理を持たせる。全 `p r w` で新旧 Bool が同じことを先に証明する（成功例だけでは不可）。旧 `Report` の分類と exact evidence を両向きに変換して、単独の選択・診断木、固定出力、元 occurrence、宣言 ordinal、物理位置、全 where 元位置の宣言順、比較の正負を保存する。旧版を残して同一入力の差分回帰を通す。

| 旧入口（外から内へ） | 平坦タグ・現在の leaf | 合流で落とさないもの |
|---|---|---|
| `HomogeneousClosedEntry459.check_full_homogeneous459` → `ProjectedClosedEntry459.check_full_projected459` → `RoutedInlineStructural458.check_full_structural458` | `field(.homogeneous / .projected / .plain)`、C462 `checkSameField` + `factorExisting` | exact `emptyKey` と cursor、同じ旧 raw K2 の field/stamp（正の true の枝）。タグ不整合や検査失敗が返す false も保存し、I-93 の安全報告とは混ぜない。 |
| `RoutedInlineVariant458.check_full458` → `RoutedReadyMixed457.check_full_ready_mixed457` → `RoutedReadyRecord457.check_full457` | `field(.inlineVariant / .readyMixed / .readyRecord)`、それぞれ現行 `checkField p.old` | 旧 `FieldWire` の型が異なる。準備、author 元位置、実 route を混ぜない。 |
| `RoutedNominalMixed456.check_full_nominal456` → `RoutedMixed456.check_full456` → `RoutedRecord455.check_full455` | `field(.nominalMixed / .mixed / .routedRecord)`、各 `checkField p.old` | C455 `RecordTrailEntry455` はこの直接鎖にないが、`RoutedRecordEntry455`・barrel・`Cycle455I74RecordTrail{Actual,Entry}` が import するため置き換え前に削除不可。I-93 post-C469 の report を旧 raw K2 で代用しない。 |
| C454 `SamePhase454.check_full454` → C453 `GroupedEntry453.check_full453` | `whereRawGrouped`, `whereGrouped`、`SamePhase454.check` / `checkGrouped453` | 元の異なる report 二種。raw Alias 類・原順位・旧完全ガードを保存。I-84 の表示代表未定、G03b の相遷移とは別。 |
| `WhereSites450.NoSiblingMerge.check_full450` → `ListSites449.Frame.check_full449` → `ListSites449.check_full449` | `whereRoot`, `listFrame`, `listSite`、各 `read…` と現行 `matchesNoWrites`、where は `noSiblingMerge p && WhereSites450.check_full450 p r (.whereRoot w)` | 元 `Result`、raw 子の K2 と親の誤代入防止、exact list の各実調査位置。 |
| `Opaque448.Whole.check_full448` → `Opaque448.check_full448` | `wholeBare`, `opaqueName`、現行 `readWholeChoice` / `readOpaque` と report 照合 | 解決済みアクセス・ロードの元 roster。nominal 本体を追加調査しない。 |
| C447 `SelectedReplay447.check_full447` → C446 `RetainedSplit446.check_full446` | `localSplitOutput`、`legacy446`。元の `readLocalSource`, `matchesSelection`, `matchesAssociatedReport432` と C446 を使う | 旧 B6 RHS、output ordinal・固定先・kind・同じ retained state。C446 は入口境界として温存。 |
| C479/C480 の `TypedInput` / `IssueIsFaithful` | **まだ平坦化対象にしない**。将来の一つの field 観測枝候補 | I-92 の二入力根拠、I-93 型商、実旧 root と選択済み prefix。既存枝との同 Bool と同外形健全性を証明する前に公開枝にしない。 |

## 2. G00–G03 の狭い C 分岐と検証の置き換え候補

以下は今の狭い成功だけで削除可という表ではない。元の [C 一覧](dots-cycle-423-c-coverage.md)、[G 計画](dots-cycle-443-no-false-rejection-design.md) を基準に、各 narrow 型の report/wire を新タグに送る exact compatibility と全依存移行が先。意味論対象外の C 行も勝手に畳まない。

| 元の狭い領域 | 使う一般化（局所前提は維持） | 残す回帰／削除を許す条件の候補 |
|---|---|---|
| C22 の一点 where 無し 1 mixed-ref 出力の保持、および C442/445/446 のその狭い中継 | G00 `selected_wire_iff_exact_local_report447`, `independent_selected_report_has_finite_witness447`, `check_full_sound447` | 旧 exact B6/固定 target、異なる target と異なる型の対照、`Cycle447I74SelectedEntrySpec`。C11/C12 の明示・既定、C14 の非点や一般 release を吸収済みとはしない。他の経路が C446 に依存する限り legacy446 は残る。 |
| C01 の名付き nullary bare nominal、C448 の narrow opaqueName | G01 `exact_call_site_choice_iff_whole_wire448`, `Opaque448.Whole.check_full_sound448` | `Cycle409I74NamedSpecX12`、`Cycle448I74OpaqueWholeSpec` の元 X12 と roster 誤差／未知の負対照。`NamedPriority409` と `OpaqueRead448` も旧 Named を参照。狭い fixture を一般入口経由で再現し旧 input 全体同値を得た候補だけ。 |
| C02 の単一点 invariant list-binder、C449 の単 site | G02 `exact_frame_wire_iff_independent_report449`, `ListSites449.Frame.check_full_sound449` | `Cycle410I74ListSpecX8`、`Cycle449I74ListFrameSpec` の別の root / 未訪問位置 / 位置順の対照。`ListPriority410`・`ListInspections449`・`WhereListRule411` の依存を先に移す。bare nominal と list 根の識別、非点・任意構造は同値性なしで消さない。 |
| C03 の単一 where 子を通る根 K2、450–453 の sibling なし／一群の狭い枝 | G03 I-85 同相 C454 `exact_same_phase_report_iff_finite_wire454`, `check_full_sound454` | `Cycle411I74WhereListSpecX9` と `Cycle454I74WhereSamePhaseActual` の親／実子、raw 別群、元順、欠落・重複負。C453 の whole-roster scope と C454 が違う場合はアダプタ保持。`WhereLegacy450`・`WhereListPriority411` の旧依存も先に移す。G03b、where 出力、診断表示決定は代替しない。 |

## 3. 固定声明と検証計画

- I-65 の `dictionary_sound`、`check : Problem → Result → Witness → Bool` とその `check_sound` の型・中身をこの短縮で変えない。旧公開 namespace と名前も残す。累積 side の旧公開 `check_full_sound447` ほかは、全 `p r w` の Bool 等式から従来の `ClassifiedAsFull p.state p.root r ∧ ∀ m, FitsFull p.state m → ReportEvidenceFull p.state m p.root r` を同じ引数で再取得する。C453 以降の `ClassifiedAs p r ∧ ∀ m, FitsFull p.state m → ReportEvidence p m r` も同じ型を維持する。新しい effectful compilation や別 state への埋め替えを含めない。
- 変更を提案する実装回では (i) 各旧入口の **全入力** Boolean compatibility、(ii) 独立 report と全 Fit 証拠の保存・反映、(iii) 同じ最上位 soundness の既存 `#check` / `#print axioms` と source-to-wire 完全性の再監査を順に行う。旧 report 運搬が困難な枝を unsafe downgrade せず、どちらの polarity が欠けるかを個別に記す。既存 source truth, settlement, solver 探索・停止、I-93 equality を新しく定義しない。
- Audit の最小構成案: 共通 fixture データを一箇所（既存の code と test 分離を保つ）＋各 G 行ひとつの隔離 standalone に主定理と代表 exact true/false＋一つの旧 compatibility inventory。上表の各 X 経路および元の負対照を名前つきで維持し、一つの expected 結果を再利用する形への置換を検討する。単なる axiom print の型・核が同一のものだけを候補表に載せる。guarded 実行を theorem の証明には使わず、同じ fixture を別の package や tool が参照していないことを確認する。
- 削除のゲート: import と依存者一覧、各旧 branch の等価証明、差分比較（失敗も含む）、全既存 Audit/集約の監督役検証、置換元／先一覧を提示し、それから **別のユーザー承認で一度だけ**。この設計・今回の I-96 追記では旧モジュール、Audit、report、spec、State、checker を一つも消さない・書き換えない。意味論未決事項を新たに決めない。
