# C417: C09 / X6 後半の検証記録

固定技術コミット: `9f3242f3742abc1e62ac4f1d346e87123af737eb`。Git の Lean tree: `84940bfb96de2b0043e26437d186c6fffa801236`。
前提は [仕様 6.2・6.3](https://github.com/momota1029/yulang/blob/ad65248e70b70ca116703701c55bbb220c5e21c6/spec/06-roles.md#L51-L118) と
[X6](https://github.com/momota1029/yulang/blob/ad65248e70b70ca116703701c55bbb220c5e21c6/notes/handoff/2026-11-08-m1-spec-examples-conformance.md#L24)。
開始時の integration の Lean tree は検証済み C416 と一致。この記録の検証対象は作業ブランチ上の固定コミット。

## 三条件

1. `R9` は `R8` の選択規則を変えず、同じ一点要求の実可視リストに plain と ground が両方当たる場合だけ局所 `.ambiguous` を追加する。
   各候補は別の実宣言と元 ordinal、宣言の role と head、元の型資料を使う。両方が同じ実 payload を読む。
   `dictionary_sound_R9` は同じ状態の任意の fitting model に対する既存 `DictionaryEvidence` のまま。
2. `X6Ambiguous417.check` は有限の元行・元宣言・元観測の index と二つの raw escape のデータだけを検査する。
   ground 用に同じ payload の元 `.ordinary (.base .int)` 観測が必要で、int の生等式は代用しない。
   ground の実 visit は根とその payload、plain の合流後 visit は根だけ。raw K2 は候補の根拠で絞らない。
   元の report は `.ambiguous` / `.ambiguous` / 空 writes。旧分岐への委譲は定義上同じ。
3. `X6Ambiguous417.check_sound` は元の State・Request・Report の `ClassifiedAs` と同じ State の全 fitting model の `ReportEvidence`。
   対象状態に R9 の別の診断や選択はない（`exactly_the_ambiguity_classifies_for_actual_X6_417`）。
   一般に R9 の成功した辞書・元イベント・順序つき書き込みは R8 へ戻せる（`successful_report_unchanged417`、`no_new_successful_dictionary417`）。

## 再現・結果

- 公式 Lean `4.35.0`（`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`）。固定版の各 blob を取り出し、
  `git hash-object` で一致を確認してから、
  `lake env lean --trust=0 -DwarningAsError=true -o <新しい .olean> <対象 source>` と
  `lake env lean --trust=0 -DwarningAsError=true <standalone audit>` を実施。
- 独立 C417 **10 source / 4 audit**、C416–417 合同 **20 / 8**、I-74 の C409–417 scoped **78 / 49**。
  いずれも終了 0。各スコープで元の barrel の全バイトに今回の import だけが追記されたことと、その import 集合の検査を確認。
- 独立 C417 の `#print axioms` **48 個**は `propext`、`Classical.choice`、`Quot.sound` の範囲内。
  凍結した `lean/Audit.lean` と `lean/README.md` は内容を開かず blob ID の不変を確認。lake 設定・toolchain メタデータも不変。
- 両宣言順、各宣言順で三つの元 ordinary 行の六順（計 12）、自動の有限番地対照で正しい元の二宣言・二観測を確認。
  元観測無し、同名/誤番地、ground の違う tag・primitive、第三候補、偽の選択／書き込み、payload や根の生 K2 では曖昧と報告しない。
  実 off-path cycle と同じ payload を指す実 alias は正例。
  載らない inner K2 の一般報告 checker はこの周に足していない。旧の根 K2 は元観測が欠けても従来どおり。
- 追加のローカル回帰では同じ固定 source / audit を再利用し、C409–C416 の 17 対照を新入口の `.previous` 経由で再実行（11 true、6 false）。
  C417 の 4 対照は `[true, true, false, false]`。同じ二つの fixture で
  各元番地 0–3 の7座標（16,384 組ずつ）を列挙し、通ったものは各宣言順の正しい元番地一組だけ。
  この列挙は固定 fixture の実行対照であり、一般完全性の証明ではない。


## 限界

対象は I-74 の C09 のみ。検査器は元の自己 join 行を作らず、既存の元行がある範囲を検証する。
異なる alias payload、証明できていない根拠、出力・where、任意多候補を一律に言語の拒否とはしない。
`false` はこの検査枝で所定の証人を確認できなかったことだけを表す。
全リポジトリビルド、Rust、solver の NoFalseRejection、停止性は実行・主張していない。

[C の残り 13 行](dots-cycle-417-c-coverage.md)。

## 追加のモデル・有限照合の対照

固定コミットから作った独立作業ツリーで、C417 の Spec/Graph audit を読み込んだ補助検査です。
本体の scoped build や上記 48 個の個別監査とは別の検査で、Lean tree は変えていません。

- 実 off-path の `2 = :{tick 2}` に `μX.:{tick X}` を割り当てると、同じ X6 State が `Fits`。
  元 slot 0 は `:{tick int}`、元 slot 1 は `int` のままです。
  `μX.:{tick X}` と一回展開した型の全ての深さの観測が等しいことを、
  [C410 の同型の観測証明](../../lean/Audit/Cycle410I74ListSpecX8.lean) と同様に示しました。
  off-path raw cycle 自体が存在し、同じ fitting model でも C417 の曖昧報告の `ReportEvidence` が成立。
  循環のない自明なモデルで済ませたのではありません。補助定理の axiom audit は標準のみ。
- 四つの候補 slot の palette 値を 0、1、2 から独立に取る 81 通りを、根と payload の証人に別々に試しました。
  rank は実 alias が同じ class になるものを使用。根 gate 数、payload gate 数、最終 report を通す対の数の順で次の結果です。
  色が式を決めるのではなく、色候補は判定済みの生グラフを検証します。

| 固定状態 | 根 gate | payload gate | 曖昧の証人対 |
|---|---:|---:|---:|
| 元の二候補 | 9 | 9 | 81 |
| 根の実 K2 | 0 | 0 | 0 |
| 入った payload の実 K2 | 9 | 0 | 0 |
| 入らない実ループ | 6 | 6 | 36 |
| 同一 payload への実 alias | 9 | 9 | 81 |
| alias を介した別 payload | 3 | 9 | 0 |
| int 生行はあるが元 int 観測なし | 9 | 9 | 0 |

最後の二対照では gate のどちらも通る有限データがあるため、元 payload への読みと元の型つき観測の検査は独立に必要です。
この表の有限試験から一般の証人生成や完全性は主張しません。

- 同じ型でも別の元 slot では代用できないことを補助検証しました。元 (1) と別の (2) を同じ `int` に割り当てた fitting model に対し、独立 int 観測を (1) から (2) に移すと、実 payload の int 生行があっても曖昧の証人を受理しません。型の不等しさではなく元番地の不一致です。これは既定の [6.3「根拠のある頭」・raw K2](../../spec/06-roles.md#L182-L213) の区別と整合します。
- 固定版の `#check` でも `DictionarySound R9`、全 fitting model の `check_sound`、元 int 観測の番地定理、R8 と R9 の成功同値を確認しました。C402 の定義、C407 の R₀、C408 統一入口、C416 入口、C365/C380 の固定文は integration・開始 work・現 work の三者で blob ID が同一です。
