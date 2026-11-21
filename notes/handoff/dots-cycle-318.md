# C318: 記録済み where 行の由来と、新規・再利用が混じる一つの要求

2026-11-21 09:30 UTC / 18:30 JST 枠。開始時と終了前に
`integration/m1-final` の常設指示・inbox を確認。指示の両版は不変。integration は途中で
`fc059f2157cf0dc4bcf35697ccc956951b174571` から
`b31b5fa0fbe056a9d3c82cca2f4aca60d7bc29ed` へ進み、主要な C317 の据付・
再利用・回帰の三ソースが作業時の版と同一であり、C318 の新規36モジュールの
パスが integration 側には未作成であることを確認。
C317 完了 `ac6c3f215a4ffaee155bd9612285b4f1471209d2` を照合した。
I-55 の (4) 型推論・辞書健全性を優先し、停止性は扱っていない。

## 検証したこと

1. **slot があるだけでは根拠にしない。**
   `Compiler318.materialized` / `Schema318.exact_schema` は checked canonical compiler
   の実出力を、実出力／裸変数の自明行／実ソース位置を持つ版つき複合行に同定する。
   `Trace318.from_lookup` と `Config318.already_holds` は、有限の配置差分を検査した
   隔離版の履歴なら、既存 slot からその生成宣言の実記録を取り出し、
   任意の同一 journal model で現行を証明する。履歴の配置検査は観測の意味を
   自動では保証しない。現フレームと過去の設定を照合するので、
   owner だけで別の出現を同一視しない。
   `Receipt318.exact_receipt` では宣言・where 節・引数位置・極性・記録行そのもの
   まで一致することを証明した。C317 の実据付は、手指定の表ではなく
   コンパイル済み入力から列挙する `CheckedLayout318.enumerated_trace` を通過。
2. **混在を同一モデルで処理。** `Partition318.checked_batch` は既存 slot の行を
   読み直し、真に新しい行だけを書き込む。予約・言及だけで slot がない場合や、
   既存 journal・現フレームの保護座標とぶつかるものは新規としない。
   `FreshRead318.fresh_not_read` は、後から既存端点を読むことを許したまま、
   本当に raw にない新規番地が既存の現式の読みに使われないと示した。
   `Assemble318.modeled_preinstall` は旧 journal・現ヘッド・捕獲・class と
   全コンパイラ行を同じモデルで満たす。関連出力の既存証明は別に保持する。
   `LayoutContract318.exact_insertion` は実際に追加する物理 slot と書込対象を
   ちょうど対応させ、由来のない追加や既存 slot の書き直しを排除する。
3. **一つの実観測・生成区間に上端再利用と下端新規が同居。** C316 そのままでは
   重複 capture の集約番地が区間列全体を符号化するため、両足跡が変わる
   （`ActualShift318.both_move`）。同じ検査を通る別 fixture で第二の名を独立させると、
   同じ二つの実 nominal 観測から、同じ owner の生成子に対し、上端は同番地、
   下端は別番地となる（`SingleCells318.unique_endpoint`）。
   `SingleCommon318.common` は両 raw 文脈と旧現四行を一つのモデルに置き、
   新下端の割り当て後も旧下端・旧上端の割り当てを完全に保持する。
   `HeadAgree318.exact_observations` はさらに旧現の `HeadModels` を同じモデルで満たす。これは実観測と
   実コンパイラを使う試験で、別 fixture の混在据付の全到達履歴や子選択は未証明。
4. **実据付に接続。** `Install318.executes` は、実 pre-install の選択と prior-choice
   互換、有限 layout、候補範囲・raw 側の意味証明、出力を要求しない子などの明示前提
   のもとで、旧記録と新記録が同一モデルを持つ実隔離 Step と生成 edge を構成する。
   `RealInstall318.executed` で C317 の実初回据付をこの経路から再構成。
   `CheckedFixture318.rechecked` で C317 の再読（両端点再利用）も同じ行分類を通過。
   なお hidden field に現れる名前の raw 読みは表面的な正規形スコープからは導けない。
   `Shadow318.checked_shadow_example` は、具体的な隠れた値の束縛を仮定せずに
   端点と実 center の間の包含に必要な式の区間性が保たれると示す。一般の正規化と
   混合モードを含む interval 導出は未完。

## 残り

- **(4) 2群。** (4a) 別 owner の prior-choice/alias 宣言鍵を一般に保つ証明。
  (4b) 一般の混合履歴での物理 slot 配置・raw 観測の意味保存、出力要求を追加する子の
  class 更新、全パターンでの interval/現 head 前提の生成、そして実際に再帰選択された
  各子の同一モデル証拠。今周は (4b) の記録済み行の由来、有限書込と両側の守るべき
  モデルを閉じたが、一般の本体は未完。旧カーネルの C316 の反例は残る。
- **(2) 2群。** 一般 observer/compiler の証拠生成、および停止成功時の実到達経路・
  返却地点の安定・宣言的分類との一致。停止性は証明対象外。
- 次は、混在 fixture で実際に旧上端の物理 slot を残したまま新下端を配置する raw
  producer を検証し、`RawTicket`、実の再観測、子 Frame / Evidence につなげる。
  [設計ノート](../design/2026-11-21-cycle318-where-origin.md)。使用枠の残量は不明。

## 比較・公開

Yulang2 実機との照合は未実行。既存の Lean の checked 構文・実観測・生成規則と比較し、
元の C316/C317 fixture と新しい比較用 fixture を区別した。言語の規則・既存コードは
変更していない。Rust、CI、実 Sat、全体 Lake build は未実行。
[対象ビルド、全ソース trust=0、独立監査・追記差分](../verification/cycle318/verification.md)。
旧 head 指定の非強制公開は `work/dots-main` のみ。固定コミットの全差分を照合した。
