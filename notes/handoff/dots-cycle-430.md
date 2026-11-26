この周に閉じた C の行: なし。
Audit の import: `Yulang.*` 以外 0 件

# C430: C428 の Audit 7 件を単独実行できるよう修復

開始: 2026-11-26 01:31:03.000 UTC。I-77 の対象 BodyReplay / IntegratedLegacy / LegacyTrace / RootFrame / SingletonTape / TapeBoundary / Trace のみ修復。元の監査対象30件を保ち、共有の元データ・wires・選択／再生証拠を3つの `Yulang.*430` helper に分離。既存 MixedSibling、C429 修復済み Audit、その他の監査の blob は不変。変更許可のないファイルには触れず、barrel は末尾 import 3 行の追記だけ。元の証明・テストは、共有定義の移動および import/namespace 参照の切替を除き同じ。C428全9監査の公理表示43件の宣言名と公理集合は修復前の依存順結果と完全に一致。

## 終了コードと再現

- Lean 4.35.0 `--trust=0 -DwarningAsError=true`。対象7件だけでなく、C427/428 の変更 Audit 全16ファイルを、それぞれ空の一時 cwd にコピーして、production-only `LEAN_PATH`、Audit olean ゼロの状態で単独実行し、**16件すべて exit 0**。上の import 件数はこれら16ファイルについて Lean 自身の header parser での実測。標準公理の表示93件（propext, Classical.choice, Quot.sound のみ）。
- 同じ条件で、修復前の C428 の対象7件はすべて exit 1（`unknown module prefix`）。修復後は同じ実入力・同じ検査を維持して exit 0。統合済み R14 公開入口で復元済み legacy 子を受ける既存テストも通過。R15 を追加したわけではない。
- 候補 Git から拾い直した各ファイルの byte を blob ID と照合し、production 24本すべて再コンパイル。24 import の同時読み込みも exit 0。全体ビルド、Rust、網羅性、停止性、NoFalseRejection は実行していない。凍結ファイルは blob ID のみ確認。

## 統合に渡すもの

技術 pin `5812d3bd90559aa723223674b4718e81d6ea5a4a`。 [C427–C430 combined exact replay](../design/dots-cycle-430-i77-supervisor-replay.md) blob `4390c5f491bc616d85253afaaba17ed5607e09d0`。既存統合の基準に Lean-only A40/M1 の正確な差分（40 path + barrel の末尾24 import）を投影すると、root tree `737989c8b146516bf93c58ae3f7f56ff101a0442`、Lean tree `881d83f60dd5ca7064e241f8a7f71f0a5f7efee1`。`git mktree` と `diff-tree` で独立照合済み。監督の統合は別、ほかのブランチへ書いていない。 現行統合 `9ef86984658f7d5b152d0b56685033d7dc940e0b` で40 blob・barrel・Lean tree の完全一致を確認し採用済み。GitHub Actions 実測は `proof` cancelled、`core` success。このサイクルの focused 検証とは別で、全体の PASS は主張しない。

**C の残り: 8 行（C15–C22）。**
