# dots-main cycle 276 — 実際の Display 非葉から V8 証拠と停止証明へ

- 開始: 2026-11-19 15:30:08 UTC。報告記録: 2026-11-19T16:20:09Z（経過 50.02 分）。
- 275 の公開済み成果から開始。公開済みの範囲内に途中コミットと心拍を残した。実行機械と証拠判定を含む主チェックポイントは `d93cdf57`、HeadAlloc 差分の検査は `7750ecdb`。
- 開始時の integration は `3382f7ea`、途中で `751fde8d` に進んだため、両時点で standing orders と inbox を取得。後者について報告前にも再取得した。指示ファイルの両 blob は同一、ACTIVE、I-51〜53 と凍結を適用。
- 実装は private `work/dots-main` のみ。今回追加の導入ガイドは [こちら](../design/2026-11-19-cycle276-nonleaf-certificate.md)。

## 証明したこと

1. **実際に子を1個持つ正例。** 旧 198 の Display 正例をコピーして結論だけ再利用するのでなく、234 の versioned/mixed 環境で親が実際に確保する点・子の識別子・入出力・両端の式・子が指す登録 source 1 を照合した。この子は Int の葉で、親子が異なる識別子であることと、別の識別子同士を分離するモデルも確認した。有効な任意の settled モデルで本物の V8 `Evidence … (.node 1 [.node 3 []])` を構成し、`GeneratedChildren` と順序付きの子リストを明示した。
2. **実際の source からの唯一の Step と停止。** `GeneralNominalVersionedMixedBoundary234` の直接の具体初期状態から、234 の実際の `Step` は親の install 1 回だけ。到着状態は安定し、refresh と追加 install は起きない。子はこの時点で意味論的に既に committed で、2 回目の install を仮定しない。元の初期状態での `Acc` と到達集合の完全な特徴付けまで証明した。
3. **実行可能な判定。** 2 状態・ランク 1→0 の機械が、この具体到達集合の実際の Step を両方向で反映し、両状態で同じ full-model predicate を保つ。Checked Local から親と Int 葉の順序付きペイロードを実行可能に生成する。settled full model の任意の有効な割当について、Bool の判定が本物の証拠と同値。親だけ・余分な子・誤キー・足りない fuel を誤って受理しない。
4. **独立な一般化。** source/row/seed を保存する refinement の下で、現行 Frame・`Observed197`・committed semantics・Ready と子順序の一致を各節点が供給すれば、mixed refresh 越しに任意の有限非葉辞書を運べる。任意の子数を扱うが、必要な節点証明の一律生成は仮定しない。スカラーは別補題で、元の観測値が対応先へ写ることだけを証明した。また Int 底から作る限定した nominal tower について厳密ランクと非循環性を確認した。

## 残っていること

- 別の `GeneralNominalVersionedMixedSourceBoundary234` adapter は、初期状態を元の registry で作り、Step・診断・証拠を HeadAlloc encode 後の registry で判定するため未接続。Display の2宣言も role 0 での列も不変だが、無関係な Wrap の出力バインダーのキーは 21→1701 で、registry 全体は不変ではないことを Lean で確認した。さらに、効果に registry が記録されるため生の到着状態は一致しない。同じ plan と snapshot なら core とモデル述語が一致することは証明済み。次は必要な role に絞ってコンパイル後の効果を構成し、その二状態を対応づける。
- 任意 source の V8 producer、任意の scalar 子の辞書、一般の停止、public projection から full model を再構成する定理は未証明。観測の輸送と辞書の生成は区別した。

## 検証

- 新規ライブラリ 23 モジュール、独立監査 23 本で 211 個の個別宣言について標準公理のみを確認。全追加モジュールを trust=0・警告エラー化で個別検査した。 独立監査23本と主要14モジュールを再検査して全件 PASS。 監査は `Yulang.*` のみ import。
- `git diff --check`、統合ベースおよび 275 ベースに対する `tools/verify-lean.sh --no-build`、凍結パス差分と追記のみの import を確認。全 lake build や CI の実行は主張しない。
- [検証マニフェスト](../verification/cycle276/verified-manifest.txt) / [独立監査の再検査](../verification/cycle276/final-audit-recheck.txt) / [主要モジュールの再検査](../verification/cycle276/final-fixture-recheck.txt) / [実行例7件](../verification/cycle276/executable-fixture.txt) / [HeadAlloc 差分の検査](../verification/cycle276/encoding-diagnostic.lean)。

次: direct boundary と HeadAlloc adapter 間で、親のフレームと source 1 の実子が保存される条件を切り出すか、別の実在する非葉 source を同じ粒度で検証する。非葉 198 の direct 正例や 230 の既検証の葉を再実装しない。
