# cycle 489: 実訪問の K2 を局所照合より前に確認する

道具: モデル不明、Lean 4.35.0; 委譲: なし。
使用量: 不明。

## I-100 / G05Goal: 元候補の実訪問、優先順位、同じ State の証拠

- `G05ExactSignedRoster489` は、元の可視列と同じ長さで、各位置に元の登録 ordinal と、独立な実訪問による K2 の真偽を保持する。任意の元問題と独立判定について、この命題を満たす列は一意（`exact_g05_signed_roster_is_unique_in_original_order489`）。局所分類の一価性や報告の観測表記は要らない。正の部分列は元登録順に厳密に増え、重複なし。
- `readG05Preflight489` は実需要の根を元順で検証し、範囲を元の座標に固定する。既存の型商と全候補の有限 tape を再検査してから結果を返す。任意の非空座標で、名前つき `G05ExactVisitInputs487` の下では局所照合なしで実行が成立する。その任意の成功陽性は、独立に実際の prefix 許可が揃って再帰位置まで訪れた元候補を、過不足なく元順に返す。失敗と全候補安全の成功は別。
- `routeG05WithDeferredLocal489` は、先行検査が陽性なら、候補選択はもちろん、局所照合・full report の供給も要求しない。それ以外で続行できるのは、従来の完全な C488 検証が通り、報告が全元候補の元順の `.eligible` 分類を持つ場合に限る。根が空の挙動も、既合格の full route（独立な実訪問の前提つき）も保存する。旧 checker、型および辞書選択規則は変えていない。
- `G05SignedReceipt489` は元根と全候補の signed tape だけを持ち、局所 token・分類・自己申告の陽性を受け取らない。別の呼び出し元が出した有限 tape も、各元候補・元経路を再検査して同じ結論に達する。先行検査が成功したときには必ずこの形の有限証拠を再現でき、非空の独立 exact scope ではこの有限証拠が通ることと自動の同じ出力が同値。候補パケット不足を安全と扱わない。
- `every_early_g05_hit_has_same_fit_constructor_return_at_its_actual_original_slot489`（および supplied signed receipt / checked full report 版）: 任意の検証済み陽性の元 ordinal には、その元候補・元引数・元の許可済み非空訪問がある。実訪問キーの終端で、元のチェック済み有限 cone 上の非空 constructor walk が同一の型商のクラスに帰る。一つの同じ有限帰路について、元 `p.state` に適合する全モデルで終点の型と出発位置の型が等価になる。新しいモデルや局所 verdict は選ばない。
- `a_replayable_exact_g05_report_exists_iff_every_nonrecursive_slot_has_some_local_verdict489`: 独立な exact scope と有限の局所 protocol を固定すると、完全な報告とその受理される有限証拠が存在することは、各実非再帰の元候補に独立に認められた何らかの局所判定があることと同値。候補の全実訪問は有限の元 roster から読み、引数ゼロも含む。局所判定が全候補に揃わず完全報告が存在しない場合でも、実 K2 の早期判定はできる。これは存在であり、判定が一意であることや、実 compiler が自動供給することではない。
- 元の同じ役割・需要・状態を固定して独立 prior が比較可能なら、その包含に対して実 K2 は単調で、先の確認済み元 ordinal 列は後の列の部分列。二つの独立 exact prior が実際の元 Trail 上の必要 prefix で一致すれば、非空の同じ元要求の先行検査は同一結果。仕様や許可を広げる提案ではない。

## 具体的な対照

- 実候補の二つの K2 は局所照合器・報告・局所受領証なしでも `[1,3]`。実 registry を並べ替えると二件を新しい登録順 `[0,3]` で保持。未訪問の引数または変数で捕まえるだけの候補に権限データを置いても、その循環は陽性にならない。
- 全候補の signed tape から最後の候補パケットまたは実 K2 の経路だけを消す、元順を逆にする、元需要と異なる座標を渡す、いずれも実行検証は不成立。元報告への偽の三つ目の陽性は full checker が拒み、独立の早期経路は元の二件だけを返す。
- I-93 の対照: 実 source の named child と、等価な一段展開した inline child は `[1,3]` で一致。inline の訪問位置は raw graph そのものの循環上にはない。入力の関係表から inline と named を直接結ぶ対応を省いても、この例では計算される型商は同じ。異なる constructor 形を同じとする偽の辺は実検証を通らない。
- 非公開の追加対照として、四つの permission bit の全 16 通り、二段経路で必須 prefix を欠く signed receipt（拒否）、inline の同じ元状態に実際の適合モデルを構成した上での同じ有限帰路、ならびに非再帰候補の局所規則が空で完全報告が存在しないのに実 K2 は確定する対照を、個別に厳格検査した。これらのローカル試験ファイルを、新規の Audit 間依存としては公開していない。

## 範囲・削除

`G05Goal`、`G04Entry`、元 flat checker の既存 blob はそのまま。C488 の full report の条件と独立した局所意味の前提は維持した。今回は G05 の実訪問・優先順位・同じ State の陽性証拠を進めたが、`G05Goal` という定理の宣言、G04 の閉鎖、一般の局所照合器、compiler からの prior の生成、辞書選択、曖昧性や診断位置の決定を行っていない。I-100 の期限は C492。新しい質問ノートなし。

I-100 の 18 旧入口の権威 Lean tree は [C487 の直接逆依存明細](../design/dots-cycle-487-i100-old-entries.md) と同一。どの入口にも、まだ通常 production と個別 Audit の直接 import がある。例: `WhereSamePhase454` を `WhereSamePhaseSource454` が `InternalReport` / `exactReport` に利用し、`FlatDispatch481` は実際に旧 raw-grouped の入口を呼ぶ。権威の 10,732 Lean ソースを今回も SHA から照合して直接 import を数え直し、18 入口すべてで production / Audit 両方を確認した。新規削除 0 ファイル・0 宣言、移した import 0、C486 の受領済みの重複 Audit 削除は再計上しない。

## 検証・公開

Lean 4.35.0。新規 production 13 と個別の Audit 5 を固定公開コミットから取り直し、全 18 ソースの Git SHA を照合した上で別の焦点用出力先にて `lean --trust=0 -DwarningAsError=true`（exit 0）。新しい 63 定理の標準公理出力は `propext / Classical.choice / Quot.sound` の集合内のみ。独立の対象 Lake `--no-cache build --wfail` は段階 A/B/C が 3/3/2 jobs（各 exit 0）。C481、C487、C488 の旧テスト計 6 も Git blob を取り直し、3 回に分けて各 3 jobs・exit 0。新規 Audit から既存 Audit への import なし。禁止構成なし。

公開済みバイトを検証したログ SHA256: A/B `fb5aff5a21c191d1eb46afadd71e512b451e664ccd1f16126aa3061e2bb56b23`、C `2850d50a4806b8d92e2f175cfccd5cae737420d41c251b2f27a072915c0c32f8`。今回および旧回帰対象の repository ソース依存 4,638 件は、入力の権威・既公開差分・今回の正確な差分の Git blob と照合し、欠落・未解決 import とも 0（一覧 SHA256 `16075da9ec5a1ab7fa2589f514d1e01856ab392d49a06a1d9c1063b77e06a91c`）。依存確認は全依存の再ビルドではない。全体の Lake build、`tools/verify-lean.sh`、Yulang2 実機は実施していない。

開始 `2026-11-28T12:29:01.494Z` UTC。権威 `dc51fb0613f5df358f1ff4cc86a39dff22981a8b` の常設指示 `7ae4d68d2ac7df80d1eadbd061dadd2296faf4c4` と I-100 inbox `5dbffec4b4d8b9b6664230cb5f7773b9b9d71301`、前回の完了報告を読み直した。開始心拍 `664424f30f86dd4e954896bc32778e86afdcd462`、+10 `9dec40f3f94cb0533c5bc059ff0158f1fede63a0`、+20 `0917c526f5fdf4715b87ec600a7d33c8619d76e8`（Lean tree `7101ac3b57c659634611d4725d0355817a3505c3`）、+30 `d7d52f2feefe18e33741347b543be342ae7ad28e`（Lean tree `12af44b81c9739adeb0fda540ee868fb84d26e7a`）、+40 `dc85635f5c97826e401b4ad1106ff57ef466a84c`（最終 Lean tree `9430b3ba42033fe0d2c52fcb8347bb4624864fc7`）。+40 時点で前回最終との差分 24 パス、追加 22、集約 import と心拍のみ変更、削除なし。今回の Lean 差分は 19 パス（既存の 1 ファイルは集約 import の 13 行追記のみ）。`G04Entry`、`G05Goal`、`FlatDispatch481`、`Audit.lean`、inbox、spec は前回最終と同じ Git blob。最終はこれに報告を 1 ファイル加え、完了心拍を更新するだけ。公開先は `work/dots-main` のみ。

+45 の再取得（`2026-11-28T13:14:03.880Z` UTC）でも権威・inbox・作業先端・検証した Lean tree が同じと確認した。報告時刻 `2026-11-28T13:19:01.496Z` UTC、実開始から 50 分。照合と報告は 55 分以内。