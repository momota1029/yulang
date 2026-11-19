# dots-main cycle 283: 実 install の差分再評価と、履歴の値・索引の有限性を区別する

- 定刻・実際の開始とも 2026-11-19 22:30:00 UTC。記録終了 2026-11-19T23:20:06Z（50.10 分）。全 73 パスの変更。公開先は private `work/dots-main` のみ（非強制・expected head）。使用量の枠は不明。
- 開始時と作業中に `integration/m1-final` の standing orders と inbox を再取得。統合先 `e62f33b58`、ACTIVE / I-51〜53、凍結指示に変更なし。282 完了 `0f9cf719` を検証し、作業者がいないことを確認して開始。新たな統合版の全 import は作業版に既にあり、凍結を保ってローカルへ ancestry を取り込み、282 より後の作業を巻き戻さなかった。
- 途中の検証済み tree: 早期 `29e938e0`、10分 `00d24b0b`、20分 `44c0e2d5`、30分の照合・修復 `1dd1275c`、40分 `68141268`。30分の最初の配信は worktree の編集中の barrel に当たり、一時的に import 先2本が不足した。既に focused build が通っていた2本を追加して直後に全 tree 一致を確認。以後は指定 commit の内容だけを取得し、編集中の内容を使わない。停止・別作業者による書き換えはなかった。

## 何を証明したか

1. **履歴の更新を候補だけから計算（健全性・完全性）**。任意の実到達する旧 journal とそこを snapshot とする候補 effect について、旧候補に Common があることを前提にせず、`GeneralRebaseInstallCache283.add_valid / lookup` は新 packet の版付き定義だけを旧の正順台帳に挿入する。既存キーと同一の新行は RHS も同一である。実型読みを書込の差分に沿って伝播し、影響された行だけ再評価しても全履歴の最初からの解と各型・各 row が完全一致（`GeneralRebaseIncrementalHistory283.exact_update`）。入力割当も、任意の有限リストの型座標だけ変えて row は全域一致なら、同じ差分キャッシュで再 probe できる（`GeneralRebaseCrossProbe283.exact_refresh`、actual `GeneralRebaseSparseGate283.semantic`）。row 変化まで無視すると型中の矢印の効果が変わる閉じた反例を添えた。
2. **実 install の判定と全 path（健全性・完全性、停止性は別）**。`GeneralRebaseIncrementalGate283.enabled` は実 registry・source reachability・旧ガードを保ち、旧 catalog の型支持に変化があった検査だけを再評価する。旧モデルの合格が分かっていれば非影響レコードは再評価不要。新規 plan の安全・材料化・Known・真の novelty・生成済み条件は保持。既存 effect の live class は新しい出力と少なくとも片側が新しい等式対だけを別に追加し、古い snapshot の effect は捨てない。`GeneralRebaseClassLocality283.merge_local / install_fresh_request` は、merge の影響が両端の旧 alias class、install の新規出力が追加サイトに限定されることを示す。`GeneralRebaseFrontierPairs283.fast_count / actual_iff` は旧旧対を列挙せず、新しい要求数×現在の要求数×2 以下で等価な対だけを列挙。全 journal の一般的な可判定性や I/O を含む速度上界ではない。
3. **再帰 evidence を安全に slice（健全性・完全性）**。`GeneralRebaseSliceExact283.exact_support / queries` の後ろ向き slice は、問い合わせから型読み辺で届く定義をちょうど保持し、その読みで全 solve と一致。row は全名前で保存。実 journal と任意の payload の同時成立は、同じ割当を共有する有限の証明 plan 集合を選び、その支持だけを読む式と同値（`GeneralRebaseSliceEvidence283.exact_finite_query`）。成功した役割 default と明示出力、実 provenance、子の順序・重複を残す。未知の子を成功扱いしない。有限証明 plan の存在は各証明から導いたもので、探し方が可判定・一様有界とは証明していない。
4. **古い二反例の全履歴を値では有限にする（補助、具体例では完全）**。`GeneralRebaseOneSource283.reflects / meaning` は、同じ元の変数を重複する union/inter の単純形を識別。異なる変数や一般の交互式を誤って一つにしない。`GeneralRebaseVersionAliases283.canonical / GeneralRebaseLooseAliases283.canonical` は n 段すべての履歴定義の根を 239 では 2、240 では下端 2・上端 4 と決定し、任意の base の全旧意味を相互部分型と全 row 一致で保存。raw の versioned key をあらかじめ有限だと仮定していない。`GeneralRebaseFreshOnlyCache283.quick_exact / reads` は旧右辺が真に新しいキーを読まない場合、新 packet だけから処理行を選べる。両実反例の任意段につきちょうど2行（`…FreshOnlyFixtures283.Version.quick_two / Loose.quick_two`）、optional の二回目も新 lower/upper のみ。逆に実版付きキャッシュに必要な索引は n 段で 2n（`GeneralRebaseArchiveUnbounded283.version_exact / loose_exact`）。この representation 全体の一様有限性は否定され、raw を保持する限り無制限 driver は依然 non-Acc。
5. **運用 successor を区別（補助・停止性）**。`GeneralRebaseCachedDriver283.initial_paths` は実経路との双方向対応、`GeneralRebaseCanonicalCache283.raw_next_exact` は同じ raw 終点に余分なキャッシュ非決定性を入れない。`GeneralRebaseGuardedCache283.paths / accessible` は cycle281 の chart/phase が選ぶ既存の関係に対してのみ経路と Acc を移す。optional の実3遷移を保持。Display の実非葉 `.node 1 [.node 3 []]`、206 の default `.node 37 []`、optional の出力・payload を sliced 形で検証。218 の拒否を緩めず、最終状態から新しい cached transition が出ないことも型付き使用例で確認。230/233 の旧監査は再確認。

## 検証・根拠

- Lean 4.35.0。新39モジュール、独立監査6本・133宣言（標準公理のみ）PASS。各新モジュールを `lake env lean --trust=0 -M 3200 -DwarningAsError=true -R . -o …` で再構築。各監査は単独実行、import は `Yulang.*` のみ。barrel への全登録と凍結を両方照合。9+2 行の `#eval`、7 件の型付き実使用。実出力、監査の全文、モジュール一覧、両方の static diff の出力全文は [verification/cycle283](../verification/cycle283/)。
- `bash tools/verify-lean.sh . <統合先／前回ローカルpin> --no-build` は両方 PASS。全体 `lake build`、CI、新たな Yulang2 バイナリ実行は常設指示に従い行っていない。旧独立監査の結果と制限は同 verification の `legacy.txt`。cycle283 自体は全件通過。
- Yulang2: `work/dots-audit` `55574b60` の X1（子が宣言に現れるレジストリ）、X2（旧実機が増大 where を許す差）、X3/X5（実機で直接表せない構文）、C3-ROLE-01/02（固定済みの仕様上の挙動）を比較。今回は spec 構文や受理ルールを変えず、既存 Lean 判断の解釈を差分化した。新しい言語上の判断を求める質問ノートはなし。

## 残りの名前付き候補

1. 一般段階における `NoBackReads` の source 由来証明または反例。現在は厳密なフォールバックあり。生の「予約名」を型の意味支持と混同しない。
2. 版付き環境を保存せずに済む一般の有限 fact basis と、`Known` と `Local` の独立実装。今回の 2n の結果により、索引を保持したままの単純な圧縮は全体の有限状態化にならない。
3. 各 install の旧 plan を繰り返さずに済む差分 class catalog と、source graph による finite candidate 証明探索。今回は raw-indexed semantics と各証拠 witness の exact slice まで。完全な EvidenceNode、汎用停止性、独立 finite executor は未達。
- 次周の証明分解は [cache-erasure design](../design/2026-11-19-cycle283-next-cache-erasure.md)。
