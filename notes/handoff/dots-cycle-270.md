# Cycle 270: 実行できる後継 Step と検証付きの有限探索

- 指示: I-52 (rebase 後継 Step)・I-51 / I-53。対象は検証済みの範囲だけ。
- 開始: 2026-11-19 09:30:00 UTC。報告作成: 2026-11-19T10:20:06Z（50.10 分）。使用量の枠: 不明。
- 前周: 完了した cycle269 の公開 `157c21459328db42119c52326288d8e672036535` と心拍を照合。未完復旧なし。ローカル開始 tree はその公開 tree と一致。
- 指示とベース: 開始時 integration `1b113cfd93bd7ab89ccb1e4b29653dfd5f655775`。途中で `499b87919b44c2d2acb8b573236a4b171bd92a32` に進んだので公開を保留し、standing orders と inbox を新しい commit から再取得。両 blob（`7ae4d68d2ac7df80d1eadbd061dadd2296faf4c4`・`2f6b72446884d0e340537ac4b9aea1bb6c0e047d`）は変更なし。STOP なし。最新 integration と同じ tree `ee118f23bc38259f33c3a0685da46eb47ba468d7` のローカル等価祖先 `9f6a6104f` を静的検査に使用した。
- 公開: `work/dots-main` のみ、expected-head 付き non-force。報告・検証を含め前周から 83 ファイル。途中公開: `9482d38a`、`3a4ecc29`、`5f4aab41`、`0b362bc8`、`e16ef9b1`、`b613c718`、`a249da93`、`ca697056`、`fcfa604a`。
- 中断・制限: integration 進行時に上記照合を実施。途中の一回は差分開始点に誤って現在のローカル commit を指定したため空のパスで tree 作成前に拒否され、正しい前 checkpoint の commit を指定して再試行。失敗した要求では ref は変更されていない。

## 成果と主張の範囲

1. **実例 238、rank 2 の完全な初期挙動と有限後継 Step。**
   `GeneralRebaseRetainedMetadata270.from_empty` と `GeneralRebaseCompoundProjection270.all_equations` は、実 journal の任意の旧到達列と保持済み plan に対して、該当出力の body 式が一つであることを示す。単一 owner・出力に対する body と自己 pair の二つのアドレスは同時に現れる。`dichotomy` は任意の旧到達状態で残りが実際の二要素か空。`all_weak_targets` は実初期状態の任意の旧 `Weak` 出口について後者を示す。
   `GeneralRebaseCompoundExecutable270.initialCode_exact` と `computed_run` は条件なしで実初期 canonical code を決定し、その実行結果を計算する。一回の可視遷移で空の terminal leaf。さらに `GeneralRebaseSourceStepDriver270.Compound.exact_weak_targets` は任意の有限後継ターゲットについて、有限 rebase Step があることと、同じ初期状態からその射影を持つ旧 Weak 証人があることを同値にする。逆向きの実証人は V8 install。 `matches_concrete` と `no_second` はその install の射影と二歩目がないことを照合する。具体的な全 successor の同一性や、この例の任意のフルランクの別状態からの網羅性は主張しない。
2. **出力要求なしの断片を実際の root と registry から認識。**
   `GeneralRebaseNoOutputs270.trace_quiet` / `fixed` は、根に要求がなくすべての宣言の子節が出力要求を発行しないとき、任意の旧到達列と任意の固定 basis で可視射影が一定であることを示す。子がないとは仮定しない。`GeneralRebaseOutputFreeCompiler270.compiler_sound` は有限な入力検査が受理した root・registry のすべての到達状態について canonical code と一致。認識外（実例238を含む）は `none` であり停止ではない。`GeneralRebaseSourceStepDriver270.OutputFree.exact_empty_observer` は受理した断片の全到達状態で空の有限 observer が正確と示す。`GeneralRebaseOutputFreeRegressions270.Version239.visible_stop` と `Version240.visible_stop` は、任意の非停止ループ段・可視燃料・固定 basis で可視進展は 0 回である一方、元の旧関係では `¬ Acc` のままという回帰。
3. **独立検証可能な旧遷移の replay と有限探索。**
   `GeneralRebaseReplayCommand270.run_sound` は任意の入力 command が計算した after を旧 `Step` が認めること、`supported` は任意の旧一歩にそのような command が存在することを証明する（一般の自動抽出ではない）。`GeneralRebaseWeakSpine270.normalize` は供給した順序と strict 数を保持。`GeneralRebaseReplayFrontier270.certificate` は任意の供給 frontier の正結果から検証済みの旧 Weak 証人と対応する経路を取り出す。`no_visible_advance` は列挙済み経路だけの lull。`GeneralRebaseReplaySearch270.none_rules_out_bounded_weak` は供給 schedule が全旧一歩を網羅するという別の証明がある場合だけ、指定した raw 深さ以下の Weak を除外する。深さ0で失敗する238は深さ1で実 install を返す。実 refresh/reobserve の二歩を含む frontier は全候補が lull。
4. **再帰判定の両極を処理する有限 semantic Origin 窓。**
   `GeneralRebaseMixedOriginWindow270.certified` は、full model の存在証人、対象窓の検査、比較の Reflection のもとで rigid pair/variant、scalar、nominal 型位置に対し有限窓の健全性と前向き網羅性を示す。`GeneralRebaseOriginRepresentative270.representative_sound` は返された raw slot と source または一段 nominal 型引数の全モデルでの意味の一致を保証する。 `GeneralRebaseOriginNegativeTags270.distinct` は full model 一つで異なる tag を得れば全モデルでの等値を否定。tag 同士の一致では何も推論しない。
   `GeneralRebaseClosedOriginDriver270.inspectRoot_sound` は full model が少なくとも一つ存在する場合、全 raw slot から窓を構築し root の引数および該当 site の center の `RootCycle` 結果を sound に返す。`inspect_exact` は窓が閉じ、すべての edge が確定し、問い合わせの代表が見つかった場合の完全性。`GeneralRebaseClosedOriginFixture270` は明示的な full model を持つ二つの synthetic journal で、variant と nominal の往復を正、nominal から Int を負として計算し、意味論の両命題を証明。二例とも全 edge が確定。未収録 origin は unknown。surface からの到達性は主張しない。
5. **レコードを pair のように扱うと誤る理由を証明。**
   `GeneralRebaseRecordTagBoundary270.duplicate_hidden` は任意のラベルと payload で外側の同じラベルが内側を隠すことを full carrier で証明。`GeneralRebaseRecordWindowBoundary270.no_literal_exhaustion` は一フィールドの raw 正規形を持つ任意の journal に対し、「正の arity を持つ semantic Head は記録された単一 literal test に限る」を否定（`[l,l]` も Head）。`noncanonical_hidden_excluded` は full model が存在するとき、影になる二番目の位置が任意の Origin と Equal にはなれないことを示す。canonical な位置の正の edge は `canonical_positive`。一般の record 窓の完全性は未証明。

設計・境界: [design](../design/2026-11-19-cycle270-executable-source-behavior.md)。
各モジュール名と全宣言名は [cycle270 の監査一覧](../verification/cycle270/) の `*-modules.txt` と `*-declarations.txt` に記載。仕様変更やユーザーの設計判断を要する問題は発見せず、質問ノートは追加していない。

## 検証

- Lean 4.35.0、各新規モジュールを `lean --trust=0 -DwarningAsError=true -R . -o <isolated .olean>` で新規コンパイル。新規出力だけ隔離し、従来モジュールの既存キャッシュを使用。終了 0。[再コンパイル出力全文](../verification/cycle270/final-fresh-recompile.txt)。
- `cd lean && lake env lean --trust=0 -DwarningAsError=true -R . Audit/<file>.lean` を監査ごとに独立実行。9 監査、28 モジュール、277 宣言。終了 0、許容された標準公理のみ。最新の新規隔離キャッシュでも監査を再実行。[監査集計](../verification/cycle270/final-audit-recheck.txt) と各 `*-audit.txt` に出力。[11 対象の focused 再検証](../verification/cycle270/final-fixture-recheck.txt) も終了 0。
- `bash tools/verify-lean.sh . 9f6a6104f --no-build` と前周からの同検査 `... 9c415785a --no-build` は終了 0。出力全文: [integration 同一 tree 基準](../verification/cycle270/diff-gate.txt)・[前周基準](../verification/cycle270/prior-cycle-diff-gate.txt)。[凍結と barrel](../verification/cycle270/freeze-and-barrel.txt) も確認（barrel 末尾だけに各新規モジュール一回）。全体の lake build、CI、Yulang 実機は実行していない。

## 残り

- 任意の旧全経路を網羅する source 由来の有限 observer・behavior key を抽出すること、ならびに一般の公開モデル保存・反映。出力ありでも今回の rank-two 以外は未検証。
- 影になる record 位置の否定と最初の可視位置の正確な比較を任意のラベル列へ一般化し、閉じた有限窓に統合。deferred、residual、モデル自動構築、任意の等値は対象外。
- I-52 の一般の置き換え遷移、surface 一般への soundness / completeness、V8 EvidenceNode と全回帰の移植は未完。旧 kernel の停止は結論でなく、239/240 では明示的に否定されたまま。
