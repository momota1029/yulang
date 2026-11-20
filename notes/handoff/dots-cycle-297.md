# dots cycle 297: B4 の実 source observer と有限のモデル証跡

## 再開と範囲

定刻 2026-11-20 12:30 UTC、実開始 12:32:48 UTC。統合先
`3d17bf3001770ac8dea4cea935dbd1ef82ede594` の standing orders → inbox を再読。
新規 **I-54** に従い、Rust CST の拡張はせず、Lean の registry・goal から始まる B4 本線へ戻った。
前周の `ff9d762e03d051f6bfaa9278465c5aaa6342ec38` の完了心拍・報告・全 tree を照合した。
最新統合 tree `bf155630ff333085a4c64cfcd3f6e4a7a98ad4b6` は blob を照合してローカルで再構成し、
既存 Lean の upstream 差分をすべて保持。新しい inbox は検査基準にだけ取り込み、
作業 branch に上書きしていない。期中の inbox 再読でも変更はなかった。
`work/dots-main` のみ、期待 head を親に非強制更新し、各公開の親・全 tree・head を読み戻した。

## 結果

1. **任意の到達 source の候補を、有限の質問にする（健全性・完全性）。**
   `GeneralRebaseSignedModels297.pass_exact / accepted_exact / rejected_exact`:
   既存の registry と snapshot に一致する実 effect と任意の割当について、
   「直前の Models を満たし、plan と現在の class effects を同時に満たす」は一つの
   joint Residual と実 install 後の Models のどちらとも同値。
   反対の符号は、直前には通るが実 install 後は通らない割当であり、
   その存在が semantic novelty。新しい子辺による novelty は別の既存ガード。
   到達性のない一般状態では新たな出力要求の Delta が別に残る
   （`loss_includes_delta`）。両符号は同一割当では両立しないが、
   異なる割当で両方存在できる。直前に Models がなければ両方不存在。

2. **一状態につき必要な証跡は有限（完全性に使う補助）。**
   `GeneralRebaseSourceQuestions297.entries_exact` は実の generated occurrence と
   ready-plan 列から質問を漏れなく列挙する。候補が N 件なら install 両符号を
   高々 N+1 個の直前モデルでカバーできる（`GeneralRebaseWitnessAnchor297.exists_pool`）。
   head は直前の Models を仮定しない別の存在判断。merge は順序を保った実 center の
   各対応位置を比較し、登録 site が S 件なら、各順序付き組の反例を追加した head・install・merge
   全体の証跡は高々 2N+S²+1 個（`GeneralRebaseWitnessExistence297.smaller_pool`）。
   上界は行数だけ。証跡の選択は古典的で、任意の型の新しい求解器ではない。
   検査済みの行からの集計と位置 lookup は実行可能。
   未登録位置は `none`、登録済みで被覆された問い合わせの偽は `some false`。
   merge の負例を欠く未検査表が誤って true を返す実行対照も残した。

3. **射影が変わる実 B4 の一歩に、対応する observer の一歩がある（健全性・完全性）。**
   `GeneralRebaseSourceMetadata297.source_strict_exact`:
   任意の到達状態、検査済み有限証跡、生成 occurrence の正確な raw SafeKnown と任意の
   射影表に対し、有限 observer の一歩 iff 同じ射影先を持つ実 raw Step があり、
   その射影は直前と異なる。型構築子表・解釈が全 raw Step で保存されることを証明し、
   metadata は初期 source から導出し直した。
   構成する effect は既存の Frame・Unique・Ready を持ち、raw install の選択整合・cache・
   materialization・cycle ガードを残す。V8 最終診断の `selected` を仮定し直す必要は
   ない。独立の四つの安全 probe を集計する部分は、未知・否定・肯定を区別し、
   決定済みかつ健全な probe の条件だけで完全になる。任意 source でこの安全 probe が
   決定済みになることや、V8 の優先順位・最終分類の変更は主張しない。
   射影の不変な raw 管理歩は区別され、厳密一歩がないことを raw 停止とは読まない。

4. **実例と鋭い限界（入口の検証と補助）。**
   252/271 の `F(Int) → F(F(F(Int)))` では実生成・一つの候補・実据え付けを
   二つの直前割当で再現した。入力座標と全効果行が同じでも出力座標 3 だけを
   変えると符号が反転する。raw SafeKnown・semantic novelty・joint のいずれを
   無効にしてもこの据付候補は出ない。別の実 install 前 refresh で 0 と 1 を既知にした後も、
   新たに列挙した同じ候補の二符号を同じ割当表で再確認した
   （`GeneralRebasePreInstallReplay297.listed_after / retained_coverage / retained_answers`）。
   一般の証明は現在 context の一致と pattern 観測を明示しており、任意の見直し・全相には
   適用しない。233 の optional 実 install は新しい辺なしでも semantic novelty と
   joint の両方が成立する旧回帰。
   239 と 240 の実ループでは各 **n 周の前置区間の棄却割当の最小数が厳密に n**。
   いったん落ちた同じ割当は後の直前 Models に戻れないため。既知の bad 割当が上界を
   達成する。いずれも全周で使える共通有限台帳はない
   （各 `GeneralRebaseSignedHistory297.*.finite_prefix_minimum / no_universal_rejections`）。
   同じ数え方を正準な相対 port の観測や修正版の一般停止性へ外挿しない。

## 検証

- Lean 4.35.0、`--trust=0 -j 1 -M 3200 -DwarningAsError=true`。
  新規 **24 モジュール**を既存 cache とは別の影 cache に順に再構築。
  9 本の Yulang のみを import する独立監査で **全 176 定理**を検査。
  標準の `propext`、`Classical.choice`、`Quot.sound` の範囲。実行対照 4 本を
  保存済み出力と照合し、旧 267/269/271/279/280/281/284/285 から 21 本の対象監査を再実行。
  [正確な定理一覧](../verification/cycle297/theorem-index.md)・
  [再現手順](../verification/cycle297/README.md)・[独立再構築全文](../verification/cycle297/focused-replay.txt)・[原本 SHA-256](../verification/cycle297/source-sha256.txt)。
- [実 nested output](../verification/cycle297/depth-observer.txt)、
  [merge](../verification/cycle297/merge-observer.txt)、
  [二符号と位置](../verification/cycle297/signed-polarities.txt)、
  [実 install 前 refresh](../verification/cycle297/preinstall-transport.txt)。
  merge の二対照は比較 fixture であり、別途検査した既存の strict merge は stress state
  の実 kernel step（その stress state 全体の source 到達性は未主張）。
- [静的検査全文](../verification/cycle297/static/)で、前周と最新統合 tree を基準とした
  `tools/verify-lean.sh --no-build` がそれぞれ exit 0。統合基準側は検査専用の一時 commit
  を使い、公開していない。追加モジュールは同じ変更で barrel に一度ずつ追記。
  既存 Lean モジュール、Rust、spec、lakefile、作業 branch の inbox は変更していない。
  全体 Lake build、全統合監査、Rust、CI は実行していない。
- Yulang2: 既存の監査 branch `55574b6052ef1534fd0fc36d6d3617ebede59a0e` の X1/X2/X3/X5
  （where の実行可能例・増大 where との差・構造型入力の旧文法限界）と照合。
  新しい内部 ledger を旧実機の観測と同一視していない。Rust の再調査は I-54 に従い不要。
  仕様判断を求める新しい質問ノートなし。利用枠不明。

## 次の候補

1. 実 source の一般 observer の残りは、古典的に選んだ行を、独立に完全性を示せる
   実モデル探索へ置き換えること。ordinary/signed 制約ソルバの grammar・width・row の
   前提を検査し、決定できない枝を未決として残す。現証明は有限の質問表であって有限値域ではない。
2. 安全 probe の否定側の source 由来の完全性、特に K2 の経路の被覆を、選択済みの
   heads と独立に証明する。最終診断と raw が同じであるとは仮定しない。
3. 一状態の install 前 refresh の結果を、enqueue・equate・reobserve を含む相へ
   伸ばす。raw 239/240 の下界を繰り返さない正規形と、B4 の一般停止性・
   EvidenceNode の再帰は未証明。

[有限質問の設計](../design/2026-11-20-cycle297-b4-signed-model-questions.md) /
[raw guard と分類の分離](../design/2026-11-20-cycle297-b4-raw-observer-guard.md) /
[実 refresh の証跡再利用](../design/2026-11-20-cycle297-refresh-signed-reuse.md) /
[構成的モデル探索の設計](../design/2026-11-20-cycle297-next-real-witness-search.md)

- 最終報告書の固定時刻: 2026-11-20T13:22:52Z（経過 50.07 分）。前周からの変更 68 ファイル（完了心拍・報告を含む）。
  書き込み後に固定 pin で報告と完了心拍を読み戻す。
