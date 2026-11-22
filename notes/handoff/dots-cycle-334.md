# C334: I-60 の証人つき宣言分類から、同じモデルで辞書の根拠へ

## 今回の範囲

01:30 UTC 枠。開始 2026-11-22 01:34:48 UTC、報告時刻 2026-11-22T02:24:49Z（実 50.0 分）。終了前の integration は e60c9f2240e4a9eaf5b5ef85bc107a3acf4c1960（指示・spec の 3 blob は開始時と同一）。開始時の `integration/m1-final` は `e60c9f2240e4a9eaf5b5ef85bc107a3acf4c1960`。standing orders、inbox（I-60）、spec §6.3/6.5 と直前完了版 `eebbb67128b5e09524bb4c0cae0bb6e2f249ddda` を確認。I-58 の選定後の実中心等式と、I-59 の狭い根 K2 を変更せず、I-60 の新分類で (4) を先に証明し、旧定義との対応、(2) を別に扱った。変更先は `work/dots-main` のみ（expected-head、nonforce）。主証明・独立監査の固定 pin は `dbbce5897c89b27ed508797271429173d53b9d02`。

## (4) 証人つき分類の辞書健全性：残り 0 群

- `WitnessHead334` の `Argument / Actuals` は、本物の named trace、inline read、対応する区間射影を区別し、実引数から実中心と捕捉を得る。普通の状態の包含と、由来によって許された source 行の包含は別々。出力の等式が通常状態で真というだけでは、前段の読みの支持に使えない。 `current_heads` で、その読みに今の状態でも支持があることを示した。
- `WitnessNode334.Generation` は、選定前に独立に用意できる実 source と捕捉名、実 `compileBody` の結果、実順序の子需要、固定出力先への同じ論理名の通常 receipt を持つ。`Frame`、`Meaning`、`Evidence` は仮定しない。`Witness` には今の候補の独立な選定を足す。`Generation.frame` はこの入力だけから普通の読み・子・出力を導き、`Witness.ties_in_current` は I-58 の共有 binder の実中心等式が現在のどのモデルにも成り立つことを保証する。
- `GeneralDeclarativeWitnessClassify334.dictionary_sound`。任意の通常状態・支持表・待ち観測について、checked な registry、解釈 coverage、宣言済みの根需要を仮定する。証人つき `Classify` が selected 辞書を返すなら、**現在の任意のモデル**でその辞書の `Evidence` が成り立つ。根、実順序の where 子、全子の固定 output に、同じ一つのモデルを再帰的に使う。旧 Local との同値、モデルの存在、raw solver の到達可能性、停止を仮定しない。C332 の実二子に対し、inline の根・named の子、三つの実コンパイル結果を組み合わせて、実モデルを持つ辞書を確かめた（`WitnessFixture334.nonvacuous`）。
- 新 `Rule` の非選定側は既存の非生成分岐、I-59 の明示的な根 K2、独立に選べた候補だが現状態の実読みがない場合の保留。receipt や I-58 の等式を単に見つけられなかった場合を、今回勝手に保留または拒否にしていない。`WitnessVerdict334.verdict_functional` は、同じ現在状態の導出は保留・拒否・曖昧・選定の別と選定時の宣言 ID に関して一致することを示す。選定の二つの導出で異なりうるのは子需要列だけ（`only_lists_can_differ`）。許された名前配置の一意性や診断の全域性は未主張。

## 旧 Local との対応：到達可能状態での逆向き 1 群

- `WitnessCorrespond334.classify_to_old`。新たな証人つき成功から、具体的 `C331.candidates / Local59 / Staged` の**同じ節点 ID、同じ実子と順序、同じ診断木及び辞書**を作れる。`classify_from_old` は旧選定の各節点に独立の `Generation` があるときの条件付き逆向き。古い `Staged` だけからこの前提は得られない。
- **無条件の逆は抽象的な通常状態で偽**。`WitnessCut334.separating_state / no_new_dictionary / not_every_old_readback`。両端の record は別々に認可された支持を持ち、通常状態は実モデルを持つ。実コンパイラが固定出力 `5=3` を発行した ordinary receipt もある。だが中心名 1 の record 行は未完了の owner 100 由来のみ。支持されたエイリアスを別名まで辿っても得られず、named・inline・承認済み射影のすべてが使えない。旧は selected、新は pending で、旧へ合わせるため新選定を広げていない。この状態を raw solver が実際に返すことは未証明。
- `WitnessCompletion334.exactly_completed / pending_iff_incomplete`。通常の等式、区間、由来表、実モデルを一切変えず、完了述語だけを任意に切り替えたとき、owner 100 が完了した場合に限り、新選定が同じ宣言と子列で成立する。無関係な完了では保留を解除しない。完了後は元の record 行を読み、同じ固定出力先で実コンパイルして実モデルで辞書の根拠を得た。残りの 1 群は、この種の未支持中心を actual successful-stop から除ける条件と、訪れた真の選定が持つ receipt を備えた到達可能状態での逆向き。任意状態の同値を目標にしない。

## (2) 成功停止を前提とする部分正当性：残り 2 群

- `WitnessStopped334.selected_iff_retained`。有限の成功診断木を再生するのに、木の外の旧選定すべてに観測完全性を仮定する必要はない。訪れた各節点の旧 frontier、独立の普通の `Generation`、同じ順序の木で十分であり、逆に証人つき成功木からその有限記録が得られる。`selected_receipt` は全く同じ診断木・辞書と同じ任意の現行モデルでの `Evidence` を返す。
- `WitnessReobserve334.successful_reobserve`。ordinary の成長と支持が区別され、今の独立な選定が確認できれば、**節点ごとに違う過去の発行状態**から、元の実捕捉・子要求順・固定出力先のまま再生できる。C332 の root/child1/child2 をそれぞれ違う通常状態から読み、実際の二子と実モデルを照合した。 `WitnessRowProjection334.Embeds / actual_selected` は、完了述語の単調性や古い由来の恒久保持を一律に仮定せず、必要な普通の行が**今の真正な由来表で読める**場合に同じ保存を行う。無関係な完了が失われても読みを保持できる例と、中心そのものの唯一の由来が失われると同じ通常状態でも射影できない例を検証した。
- `WitnessReadout334.replay_exact / selected_from_replay` は、支持付きの実入力から、返された declaration key・全引数・順序・実中心・論理出力先が実コンパイラ出力と文字どおり同じことを検査する。C332 の並べ替え、出力先のすり替え、中心のすり替え、別 key を拒む実回帰を確認した。検査だけで現在の支持や receipt を作れるとはしていない。
- **順序の実差を確認**。raw の `GeneralDictionaryEmissionPlans.children` は既存 clause ID による正準順、ordinary の `compileBody` は入力宣言順。checked な C332 二子宣言を逆にすると、同じ role の子の固定 target 順が `[5,10]` から `[10,5]` に変わる。この例では両方の実三つ組を含む子そのものが逆順になり、入力の正準化で元に戻った。一般 raw 射影の順序・名前保存はこの実証と別。
- **残り A**: 任意の実 solver 成功停止の root/current state/各 occurrence から、現在の支持付き実読みに基づく普通の発行記録と同じ順序の子を得ること。raw `Stable` はそれを直接返さない。 **残り B**: 射影を使い、実 solver の返した診断木（非成功な下位診断も含む）、辞書・固定出力を、raw と普通の Models の対応込みで結ぶこと。今回閉じた有限 replay は B の利用側であり、A や B の実 solver 仮定を閉じてはいない。切れ目と既存の raw lemma 名は `notes/design/2026-11-22-c334-i60-success-projection.md`。停止性は扱わない。

## 質問

`notes/questions/2026-11-22-cycle334-record-center-withheld.md`。Yulang の模式例付き。案 1 は独立支持が戻るまで遅延、案 2 は支持が十分な場合だけの独立な record 射影。どちらも新たな言語受理規則として実装していない。

## 検証と公開

Lean 4.35.0。16 新モジュールの focused Lake `--wfail`、9 本の独立監査（`Audit/Cycle334*.lean`、凍結 Audit は不使用）、追加 Lean ファイルの trust 0、固定 pin から再取得した 25 proof/audit ファイルを exact bytes で照合して trust 0 で再検証。今回の 16 モジュールのキャッシュを使わない別ライブラリも作り直し、その新しい objects から 9 本の監査と個別回帰を通した（過去モジュールの cache は再利用）。121 個の定理を個別公理照合（`propext`、`Classical.choice`、`Quot.sound` のみ）。scoped gate は 65,255 宣言、宣言境界の依存チェックは 437 定数・5,740 依存。I-57 対応 diff-only、statement index、別置き回帰と raw/ordinary の順序境界（別置き trust 0、5 定理の公理照合）の記録は `notes/verification/cycle334/`。全 repo の Lake / Rust のビルド・実行、利用枠の残量は未確認。

凍結の `lean/Audit.lean` と `lean/README.md` は一切書き込まず、元と同じ SHA を確認。巨大な `lean/Yulang.lean` は全 bytes の Git digest を確認してこのサイクルの import だけを同じ変更に追記。公開は開始時の `work/dots-main` からの cumulative tree 差分と、個別公開後の変更パスの exact bytes を照合した。変更は合計 74 パス（証明と監査・barrel、設計と質問、heartbeat、検証ログ、今回の報告）。既存の実装・spec・指示・build config に変更なし。

## 次に

`Retained` の必要な source/current occurrence 記録を、まず実に到達した root と生成済み子の小さい断片から得る。既存の raw `GeneralNominalVersionedMixedStableLaws235.install_committed` は actual `Installable` が別にあれば、生成済み occurrence の現停止状態から同じ発行の意味と実子 edge を返す。`StableEvidence235.certificate` は同じモデルの現行 physical frame と出力を与える。ここを出発点に、まだ未接続の通常 source origin・現在の読み・同じ固定名の射影を作り、`Installable` を停止だけから仮定しない。通常等式の再生は `replay_exact`、過去出力が現在の独立支持で使えるかは `Embeds` と全く同じ論理名の current receipt で確認する。実 solver の受理を変えず、I-60 の old/new 問いと (2) の raw Models/診断投影を先に解消する。
