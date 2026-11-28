# cycle 488: G05 の観測表記と元要求の全範囲

道具: モデル不明、Lean 4.35.0; 委譲: なし。
使用量: 不明。

## I-100 の G05Goal のうち今周で検証した内容

- `checkFlatWithDemandScopedG05Tag488` は元要求の座標が空か非空かで分け、どちらでも旧 flat tag の Bool を全入力で維持する。report / witness の tag が交差したら false。新 tag は元 root checker と既存の signed tape で実際の要求根、全実可視候補およびその元の順序を照合する。
- 変えられるのは **報告上の観測キーの列**の表記だけ。各候補のキーについて正準な実訪問と双方向の所属を、元候補 ordinal・分類と一緒に検査する。順序と同一キーの重複は許すが、キーの欠落・別引数のキー・候補順の入れ替えを許さない。witness の経路と原順には緩和なし。候補の自己申告から訪問の範囲は作らない。
- `verified_g05_report_has_exact_original_coordinates_and_evidence_for_all_fitting_models488`: 任意の元問題と座標について `G05ExactVisitInputs487`、`G05ExactLocalProtocol487`、全 FitsFull での局所意味の証拠を受ける。成功なら同じ root 座標、独立に正確な全候補の報告と同じ State の全 FitsFull の証拠が得られる。`independently_exact_g05_reports_reify_without_an_observation_order_or_arity_assumption488`: 同じ独立訪問・局所 protocol の下、任意の独立正確報告に対し、入力 root がその順のまま通る有限 witness が存在する。観測列の正準順と追加の arity 仮定は要らない。
- 非空では実際の元引数 0 の準備済み情報から全候補の arity 一致を導く。空の場合は元候補に一件ずつ空の正準経路を作り、既存 reader で照合する。訪問 K2 は独立にも無いが、局所 token の欠落を不一致とも安全な報告とも扱わない。
- `original_root_read_back_is_sound_independently_of_the_prior_and_local_protocols488` と `g05_new_tag_cannot_drop_a_visible_candidate_a_tape_packet_or_a_local_token_slot488`: 独立な prior や局所意味の前提を付けなくても、新 tag の受理は、元要求の根の座標・順・guard と全可視候補の個数・元 ordinal・全 token 枠を保持する。
- `every_previously_accepted_canonical_g05_report_still_accepts_the_same_wire488`: C487 の canonical G05 がすでに通した report / wire は、新タグでも同じ入力のまま通る。引数あり・なしの両方で、古い成功を捨てずに観測表記を広げた。
- 独立局所意味が single-valued なら別の正確報告は観測表記以外で一致する。同じ独立意味を表す別の codec には、同じ report を通す **ある有限 witness** を移送できる。同じ wire の Bool 一致は主張しない。
- `a_real_original_k2_cycle_preempts_every_next_phase_on_a_verified_g05_report488`: 上の独立訪問と局所 protocol の下、本当に訪問された K2 があれば成功報告はその元 ordinal の全非空リストを返し、任意の次段 callback には進まない。K2 が無ければ検証済みの局所印の列をそのまま渡す。不検証は `notReplayed`。辞書選択と曖昧性の意味規則は実装していない。

## 実例の対照

- 同じ実元要求に二つの異なる深さの観測がある例で、報告の順序入れ替えは true、旧 canonical report checker と witness 側の経路反転は false。二重表記は true、欠落・別引数のキー・候補の入れ替えは false。
- 引数ゼロの実 `Problem`、準備済み GD、具体的な fitting model、独立局所規則とその有限 protocol を構成。rigid match・definitive mismatch・未確定を元可視列で保持し、局所証拠の省略・別候補の tape・偽の K2・非空要求への空座標の代用は false。
- 四実可視候補の別例で真の K2、二つの rigid match、未確定一つを同時に検証。独立 prior、独立局所規則への有限 protocol、具体的な fitting model も対象の Lean にある。実 registry の入替後も K2 優先は維持し、元 ordinal は 1 から 3 に移った。K2 が無い対照では未確定を含む印を全件元順に渡した。

## 残りと削除

`G05Goal` の定義は変更せず、その名前の証明宣言は追加していない。今回の健全性・有限再現は I-100 の明示した独立入力を前提とする。一般の compiler からその prior / matcher / local evidence を得たとは言わない。G04・旧 flat 実装・最終曖昧性や辞書選択は変更なし。I-100 の期限は C492。新しい質問ノートなし。

I-100 の 18 旧入口は、権威の Lean tree が C487 の [逆依存明細](../design/dots-cycle-487-i100-old-entries.md) と同一で、直接 production importer と個別 Audit が残った。例として `WhereSamePhaseSource454` は `InternalReport` と `exactReport` を使用し、`FlatDispatch481` は raw-grouped の既存判定を直接呼ぶ。新たな削除 0、消した宣言 0、import の移動 0。C486 で受領済みの Audit 重複削除を再計上しない。

## 検証と公開

Lean 4.35.0。新規 production 14・独立 Audit 16 を `lean --trust=0 -DwarningAsError=true` で厳格検査し、新規全 production の焦点集約も通った。隔離した対象のみの `lake --no-cache build --wfail +Audit.…` を三段に実行して 13 / 4 / 2 jobs、各 exit 0。A 38、B 13、C 3、合計 54 の監査出力は `propext / Classical.choice / Quot.sound` の標準集合のみ。kernel の具体例は最初の default heartbeat で深い例が上限に当たったが、当該テストの限度だけを調整し、最終の厳格ビルドと監査で全例が通過した。

直接ログ sha256 は A `9f433fbfcef6920556ac1adacf93f96c3418dd96dfb720743aface90cf23d119`、B `ae82bbf310c805a759c40a4a46ecce218ca58893da1fc47b8bf3becc37123b2c`、C `a40494317c6840461e1b573f68301d9e5a6517f221ec1425ef35c588d95f8c6f`。対象 Lake ログは A `429fa3a0ba99083cc3ba60962da8895586a5d24453c1bd41292f3380206f7081`、B `fea35a9d64a143171b597e7a8cff56f134746b45645d01baf7786d10e8656a6b`、C `9be1d6488578eb5f71b1554fdf18519b4be71ca1ef19e42f61a9e96e1f50288f`。

関連する repository ソースの import 閉包 4,628 の Git blob を、現在の権威・公開済み差分・本周の exact パッチと独立に照合し、欠落 0、未解決 import 0。閉包照合ログ sha256 `02f74339cda6a20fafa6f58b22f0796112c50b36ae785841ac505173662fe4e8`。これは依存ソースの一致で、全依存の再ビルドを意味しない。リポジトリ全体の Lake build・`verify-lean.sh`・Yulang2 実機は実施していない。禁止構成なし、既存 Lean は集約 import の 14 行追記のみ、新規 Audit から既存 Audit への import なし。

実開始 2026-11-28T11:33:22.168Z UTC。権威 `dc51fb0613f5df358f1ff4cc86a39dff22981a8b`（I-100 inbox `5dbffec4b4d8b9b6664230cb5f7773b9b9d71301`）と C487 完了を読み直した。開始心拍 `81458330daa7ef9bab5a3de8f07c8ffc84b02287`、+10 `f888e2633d0385e925f2ec711d74bf109abc2dde`。+20 `cab85286c550f4768fa78fdd49411e6cbe172fdb`（観測表記・空／非空、Lean tree `39806e1cec0fede2cbebc63bf9c307db0a6a4650`）、+30 `b36c8b90b526301899beb3c17e78c379b62666e0`（全候補・token と K2 優先、Lean tree `1b8710bde2c015dd1da60ab04a472fec87788abd`）、+40 `31acf062e92fb94acfca16a466f3e8610ca4cd16`（C487 合格の保存、確定 Lean tree `53c9e2ce34ef9db2fb5bf5676b646a39aecd2db6`）。前周最終に対し凍結時点は 34 パス、追加 32、変更は集約 import と心拍だけ。Lean 31 パスの Git blob をローカルと公開側で照合し一致、旧 `G05Goal`、`G04Entry`、`FlatDispatch481`、`Audit.lean` と inbox は同じ blob。公開先は `work/dots-main` のみ。最終は確定 Lean tree のまま報告と完了心拍だけを加える。
