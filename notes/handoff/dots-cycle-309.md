# C309: 順序のある二つの実 child を同じモデルで証明

開始 2026-11-21 00:29:54 UTC（09:29:54 JST）。終了・正味経過は完了心拍。
C308 の完了は `0efd81e8c4e38ae34b798cac1475aa7830d45e06` で確認した。
統合 `faf6b87900b6c446461b1d5f9133467abbb7dee9` の standing orders と inbox を
開始・途中に再読し、内容は不変、ACTIVE / I-54 を確認した。今回は**健全性**
（受理された辞書が実際に証明できること）を主対象とした。
使用量枠は不明。Rust/Yulang2・CI・全体 Lean build は未実行。

## 1. 二子の正例を実 source から作った

- **固定した別の実 checked source**: nominal `List[Int]` を取る親が関連出力
  `(0,1)` を明示要求し、二つの異なる role に Int を渡す。source の where 句は
  意図的に ID の逆順。checked registry の実候補を通して親の一手を実行した結果、
  canonical 順に二つの別 occurrence が生成され、それぞれ leaf key 2 / 3 を選ぶ。
  C308 の棄却例の意味論は変更していない。
  `GeneralPositiveForkSource309.actual_initial`、
  `GeneralPositiveForkPlan309.ordered_children`、
  `GeneralPositiveForkInstall309.step / actual_low / actual_high`。
- **全モデルに対する一貫した証明**: 任意の (m) で `Models after m` なら、
  同じ (m) で親の出力の witness、左右の current Certificate と leaf Evidence、
  根の辞書 `.node 1 [.node 2 [], .node 3 []]` が同時に成立する。
  出力は default の仮定で覆わず、source の明示式だけが供給元で実際に
  `.variable 0` へコンパイルされることも確認した。
  `GeneralPositiveForkEvidence309.both_same_model`、
  `GeneralPositiveForkVerified309.only_explicit_body`。
- **payload の完全な照合**: 任意の (m) と任意の shape の payload について、
  妥当な同じ (m) における Evidence は、固定した三つの occurrence それぞれで
  正しい ordered payload と同値。入れ替え・子の重複・省略は不可。局所 frame を
  独立に逆にたどって証明し、辞書の key だけで同じ子と扱わない。
  `GeneralPositiveForkNodes309.exact_frame`、
  `GeneralPositiveForkPayload309.iff_expected / swapped_rejected / duplicated_rejected / truncated_rejected`。
- 実 proof-level resolver の木は `selected(1,[selected(2,[]),selected(3,[])])`。
  checked current EvidenceAt は子の証明が本当にそろう、非空の前提で成立する。
  それでも両葉には journal の `Discharged` がなく、親の `.output effect` を
  含む `Trusted` slice は存在しない。証拠と cache の信頼を混同していない。
  `GeneralPositiveForkCompiler309.exact_root_tree / nonvacuous`、
  `GeneralPositiveForkSettlement309.sound_without_settlement`。

## 2. 観測と据え付けの境界

- 実据え付け前から親は局所で選べ、関連出力と二つの子を含む親 Certificate まで
  立つ。しかし両子の occurrence が未登録なので（Int が未知だからではない）、
  両子は `pending`、任意 (m)・任意 payload で根の再帰 Evidence は立たない。
  実 Step の前後で全モデル集合は等しい。従って単にモデルの違いを判定したのではない。
  `GeneralPositiveForkBefore309.actual_boundary / initial_tree / wrong_phase_not_faithful`。
- raw の登録を確認する `readAt` は、据え付け前に子の row を返さない。
  この固定 initial からの任意の実経路の状態 (s)、全モデル (m)、燃料 (n)、
  任意 payload (d) について、検査成功と「(n≥2) かつ (d) に実 root Evidence」
  が同値。この fixture の到達相を閉じる補助定理は、この量化にだけ使った。
  一般 source の停止性は扱っていない。
  `GeneralPositiveForkCurrentRead309.actual_exact / initial_error / one_install_unlocks`。

## 3. 再利用できる健全性の部品（明示前提あり）

- 任意 registry・状態・row の順序付き子に対し、実 source の Checked / 到達性・
  exact current Frame・Committed と同一 full model の子証拠から親 Evidence を
  構成する。Stable、全停止、台帳の output settlement は不要。さらに、候補が
  safe かつ一意で出力併合に矛盾がない row と実モデルがあるなら局所選定を導く。
  `GeneralCommittedReadEvidence309.node / child_generated / sound`、
  `GeneralSelectedReadEvidence309.selected_checker`。
- 当該 reader の実生成 root から任意 payload を検査し、通ったなら、同じモデル
  の **全ノード**の実生成 root・current Certificate・明示出力・順序付き子を trace に
  回収できる。trace を辞書 Evidence に消去でき、任意の順序付きアドレスで表と
  payload の移動は同時に成功か失敗し、成功地点ではその子の証拠を抽出できる。
  trace と燃料（辞書の高さ以上）があれば検査を逆向きにも通す。
  `GeneralCommittedReadTrace309.verified`、
  `GeneralCommittedReadAddress309.address / subtrace`、
  `GeneralCommittedReadErasure309.evidence_at_address`、
  `GeneralCommittedReadExact309.certify_exact`。
- ordered checker は入れ替えと重複を、それぞれ子位置 0 と 1 の exact wrong-key
  として区別する。任意 reader について、各祖先の key・arity が一致し、
  先に並ぶ子がすべて成功した位置に初めて返す fault を、双方向で証明した。
  燃料不足で失敗しても妥当な同じ辞書・証拠はあり得る。
  `GeneralOrderedDictionaryCheck309.exact`、
  `GeneralOrderedDictionaryFault309.exact`、
  `GeneralPositiveForkVerified309.fuel_not_rejection`。
- rooted read footprint 内の行を保てば、範囲外の行が違っても collector・validator
  の結果と信用できる参照表からの根の証拠は保たれる。この例では必要な行は 0,1,2。
  結果 777 を返す余計な行 19 を足しても根は健全だが、その行自身の成功を
  source Evidence としては認められない。
  `GeneralOrderedDictionaryFootprint309.validate_agrees / run_agrees`、
  `GeneralSelectedReadScope309.checked_on_footprint`、
  `GeneralPositiveForkScope309.accepted_root_still_sound / cannot_infer_outside`。
- 固定した二型スロット 0/1 を保持すれば、任意の外側代入（全 row 値を含む）でも、
  親明示出力・左右・根の完全な同時証拠を復元できる。逆にこれらを保つ型支持は
  0 と 1 の両方を含まなければならない。
  `GeneralPositiveForkCertifiedTrace309.packed_trace`、
  `GeneralPositiveForkPackedMinimum309.minimum`。

## 範囲と次

一般の source について reader や Committed row が得られること、一般 B4 の
全健全性・完全性、一般停止性、Rust の動作は証明していない。次は停止証明ではなく、
親出力を子も読む where 分岐で、独立の候補存在証人を**同一全モデルの**現在 packet
と class/output 証拠へ移す。`SelectionRow` のこれらの前提を何から生成するかが残り。
[健全性の証明責務](../design/2026-11-21-cycle309-soundness-contract.md)。
仕様判断の質問はなし。既存の意味論・Rust・lake 設定は変更していない。

## 既存の B4 健全性への接続

`GeneralPositiveForkCurrentSoundness309.current` は root・low・high の全てで
既存の `Current` を構成する。実フレーム、一意の子対応、互換選択、全候補の
安全性、および同じ全モデルで成立する保持・現在クラス式を証明し、
`source_installable` へ渡す。三点すべてで既存の
`StableEvidence235.selected_node` による `EvidenceAt` を得て、
`nonvacuous_existing_bridge` では両葉をもつ実 payload まで復元した。
この後者は既存 API の求める安定性を使うが、停止性を新たな結論とせず、
別経路の `sound_without_settlement` と混同しない。一般の入力で
`InhabitedAvailable` が自動的に得られることは未証明。

## 検証と公開

中間固定ピン: `8cb55c8955f6b41cadd28c1c2ccc7df9f223f46b`（実 install）、
`50dc909f15a61f2f09833b4f5d776b188693e84e`（ordered Evidence）、
`b3469b01752ac91f94055fd7db40802e45f068db`（検査・証明住所・据付前反例）、
`ff5923a90382cd180e08f0d557b6192e56f67f9a`（証明 trace・正確な失敗・支持）。
書き込みは expected-head 非 force の `work/dots-main` のみ。

- 34 モジュールの対象 Lake build（警告もエラー扱い、2783 jobs）と
  一つずつの source `--trust=0 -DwarningAsError=true` は全件 exit 0。
  [Lake](../verification/cycle309/focused-lake.txt) /
  [全ソース](../verification/cycle309/focused-source.txt)。
- standalone audit 10 部すべて exit 0。334 固有宣言（374 件出力、27 件
  公理依存なし）。それ以外は `Classical.choice`, `Quot.sound`, `propext`
  のみ。[集計](../verification/cycle309/standalone-status.txt) /
  [監査 1](../verification/cycle309/audit-00.txt) /
  [監査 2](../verification/cycle309/audit-01.txt) /
  [監査 3](../verification/cycle309/audit-02.txt)。
- `tools/verify-lean.sh --no-build` は固定 baseline との diff-only PASS。
  [判定](../verification/cycle309/diff-status.txt) /
  [末尾ログ](../verification/cycle309/diff-06.txt)。
  [実行済み Lean probe 12 件](../verification/cycle309/executable-smoke.txt) /
  [入力](../verification/cycle309/executable-smoke-source.txt)。
- 最新 integration との差分は既存 C307 持ち込み分。新規対象非 barrel
  Lean 45 件の blob は作業の確認済み baseline と一致し、standing orders/inbox
  もバイト不変。[照合](../verification/cycle309/integration-readback.txt)。
- 固定コミットでの照合記録: [検証対象の readback](../verification/cycle309/readback-substantive.txt)。
  一般停止性および Rust 実装に関する検証の主張はない。

次の一般化では既存の `GuardReduction235.current` を再利用する。これは実
selected と frame から全代替安全性を導くので、残る主対象は
materialized、現在の compatible choice、そして相互に別の存在証人ではない
`InstallationModels` である。後者は `MixedCommon235.installation_models_iff`
により「ある同じ (m) で Models・Holds・Live」とまで絞れる。一方、
明示 reader ルートの `Committed` は同じ条件を全モデルに要求する。
存在条件と全称保証の違いを保存する。
