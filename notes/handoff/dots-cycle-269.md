# Cycle 269: 有限な弱振る舞いの正準分類と、意味的 K2 の有限証明

公称・実開始 **2026-11-19 08:30:00 UTC**。取りまとめ **2026-11-19T09:20:05Z**（50.08 分、55 分上限 09:25:00 UTC）。前回の確定公開 `b5def5385a43a0559c46a066a8e75d90c054d42e` と同一 tree から開始。integration は `1b113cfd93bd7ab89ccb1e4b29653dfd5f655775`、本周の開始・公開前に standing orders、inbox、ACTIVE、I-51〜53 と凍結を照合。書き込みは `work/dots-main` のみ。

## I-52：有限の後継挙動と、元の遷移との対応

1. **正準弱コード（健全性・完全性）**。 `GeneralRebaseBehavior269.code_finite` は、任意の registry、root、固定ライブ basis、具体 state について、現在の射影をラベルとし、各弱後続の正準コードを子とする実際に有限個のコードを与える。弱 Step は「有限な射影不変の旧遷移＋射影を真に変える旧1歩」。具体分岐が無限でも、射影の残り数が弱 Step ごとに減るため、有限の順序付き候補集合を用意して正準化できる。 `.advance_exact` はコードの各子が**同じ現在の具体代表**からの実弱後続に持ち上がり、すべての実弱後続のコードがその子にあると示す。 `GeneralRebaseBehaviorStutters269.exact_bisim` は、コードの等号が残りリストを保存する弱双模倣のうち最も粗いものに一致すると証明する（このラベルから rank を決められる）。具体 Plan 表を射影だけで復元する主張ではない。
2. **跡と終点（健全性・完全性・停止性）**。 `GeneralRebaseBehavior269.old_to_abstract` は任意の有限旧経路について strict の回数を保ったコード経路と最終射影を得る（末尾の stutter は最終**コード**まで保存するとは仮定しない）。 `.abstract_trace_old` は同じ具体代表からの旧経路へ戻す。 `.settle` は正しい初期コードを与えれば有限回で、すべての有限な旧後続に対して射影が不変な実終点に持ち上がる。選ぶ終点の一意性や合流性、旧カーネルの全停止性は主張しない。
3. **旧反復の回帰と測度（停止性・補助）**。 `GeneralRebaseBehaviorStutters269.children_decline` は、射影が変わらない旧経路の後で、利用可能な正準後続コードが元の順序付き部分列になると示す。 `GeneralRebaseChangedCode269.wellFounded` は、射影の残り数と子コード数の辞書式測度で、同じコードの遷移を除いた旧1歩の存在的な像を整礎化する。この広い像の、同じ代表からの持ち上げは未証明。双方向の対応を証明したのは弱 Step の子関係。 `GeneralRebaseBehaviorRegression269.version239` と `.version240_mixed_observation` は、実239と240の旧反復が非停止のままで、十分遅い段階では射影だけでなく行動コード全体が一定になると証明（240は既存の混合カーネルへの消去）。コードが一定でも別経路の strict 出口がないとは限らない。
4. **限定実行（健全性・条件つき完全性）**。一般の正準コード抽出は実弱後続の存在を古典的に使い、未実装。 `GeneralRebaseRankOne269.sound` は残り0では入力なしで、残り1では弱後続がある／ないの認証済み1ビットだけで正準コードを計算する。残り1の肯定には同じ空ラベルに落ちる真の1証人で十分、否定に探索不成功は不可。 `GeneralRebaseBehaviorFixture269.listed_exit` は実238の据付けで空の後続コードを計算し、そのコードが元の具体開始状態の真の弱出口であることを確認。開始側の残り2における全列挙は未主張。 `GeneralRebaseKeyedBehavior269.run_sound` は別の実行経路で、供給された有限弱キーグラフの rank を機械検査・展開して、具体代表ごとの投影と持ち上げの独立契約の下で旧経路と弱終端を得る。rank 検査だけで契約が成立するとはしない。

## 意味論の独立証拠と V8 接続

5. **raw K2（健全性・構造部分の完全性）**。 `GeneralRebaseActualArguments269.actual_iff` は raw model があるとき、任意の実 nominal argument edge の添字を実 descriptor の有限 type 位置に制限する。モデルがなければ任意添字で全称条件が空真になるため、 `GeneralRebaseRawActualProbe269.fullNominal_sound` ではその場合を別扱いし、直接循環を捨てない。 `GeneralRebaseSlotInequalities269.prove_sound` は明示の変数間不等式・interval・同一 source 名のグラフで全モデル上の不等式を証明する。型引数 `[lo,hi]` に対して `target ≤ lo` と `hi ≤ target` は肯定、実モデルが `lo ≤ target` または `target ≤ hi` を否定した場合のみ当該位置の否定。 `GeneralRebaseNonpointK2Fixture269.true_nondirect` では、異なる endpoint slot の構成済 raw snapshot で、補助不等式回答がすべて不明でも、非点の実循環と直接循環でないことを検証。表層プログラム到達性は未主張。
6. **Versioned Origin（健全性・条件つき完全性）**。 `GeneralRebaseOriginCongruence269.edge_normal` は実 Origin 辺の任意の中間親を、全モデル同値を保って始点の head/projection に正規化。 `GeneralRebaseOriginQuotient269.complete_window` は、有限窓が全モデル観測同値まで閉じており root が表現されるとき、非空帰還を両方向に対応させる。構文上の完全列挙やゼロ長循環は不要。 `GeneralRebaseNominalOrigin269.exhaust` と `GeneralRebaseTypedNominalWindow269.edge_iff` は、full model がある実 nominal source slot の正 arity head は実 descriptor で決まり、型の辺候補は type 位置に限ると示す。 `GeneralRebaseNominalWindow269.check_sound` は各位置にグラフ上で強制される同値標的があるか有限チェックして窓閉包を証明。構成された初期 journal の回帰では、単一点の窓で構文的閉包が破れるのに意味的閉包と実 RootCycle が通り、別の row-only journal では full model が存在して全 equality 回答が不明でも非循環を計算。一般の構造型窓・すべての全モデル同値は未決定。
7. **SameInputs と実 V8（健全性・条件つき完全性）**。 `GeneralRebaseJournalInequalities269.prove_exact` は現在・source journal の不等式、interval、登録済み center の上下条件から有限の名前グラフを作る。入力名列を比較する `GeneralRebaseSameInputs269.probe_sound` は名前が違っても両方向に到達すれば実 SameInputs を証明する。否定は認証済みの片方向否定、探索失敗は保留。 `GeneralRebaseMergeJournal269.scan_iff` は関連する登録対で回答が既知のときのみ逆向きも保証する。初期 journal で中心名0/1が同値になる回帰は比較の実例であり、両サイトが登録済み・実 merge 成功は未主張。 `GeneralRebaseCompilerInputs269.run_sound` は raw、SameInputs、optional Origin 窓を実 V8 に接続。 `GeneralRebaseEnhancedPipeline269.actual_install` は実 compound-where の V8 選択、旧カーネルの据付け、据付け後モデルを再確認した。head・joint・novelty などの独立証明入力は残る。

## 検証・公開

- **38 新規ライブラリモジュール、315 固有の名前付き宣言**（定理数ではない）。Lean 4.35.0 の trust 0、警告エラー化で焦点ビルド、新規監査7本を個別に再実行して exit 0。標準公理のみ。 [再監査](../verification/cycle269/final-audit-recheck.txt) / [実例再確認](../verification/cycle269/final-fixture-recheck.txt) / [構成と個別ログ](../verification/cycle269/)。
- [integration 基準](../verification/cycle269/diff-gate.txt) と [前サイクル基準](../verification/cycle269/prior-cycle-diff-gate.txt) の `tools/verify-lean.sh --no-build` は終了コード0、`git diff --check` も成功。I-51の独立監査 import と I-53の全 barrel 追記を照合。旧 Lean は barrel への追記だけ。凍結の spec・plan・Audit.lean・README は無変更。全体 `lake build --wfail`、全体公理ゲート、CI、Yulang実機は未実施。
- 検証済み途中 tree は `a9ed0450`、`3bdde748`、`73b28a27`、`377dc81f`、`e09bccc1`、`749295ea`、`3223de3d`。開始および10分刻みの心拍は概ね予定どおり（20分回は11月19日 08:51 UTC 台に照合）。照合前の expected-head 入力の転記誤りは不一致で停止したため実変更なし。取得値で再試行・照合済み。使用枠は不明。前周から 81 ファイル。次枠先取りなし。

## Yulang2 との照合・残り

既存 `notes/audit/x-oracle.md` の K2 回帰（表層実機で構造再帰を再現できなかった記録を受理一致とは数えない）と 238/239/240 の既存埋込みを参照し、Lean で検証。Yulang2 実機の新規確認なし。今周で設計意味を変える必要はなく、新しい質問ノートなし。M1 健全性・完全性・主型性の完了ではない。

次は (1) 構造型と mixed-time packet を含む一般の意味問い合わせに、検査可能な正負の証人、または明確な保留を供給する、(2) 任意の到達 state から実用的な有限弱キーを抽出し、同じ代表への持ち上げを検証する、(3) その上で Permitted、Frame/EvidenceNode と終端診断を接続する。詳細は [設計ノート](../design/2026-11-19-cycle269-semantic-origin-support.md)。
