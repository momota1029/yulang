# Yulang dot cycle 339 (2026-11-22)

開始 06:33:50 UTC。統合側の指示元は `integration/m1-final` の `9bb8eeb2ebb9e949445ad1e9c4dda39a8a82477a`（開始・終了前に standing orders、inbox、roles/inference spec を再読）。I‑61、I‑58、I‑57 を適用。実装対象と監査は `work/dots-main` のみ。直前の完了版は `819fe1ea2e9a98b59072d977f644f7bf96e4970c`。検証対象の固定証明スナップショット: `d33c4777d1603e9cda83ecb849a68f6389a7f7de`。

## (4) 端点と実際の出力

- `GeneralDeclarativeOpenReceipt339`: 以前の根拠つき open-prefix の **実際の名前つき残余 receipt** を既存の候補・既存の順序にある一行へ結び付ける。残余の削除と下端・上端の意味を、独立に読まれた端点と任意の同じ適合モデルで比較する。中心の RHS を仮定、合成、上下端で置換しない。
- `OpenExec339` / `OpenTraversal339`: 入力の順序で各本物の射影を実行し、既存モデルを具体的に拡張する。有限の入れ子を処理し、保護名・既存の sidecar を保存。 `OpenSelected339.output` は既存 `Selected` の出力、残余 receipt、子の宣言可能性を同じモデルに載せる。
- `OpenFixtureWitness339.actual_open_dictionary` では中心に RHS がなく、裏付けなしの tail 名 4 を持つ可視の選択元がある。一方、独立の既存 canonical RHS は本当に根拠がある。その支えだけで選択・出力し、実際の子は `(19,14,20)`、子の固定出力先は 5、文字通りの親・子の等式は `6=11` と `5=14`。残余の中心 11・17 は実際に exactEmpty となる充足モデルが存在し、6 が実際の削除結果と同値で、同じモデルに再帰 Evidence がある。未知の RHS を読み取ったのではない。`OpenReadiness339.exact_gap` / `OpenUnresolved339.not_settled_read` は、本当に未解決の別の原始状態を区別する。旧 `Elected` はそこでも立つが、C336 の正規化 `Read` は立たず、同じ記録で空の残余と非空の残余の両方の適合モデルがある。旧 Elected を十分な readiness にしてはならない。§6.3 の genuinely unresolved ケースを拒否や新たな優先順位に変えていない。
- `MixedSources339.compile` / `MixedInputs339.input_exact` は支持元から有限入れ子 record と既存で認められた葉（variant、pair、invariant nominal）へ進み、実際の route、根拠、順序、変数名を保存する。`MixedLeafGrowth339` は既存の実際の Trace/TraceArgs を後段の支持済み状態に持ち上げ、invariant nominal は各引数を .actual、pair は各端点の mode で観測する。join は Trace 自体にはあるが現行 `Shape` にはない。これは分類断片の境界であり、join 候補の一般的な否定、新しい K2 優先規則、または証明可能性の否定ではない。
- `MixedCompiler339.selected_sound` / `MixedDictionary339.dictionary_sound` は実際に構成された支持つき観測・選択・出力順を入力とし、同じモデルでノードと子を検証する。実例は record 7 → record 9 → variant 8 → 捕捉 `(3,19,3)`、実際に発行する子 `(20,19,21)`、出力先 5、等式 `6=11` と `5=19`。元の中心も variant の中心も RHS は読まない。I‑58 は選択後に実際の中心から適用する。全ての open 判定で任意の I‑61 raw 状態から observation が得られる、とまでは言わない。

## (2) 既に到達した状態の部分正当性

- `StoppedOutput339` / `StoppedOrder339` / `StoppedOrigins339`: 実際の raw `Steps` で保持された書き手をたどり、現在の compiled body と現在の `Ready` に対して、重複を残した alias-class 要求順に文字通りの固定 target を出す。明示 RHS は実際の binder、既存 default は実際の input centers を参照する。任意の raw 適合モデルで行を真に写す。設置されたことだけでは source として使用可能にならず、元の支持または対応する書き手の完了証拠が必要。
- `StoppedStructural339` / `StoppedLower339`: 認識できる record/pair/variant/union 等の構造 head で正規降下のモデル同値を示し、既存の認識成功例では同じ結果を返す。その断片でも実際の順序と target を保つ。 `StoppedFixture339.installed_valid` は C238 の実際の install で、固定 4 の RHS と実際の書き手を認証する。元が成功停止例だとは主張しない。幅つき record は実際の slot 2 で読める一方、同じ fixture 全体をまだ降下できない。補助検査では slot 0 の非点名目パラメータ (4,2) を点 descriptor encoder が実際に拒否する。未対応 slot や未設置の葉をこの定理で補ったことにはならない。

- 別置き `RawLeafFeasible339.lean` の補助定理では、実際の raw `Local .selected k []` と独立な `ChosenHead` の存在証明から、現在の論理 frame・実際の出力先・要求順を満たす **ある** モデルを回収する。設置効果への所属は不要。ただし任意に渡された同一モデルへの移送も、head そのものの存在もこの補助定理では閉じない。

## 残件の数え方

- (4) I‑60 の宣言的な証人つき分類に関する未完 **0**。I‑61 追加の分類から同一モデル出力への一般的な適用域の拡張は **1 グループ**（正規化して現行断片に入らない混在形、特に join や現在の独立な証人で扱えない open ケース。新たな言語規則は仮定しない）。旧 reachable `Local59/Staged` からの対応は別に **1 グループ**。
- (2) **2 グループ**。(A) 全成功停止状態の現在行・一般名目を含む正規降下、未設置葉と現在の出所の全面的な回収。(B) 同じモデルで、正確な診断・辞書・順序・実際の出力先までを全到達ケースで一体にする。ここでは (A) に現在認識できる設置出力と構造 head で進展。停止性・全 Rust 実装の実行や検証は対象外。

## 検証と範囲

- 公式 Lean 4.35.0 の復元済みツールチェーン。今回追加の 29 モジュールを対象とした `lake build --wfail`、別置きの 8 監査、確定証明 pin の各ソース・監査を `lean --trust=0 -DwarningAsError=true`。独立 scoped closure: **77,303** 宣言、標準の `propext` / `Classical.choice` / `Quot.sound` のみ。個別 `#print axioms` は **81** 件（別置きの raw leaf 補助検査はさらに 3 件）。旧 C334 の元の定理ソースも同じ blob で trust 0 再検証。Open/Mixed 側の依存閉包は 595 根・2,276 宣言で選んだ raw ジャーナル・停止名前空間を参照しない（別の Raw/Stopped 結果は検査対象外）。詳細は `notes/verification/cycle339/`。
- `git diff --check`、凍結旧 Audit を行数照合から除いた既存ルールの diff-only 再検査、実ビルド対象の同時 import、個別ファイルの Git blob 照合。 `lean/Yulang.lean` は厳密に旧ファイル全文＋今回モジュール import のみ。I‑57 の `lean/Audit.lean` / `lean/README.md` は統合側・前周と同じ blob で不変。変更対象に出力切り詰めのマーカーがないことも確認。リポジトリ全体のビルドや Rust の実機確認はしていない。

完了報告の記録時刻: 2026-11-22T07:23:51Z（開始から 50.0 分。公開後の固定 ref 照合を続けた）。
