# I-60 後の成功停止の射影境界

## 別々の三つの結論

- **新しい宣言的 (4)**: checked/covered な registry、宣言済みの根、任意の通常状態と与えられた支持表で、証人つき `Classify ... (.selected dictionary)` から任意の同一現行モデルで `Evidence`。しかも選んだ実出現の共有等式、全順序を保つ子需要、固定出力先の意味が入る。全モデルの存在や旧分類・solver は仮定しない。
- **旧宣言分類との対応**: 新の成功木から旧 `Local59` の同じ成功木を作れる。逆は任意通常状態では偽。旧 `Staged` の実際の compiler 計算が合っても、その中心を現時点で読めない場合がある。後続の抽象的な環境に移しても、実際の supporting row が回復したときだけ同じ receipt の再利用が可能。到達可能状態に制限した比較は別問。
- **B4 (2)**: `Retained` は実際に訪れた節点だけの推論材料であり、executor の成功を同値とする命題ではない。`Journal` は独立な普通の保存記録（raw でない）の既知の保存則の利用側。通常の行の成長と、旧時点の各使用行が今も実際の由来を持ち利用できることを分離する。current election は古い同じ結果から引き継がず、再度与える。

## 成功した solver の出力から何を証明するか

1. **現在状態・由来・読んだ節点の射影**。既存の raw 側の concrete boundary は `GeneralNominalVersionedMixedBoundary234`。その `closure` は根と実際に生成された子の raw stability を与え、`stepModels` は同一 raw モデルの逆方向保存を与える。しかしその返す `Stable` は、(a) 選ばれた発行の現在の version/owner と support の観測、(b) 終了時に使える record/RHS と本物の center の読み、(c) 同じ論理名を使った実際の順序つき child list/fixed targets を含む `Generation`、をそのまま返さない。ここでは新しいステップや成功条件を作らず、完了 frontier の根/子を、別々の historical snapshots から成る有限 `Retained` または `Journal` に射影する命題を切り出す。何の由来かが不明な通常行や、同じモデルで真なだけの行では証明しない。`ReaderGrowth` は古い由来/完了を保つ場合の十分条件。`Embeds` は現在の本物の支持行だけの条件で、関係ない owner の完了解除は禁じない。

2. **停止時の返値と宣言的診断の一致**。現実の実行側が保持したキー・子の順序・論理名・出力先・診断木を `Retained` の同じ木に対応させる。既に戻った木に対して `replay_exact` は true iff 指定した普通の source/placement から実ファイルの `compileBody` が同じ key と全需要を生成したことを検査する。その後の `selected_receipt` は同じ結果の分類と任意の同一 **宣言的** モデルでの辞書の根拠を与える。raw `Models` とこの `Models` の対応、実際の出力から各節点の report/ordinary receipt を作れること、成功停止に現れる非成功子の診断保存は未証明。全体の (2) に停止性は不要で、ここでも証明しない。

I-60 の判断自体を物理 solver の受理条件として移植したり、C334 の記録付き fixture を Rust または実 Sat の反例として扱ったりしない。

補足: `verdict_functional` により、同じ現行支持状態における二つの witnessed frontier は、保留・拒否・曖昧・選定の種別で一致し、選定なら宣言 ID も一致する。これは既存の I-59 拒否と I-60 の「現在の読む根拠なし」を尊重した結果。残る同値比較は、異なるが合法な placement が出す同一性でない子需要についてであり、種別の不一致を埋めるために新しい優先規則を足してはいない。

### 実子の順序を射影する際の注意（Lean で小さい実差を確認）

`GeneralDictionaryReadback.Payload` は `CommonRoleOutermostResolver.Dictionary` の別名なので、key だけの辞書型変換は不要。失うのは occurrence ごとの需要と意味である。raw 側は `GeneralNominalVersionedFrame231.children` → `GeneralDictionaryEmissionPlans.children` → `canonicalEmit` を通り、既存の一意な clause ID で正準化する。一方、今の普通の `compileBody` は供給された `impl.requirements` の順を使う。C332 の checked な二子宣言の要求順だけを逆にすると、普通の実コンパイルの出力先列は `[5,10]` から `[10,5]` に変わり、正準化した入力は元に戻る（`notes/verification/cycle334/ordered-raw-cut.lean`）。子は同じ role なので、role/key の集合で照合しては検出できない。割当名も入力順で変わりうるため、すべての論理名の単なる置換と断言しない。実射影では raw が使った正準宣言を同じ順と名前で引き渡せる条件か、仕様に沿った変換を先に証明する。証人つき側の受理や、新しい順序の既定をここで変更しない。
