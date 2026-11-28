# cycle 487: G05Goal と全可視候補の署名付き報告

道具: モデル不明、Lean 4.35.0; 委譲: なし。
使用量: 不明。

## I-100 の方針と進んだ部分

`G05Goal : Prop` を宣言し、証明も公理化もしていない。全可視候補を同じ State と元 registry ordinal で扱い、各元引数の独立な実訪問を報告して、真の K2 があれば元順の全 hit を返す。K2 がない場合には rigid match / definitive mismatch / unresolved を別の印として次相へ渡す。辞書を選ぶ処理や曖昧性の最終決定はこの入口にない。許可の正確さと prefix 整合性は `G05ExactVisitInputs487` に名前つきで受ける。既存の局所意味と有限 checker の保存・反映は `G05ExactLocalProtocol487`、全 FitsFull における証拠は別の仮定。G04Entry、I-65 固定声明、旧合格の意味は変更しない。

- 任意の old State・旧位置表・関係について、独立に安全で guarded な元要求根を同じ座標・同じ列で構成し、既存 root checker に戻す。二つの元引数が同じ座標でも二件のまま。欠落・循環の root を局所安全と見なさない。
- 各元候補・元引数について、許された proper prefix のみを次へ開く有限探索を実装。旧 hop reader の前へ prefix check を動かしても、順序・重複・none を含め元の scoped 計算と完全に同じ。部分グラフの検証には従来どおり既存 checkpoint の全 guard が要る。明示許可表では、同じ候補 ordinal・引数・元構文・旧位置で先祖がすべて載るかを検査し、欠けた表を none にする。表や幾何だけから source prior を発行しない。
- 任意の可視候補の成功 tape で、許可 Bool と独立な Allowed が同値なら、候補ごとのキーの membership は元引数の実訪問と、真の符号はその訪問の最小型商での循環と一致。他の候補番号・元引数・元位置へ使い回さない。
- `checkFlatWithG05Tag487` は旧 flat タグの全入力の Bool を保持し、report / witness の交差を拒否。新タグでは根、元候補の順序、既存符号付き tape と実訪問、局所 token で読めた分類、同じ優先結果を照合する。局所 token が未読・欠落なら mismatch にせず none。
- `new_g05_tag_is_sound_for_exact_prior_visits_and_the_supplied_local_meaning487`: 任意の元 State・許可・局所 checker に対し、上の独立な正確性とモデル前提のもと、新タグ合格なら同じ元根、同じ全候補の独立な正確報告、および全 FitsFull の証拠を返す。 `g05_canonical_exact_report_reifies_under_the_named_visit_and_local_protocols487`: さらに各実候補の arity 一致と報告の訪問列が生成器の正準リストと同じなら、独立な正確報告を通す有限 witness が存在。
- 実テストは既存 compiler の実 State、GD、原位置から開始。可視順の変更で結果は `.recursive [1,3]` から `.recursive [0,3]` に元番号だけが変わり、K2 優先は同じ。先祖を欠く深さ二の許可表と、未訪問の可能サイトの循環を分けた。新タグでは rigid match・definitive mismatch・unresolved を同時に保持し、別の許可で真の二つの K2 を先に返す。候補一件の欠落、偽の優先結果、誤った・足りない局所証拠は通らない。一般の compiler の局所照合ではなく、明示した有限局所テストを用いた。

## 残り、境界

`G05Goal` 全体、G04Entry、一般の matcher / defer は未完。残り 20 / 24、G05 の期限は cycle 492。独立報告の訪問条件は membership だが、現実装は順序・重複込みの正準リストを要求する。空でない観測列を二重にした報告は独立の正確性を保つのに、現 canonical checker ではどの witness でも拒むことを証明。次は元 ordinal と分類を維持したまま訪問キーの membership を照合し、任意の独立正確報告へ有限 witness を運ぶ。局所型付けから許可を作る作業に戻らない。質問ノートなし、言語の意味判断なし。旧 Yulang2 の実機は再実行していない。

## I-100: 旧入口の削除明細

新たな削除 0、本周で削除した宣言 0、import の移動 0。対照は [18 旧入口の再照合](../design/dots-cycle-487-i100-old-entries.md)。現在の権威の Lean ソース 10,732 パスを blob 一致で再走査し、全 18 に集約以外の production の直接 import と個別 Audit を確認した。したがって今回の条件内に適格な旧入口は無し。C486 の既公開 `lean/Audit/Cycle410I74RootEscape.lean` の一件を再削除として数えない。I-100 はその試行を受け取ったが、当周の差分は新規の削除を含まない。

## 検証と公開

Lean 4.35.0。前半の exact 14 production・15 Audit を個別に `lean --trust=0 -DwarningAsError=true`、続いて G05Goal の型と監査、後半の exact 9 production・10 Audit と新規全 production を同時 import する小さな集約を厳格確認。全 24 production と独立 26 Audit。隔離した Lake の全新規 Audit 対象のみの `lake --no-cache build --wfail +Audit.…` は 27 jobs、exit 0。監査の出力 77 件は `propext / Classical.choice / Quot.sound` の標準集合のみ。実例は kernel 判定。リポジトリ全体の Lake build・`verify-lean.sh`・旧実機は未実施。広いローカル再検査の試行は exit 137 だったが、完了済みの前半・型確認と、絞り直した後半はすべて exit 0。前半直接ログ sha256 `d29f2c312b7dc30c456bfd0f6620d9b7fdb42c751d87470fe62aea995355754c`、後半直接ログ `6c729abdce5e72e6ab99a375117a2d423f1a6399745e7556cef925fa3710ddc5`、全新規重点 Lake ログ `fdf0ca931d35719a236b92426289b1a0d72a4b2e049284a6d5c7042859e2c276`。禁止構成なし、既存 Lean は集約 import の 24 行追記のみ。

開始 2026-11-28T10:30:32.411Z。開始心拍 `5ffa98bd2b1c3717948b63a1653d0694ca98e556`、+10 `650293d7e4b75b951eabef2408137a7b2b4cd553`。+20 の直前に統合先が `d12fff985c2aef3ef298b181251462f8f03c4e37` から `dc51fb0613f5df358f1ff4cc86a39dff22981a8b` へ inbox のみ先行したため、書き込みを中断して I-100 を取り込み、親と inbox blob `5dbffec4b4d8b9b6664230cb5f7773b9b9d71301` を一致確認した心拍 `47b5a998fb1c4422c99978df42b598e7752d7c98`。I-100 後の最初のコード公開 `7f0ee44f2311437aa036a2b176993f4da1c77022` は目標宣言を含む。+30 `ebadd5229bc1cc73ca1d876fb7b42fb72cbf21f0`（18 入口の明細）、+40 `913fb58ff926116582cecd3ee6ce54512bdab3de`。+40 Lean tree `b15eebdf01d87b1c5b62301fddc9eaee731fe9d5` と該当全 blob の内容を読み戻し、前周最終との差分はこの時点で 56 パス（C487 の追加 53、集約・心拍・監督の inbox の更新 3）、新規削除なし。最終はこの Lean tree のまま報告と完了心拍だけを加える。
