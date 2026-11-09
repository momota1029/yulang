# dots への現在の指示 (監督役が書く)

更新: 2026-11-08 21:35（監督役、サイクル 3 の検証後）。dots は編集しない。変わったら、更新時刻と「指示の ID」が変わる。

- 指示の ID: I-4
- 状態: ACTIVE（`STOP` と書き換えたら、dots は次のサイクルで止まる）
- 最大サイクル数: 24（ユーザー承認 2026-11-09, 12 から延長。これを超えたら、dots は作業を止めて待機の報告を書く）

## 現在の指示

計画表の **T1c** の続き（サイクル 1 は部分達成）。サイクル 1 で、候補ごとの局所の伝播（候補ごとに lower ≤ head ≤ upper の ordinary atoms を、直前の状態へ足して、実 ordinary solver を回し、そのあと実行可能な候補を集める）と、有限な source occurrence の allocator（`2 * row + side`）まで来た。残りは、上位の橋。優先順位（上から。今回は **50 分近く使う**こと）:
1. **宣言から制約を導く**: `impl Parent (box 'a) where Left 'a, Right 'a` で、`Right` の関連型が `'a` を絞る、という具体例を、ordinary 制約を手で渡さずに、宣言から導いて外側の入口で通す。絞り込みは impl の一意性ではなく、関連型の等式を通した型の流入（spec 6.3）。
2. **source identity**: 別々の occurrence の endpoint を、共通の source 変数へ統合する橋（graph/source identity）と、動的に生成される child への allocator の閉包。
3. **飽和の driver と停止性**: 再生成で現れた child をさらに解き、状態が安定するまで繰り返す。進捗の尺度は宣言時の Paterson 検査と K2 から導く。兄弟の順序独立は確定（where は連言、順序で結果は変わらない。spec 6.3）。証明の対象に入れてよい。
4. K2 / knownness と、language-visible な pending / selected / ambiguous / rejected の最終分類。外側の無条件 `resolve_exact`、X13〜X16 の少なくとも一つを外側の入口で PROVED。

## 報告に書く: 各定理がどの側か（ユーザーとの話から, 2026-11-08）

M1 の主張は、健全性・完全性・主型性の三つ組（`Typing ↔ ∃ S ∈ infer e, ...` の iff）。報告の定理の一覧に、各定理が**どの側に効くか**（健全性／完全性／主型性／補助）を一言添える。**拒否する範囲を、仕様の決定（K2、Paterson 検査など）として明示した定理**と、そうでなく実装の都合で弱めた定理を区別する。弱める場合は、弱めたことを定理の docstring に書く。

## Yulang2 との照合（証明の前に必ず）

証明を進める定義・規則が、旧世代 Yulang2 の挙動と合っているかを、ユーザーの記憶でなく**実機と文書**で確かめながら進める。
- 新しい定義や定理に着手する前に、`work/dots-audit` の `notes/audit/`（`x-oracle.md`、`y2-claims-*.md`）に、関係する主張や適合例の Yulang2 の結果が出ていれば読む（`git fetch origin work/dots-audit` で取得できる。まだ出ていなければ無視してよい）。
- 定義が Yulang2 の挙動と食い違う、または Yulang2 の規則を持ち込んでいない疑いがあれば、証明を積む前に、質問ノート（Yulang の例つき、遅延案を先頭）を 1 本書く。ユーザーの決定が権威で、Yulang2 は素材。
- 報告に「Yulang2 との照合」の節を設け、どの定義を何で照合したか（実機の例、文書の節、または未照合）を書く。

## I-3 の補足（サイクル 2 を受けて）

- 優先事項 1〜4 は I-2 のまま続ける（T1c は未達）。
- **例の完成**: 元の `impl Parent (box 'a) where Left 'a, Right 'a` の例は監督役の素描で、関連型の名前・右辺・出力 binding・既知の receiver が省かれていた。サイクル 2 が勝手に意味論を決めなかったのは正しい。**既存の spec の構文（6.1〜6.3 の associated type、`impl ... : type value = ...`、関連型の変数と等式）の範囲で、完全な具体例を自分で書き下す**こと（名前は自由）。意味論の選択が避けられない点だけ、質問ノート（遅延案を先頭）。
- **Main ファイルの配置（質問 `main-statements-placement` への回答）**: 監督役が検証 gate を調整した。`lean/Main*.lean`（root の新規ファイル）と、その `lean_lib`（`name = "Main*"`）の追加を `verify-lean.sh` が許可する。遅延案（`lean/Yulang/MainStatementsDraft.lean`）のまま進めず、`lean/Main.lean` に昇格してよい。全体 B4/B6 の Prop は、質問の遅延案（推奨）どおり、source carrier と独立 Classify がそろってから足す。
- **T7a**: 草稿 `MainStatementsDraft` を、`lean/Main.lean`（読むための主定理のファイル）に昇格させる作業を、余り時間ではなく**優先事項 4 の前に**進めてよい。現在証明済みの範囲（断片・仮定つき）は、そう明記して載せる。
- 「固定 pass の意味的冪等性」は飽和の完成ではない、と報告に書いたのは正確。これを維持すること。

## 余り時間の仕事（現在の優先事項が止まったときに、順に取る。独立で、競合しない）

- **F2: 引数の効果の変換を Lean にモデル化する（F1 の続き。T1c と並行して取ってよい）**: `notes/plan/m1-plan.md` の F2。監査 dot の F1 の報告（`git fetch origin work/dots-audit` の `notes/audit/f1-effect-passthrough.md`、質問ノート `2026-11-08-audit-F1-arrow-passthrough.md`）と、spec 5.5c の確定した位置づけ（部分型に入れず、明示的な変換の判断）に従う。
- **忠実性の確認 F1（優先して取ってよい）**: spec 5.5c（2026-11-08、ユーザー）の規則 `'a -> ['e] 'b` を `'a ['f] -> ['e, 'f] 'b` に cast できる（引数の行は空でなく全能。効果は関数の起動時に放出される）が、現在の Lean の核に入っているかを調べる。調べること: `Common.common_arrow_iff`（矢印の部分型は標準の反変・共変）、application の型付け規則、`Core.infer` の lambda・application が、この規則と整合するか。入っていなければ、反例の式（Yulang の例つき）と、定義を直す案（遅延する案を先頭に、2〜3 個）を `notes/handoff/` に報告する。Lean の既存の定理は変更せず、報告と質問ノートだけ。これは B4/B5/B6 の定義に響くので、結果を監督役が確認する。 （F1 の確認は監査 dot が実施済み。上の F2 に進む。）

- **T7b 到達可能性の解析（読み取りのみ・削除しない）**: `notes/plan/m1-plan.md` の T7b。Lean のメタプログラム（新規の `tools/Reach.lean` など、`lean/Yulang/` の外に置く）で、残したい定理から到達できない宣言とモジュールを列挙し、報告を `notes/handoff/` に出す。T7a の草稿（`lean/MainStatements.lean`）があれば、その Statement を根に加える。
- **T7a 主定理のファイル（文芸的 Lean）の草稿**: T7a。主定理を一つのファイル（`lean/Main.lean`）に再掲し、補題は別ファイルのまま。証明済みの定理は短い証明で、未完成は `def ... : Prop` で置き、日本語の docstring を付ける。主張の選択に迷う点は質問ノート。

- **T4 適合例の表を一本にする**: `lean/SpecExamples.lean` と `lean/SpecExamplesSettled.lean` の状態表を、一つの一覧（X1〜X24 の状態と、通っている入口の名前）にまとめる。既存の定理は削除しない。新しいモジュールとして作り、実在する定理と一致させる。
- **T3 の下調べ**: `notes/plan/m1-plan.md` の T3（variance 表と nominal carrier の接続）を読み、既存の `CommonDeclarationVariance*`、`CommonNominal*` の定理の一覧と、足りない橋を `notes/design/` に整理する（Lean は、橋が名指しできてから）。
- **適合例の追加**: spec 6.3〜6.5 の確定した例のうち、`notes/handoff/2026-11-08-m1-spec-examples-conformance.md` にないものを拾い、候補を `notes/handoff/` に提案する（spec は変更しない）。

## 参照

`notes/plan/m1-plan.md` の T1c、`notes/handoff/2026-11-08-dots-T1b-results.md`、`notes/design/2026-11-08-dots-T1b-producer-driver.md`、`notes/handoff/2026-11-08-dots-T1-results.md`、`notes/handoff/2026-11-08-m1-spec-examples-conformance.md`、`spec/06-roles.md` 6.2〜6.5（特に「where の子の解決は、兄弟の更新が安定するまで遅らせる」）。

## 回答済みの設計判断（監督役が転記）

- where の子は、兄弟の更新が安定するまで遅らせる。最終化はファイルの終わりの安定時。途中の曖昧・保留はエラーではない（`notes/questions/2026-11-08-T1b-sibling-recollection.md` の選択肢 1）。

## I-4 の追記: 具体例でなく一般の定理へ（ユーザーとの話から, 2026-11-08）

3 サイクルで、本命の一般定理が一つも閉じていない。定理の数は増えているが、固定した具体例（固定 3 slot の例、固定 Index 依存 2 辺など）の上の厳密な iff が多く、一般の定理に上がる速度が遅い。次のサイクルから、次の 3 つを守る。
1. **固定した具体例の iff を、単独の成果にしない**。その例が、どの一般定理の特殊例かを示し、次の目標をその一般定理にする。
2. **一つの定理の型（量化子つき）を渡す**: `notes/design/2026-11-08-b4-main-statement-draft.md`（B4 の主定理の素描。**ユーザーが承認済み**）。これを `Main.lean` の `B4Statement : Prop` に翻訳し、最短の補題の連鎖を設計ノートに書いてから進める。**既存の定理が、この定理のどの部分の特殊例か**の表を作る。
3. **報告に「この定理にあと何本の補題が要るか」を書く**（定理の数でなく）。

## 監督役からの前回サイクルへのコメント

- サイクル 3（再起動後、約 51 分）: `verify-lean.sh` PASS（1157 jobs、Audit、公理ゲート 82,887 宣言）、`integration/m1-final` に統合。73 の公開定理、新規 9 モジュール。**T1c の本命（四方向の分類、一般 `resolve_exact`、X13〜X16）は 3 サイクル連続で未達**だが、報告は正確で、未達と書いている。
- 特に良かった点: (1) **兄弟の順序独立**（`CommonRolePathOrder.observable_order_independent`: 任意の有限 2 path で実 Parent 入口の observable が一致）と、`CommonRoleSiblingOrders` で forward / reverse の最終モデル集合が等しいことを証明した。確定した where の連言の性質（spec 6.3）に合う。(2) `Main.lean` に 11 定理を昇格した（従来の 8 定理は草稿と同じ型）。「全言語完成を宣言する Prop は追加していない」という線引きが正しい。(3) T7b の根を、全 Audit・Main・X の入口へ拡張して実測した（削除なし）。(4) ハートビートを 10 分ごとに出し、復旧ではなく再開を選んだ記録も明確。
- 次の 1〜3 補題候補は dot 自身が `notes/design/2026-11-08-restart-next-saturation.md` に記録した: (A) 実生成 child の source provenance と有限仕事領域、(B) 新情報のない再訪を除いた driver の停止と意味的閉包、など。**I-4 の最優先はこの (A)(B)**。部品の追加で終えず、四方向の分類へ向かうこと。
- 注意: 「source parser から Lean request を作る生成の意味保存は未証明」と報告にある。ここは、Yulang2 の実機との照合（監査 dot の `x-oracle.md`）と合わせて、橋が本当に必要かを確かめること。

## I-5: サイクル 5 の後始末と次サイクルの順序（監督役, 2026-11-08）

サイクル 5 の短い回復は、新規 12 ファイルを 1 本ずつ公開できた（ビルド・公理は通る）。ただし `verify-lean.sh` は FAIL: 新モジュール `ArgumentEffectCastRuntime`、`CommonRoleAssociatedDeclarationExact`、`CommonRoleNamedAssociatedGraph` がどこからも import されておらず、ビルド・監査の対象外のため。単体ビルドは監督役が確認した（通る）。

次サイクルの先頭でやること（この順）:
1. **接続の 4 ファイルを、小さく分けて公開する**: `lean/Yulang.lean`（新モジュールの import 追記）、`lean/Main.lean`、`lean/Audit.lean`（追記のみ）、`lean/README.md`。1 回の公開は 1 ファイル、公開後に取り戻して一致を確かめる。ローカルの検証済み木は `da4cebca4`（回復用 clone）。
2. 公開後、公開済みの木とローカルの検証済み木の差分が空であることを、ファイル単位で確かめて報告に書く。
3. **重い検証（全体の `lake build --wfail`、全 Audit）は dot では走らせない**。監督役が検証する。dot は焦点ビルドのみ。
4. そのあとに I-4 の本命（B4 の一般定理、`B4Statement` の翻訳、既存定理との対応表、残り補題数）へ進む。

注意: `work/dots-main` は、統合ブランチが進む前の分岐点から出ている。サイクルの冒頭で `git fetch` して `origin/integration/m1-final` を取り込んでから始めること（`verify-lean.sh` は統合ブランチが祖先であることを要求する）。

- 回答済み（2026-11-09, ユーザー）: 唯一候補だが where 子に辞書がない親の最終分類は、子結果を保持する未完成の診断 tree とし、最終分類の写像は後から足す（`notes/questions/2026-11-08-cycle4-b4-classification-boundary.md` 境界 1、選択肢 1）。境界 2（辞書の観察同値）: 遅延、設計時はソース義務の正規順で比べる方向（2 寄りの 1）。

## I-6: ディスク容量（`No space left on device`, サイクル 6, 監督役 2026-11-09）

サイクル 6 は作業場の容量が尽きて止まった。測定では、`lean/.lake` は 1 つのビルドで約 800MB（`.lake/build/lib` の olean が 748MB）。ソースは 14MB。回復のために worktree を増やしてビルドキャッシュを写すと、1GB 級が積み上がる。

サイクルの冒頭で、次の順に片付けること（消す前に、未公開のコミットが無いことを `git log --not --remotes` で確かめる。無ければ消してよい）:
1. 作業場は **1 つだけ** にする。今の公開枝（`work/dots-main` の先頭）と同じ木を持つ worktree を一つ残し、`yulang-cycle4-recovered`、`yulang-cycle6`、その他の回復用・一時的な worktree と clone は、公開済みなら削除する。
2. 残す一つ以外の `lean/.lake`（ビルドキャッシュ）は削除する。`/tmp` と作業場に残した古いログ（`cycle*-focused.log`、`cycle4-recovery-verify.log` など）も消す。
3. 新しい worktree を作るときは、ビルドキャッシュを**コピーしない**。必要なら一つの worktree を使い回し、`git checkout` で切り替える。
4. 空き容量を `df -h` で確かめ、サイクル報告に「作業開始時と終了時の空き」を書く。
5. それでも足りない場合は、焦点ビルドだけにして、報告に容量の数字を書いて止まること（作業場は監督役から触れない）。

参考: 全体の検証は監督役が走らせる（dot は走らせない）。

## I-7: 上限延長と次の目標（監督役, 2026-11-09）

最大サイクル数を 24 に延ばした（ユーザー承認）。サイクル 12 までの検証は全て PASS（公理は propext / Classical.choice / Quot.sound のみ、ゲート 83,376 宣言）。サイクル 13 以降は、`notes/design/2026-11-08-cycle4-b4-statement-translation.md` の残り 5 橋のうち、次の順に進めること:
1. 区間の絞り込みと state 依存の materialization を含む子の、計算された source 領域への接続（サイクル 8〜12 の有限領域・位置の定理の拡張）。
2. 飽和の停止と意味的閉包（`saturate_terminates_and_closes`）。
3. 最終診断の独立な分類（質問ノートの境界 1 は回答済み: 子結果を保持する未完成の診断 tree）と、辞書の同値（境界 2 は回答済み: 正準なソース義務順の方向）。
4. 各サイクルの報告に「B4 の主定理にあと何本の橋が要るか」を書くこと（I-4）。

## I-8: T13（関連型の右辺の参照）は糖衣と決まった（ユーザー, 2026-11-09）

`impl Wrap (list 'a) where Container 'a: type out = list 'a::item` は、新しい型変数と、関連型の等式つきの `where` の子に展開される糖衣（`impl Wrap(list 'a, out = list 'b) where Container('a, item = 'b)`）。関連型は名前つきの role 引数で、名前なしの引数が決まれば名前つきの引数の制約は一度に決まる。`spec/06-roles.md` 6.3。**B4 の本命（T1c）を優先**し、その後で、次の 3 点を Lean に入れる:
1. 右辺が作る子を、`where` の子と同じく Paterson 条件の数え方に入れる（既存の仕組みのまま）。
2. `HeadDeterminesAssociated` を、「子の関連型の等式で決まる変数」まで広げる（上の `'b` は head に現れないが、`Container('a, item = 'b)` の等式で `'a` から決まる）。
3. 右辺の参照の循環の扱い。

## I-9: F2 の挿入位置は決着（ユーザー, 2026-11-09）と、T3

- F2: 変換は**型が求められたときに自動で入る**（注釈の有無によらない。`labeled` の cast と同じ需要駆動、`cast` 宣言との優先順位も `labeled` と同じ）。`spec/05-effects.md` 5.5c。残る Lean: (a) ソースの省略された引数の行（全能、空の行ではない）から核の矢印への橋、(b) 挿入の判断（期待される型が変換後の矢印のとき、普通の矢印に変換を入れる）、(c) X25（`x | f`、高階の引数に普通の関数）を挿入の判断を通して PROVED にする。
- T3（variance 表と nominal carrier の接続、`notes/plan/m1-plan.md` T3）: B4 の本命の橋が閉じた区切りで着手する。Codex のワーカーは使わず（コストのため）、dot のサイクルで進める。優先順位は T1c > F2 の (a)(b)(c) > T3 > T13 の Lean。

## I-10: 消さない整理（ユーザー承認 2026-11-09）

証明が積み上がって読みにくくなってきた。**削除はしない**（T7c は B4 が閉じてから、タグを切った上で）。次の整理を、B4 の橋の合間（各サイクルの最後の数分、または橋が詰まったとき）に少しずつ進めること。優先順位は T1c > F2 > T3 > 整理 > T13 の Lean。
1. **モジュール地図**（`lean/MODULES.md`、新規）: `lean/Yulang/` の全モジュールを、役割ごとに分類して一行の説明を付ける。分類の例: B4 の本流（橋 1〜5 のどれに効くか）、B5/B3/B2、旧い点モデル（置き換え済み）、E2 の反例の保存、例・回帰の確認（`…Examples`、`…Check`）、補助。`notes/handoff/2026-11-08-dots-cycle-3-reachability.md` の測定（届かない 19 モジュール）を参照。一度に全部でなくてよい。分類した範囲だけ公開し、未分類は未分類と書く。
2. **置き換え済みの印**: 旧い点モデルの定理や、新しい版に置き換わった局所版のモジュールの先頭の docstring に、「置き換え済み。現在の版は `…`」と一行足す（コードは変えない。`verify-lean.sh` は追記のみなら通る）。迷うものは印を付けず、質問ノートに書く。
3. **`Main.lean` の読みやすさ**: 読む順序と「ここまで証明済み、ここから未達」の境界を、橋 1〜5 の進み具合に合わせて書き直す（既存の定理は変えない）。

## I-11: 1 サイクルで大きな部分目標を取る（ユーザー承認 2026-11-09）

サイクルの上限は 25 分のまま（全体検証の禁止、心拍、復旧の仕組みも今のまま）。変えるのは**中身の大きさ**:
1. 1 サイクルで、橋の中の**大きな部分目標を 1 つ**取る。単位は補題の数ではなく、「この橋のこの形が閉じる」。開始時に、部分目標を 1 文で心拍の `activity` に書く。
2. 25 分をかけてよい。途中で定義を直し、証明が通るまで粘ってよい。ただし、**時間を埋めるための補題は足さない**（ゴミを増やさない）。小さな補題で終わるなら、それが部分目標を閉じるために必要な場合だけ。
3. 心拍は 10 分ごと、20 分の時点で一度、壊れない形で途中公開する。公開は 1 回の一括 API（拒否されたら、ファイルを分けず、正規の GitHub API で非 force・expected-head を指定した一括公開に切り替える）。
4. 行き詰まったら、設計メモと質問ノートを書いて、次の部分目標へ移る。
5. 報告には「部分目標は閉じたか／閉じなかった理由」と、B4 の主定理にあと何本の橋が要るか（I-4）を書く。
