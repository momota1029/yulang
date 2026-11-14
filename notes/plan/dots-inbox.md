# dots への現在の指示 (監督役が書く)

更新: 2026-11-08 21:35（監督役、サイクル 3 の検証後）。dots は編集しない。変わったら、更新時刻と「指示の ID」が変わる。

- 指示の ID: I-4
- 状態: ACTIVE（`STOP` と書き換えたら、dots は次のサイクルで止まる）
- 最大サイクル数: なし（ユーザー決定 2026-11-09: 上限は廃止。止めるのは `STOP` だけ。監督役が毎サイクル検証して統合する）

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

## I-12: 文章の中の語に注意（監督役, 2026-11-09）

`tools/verify-lean.sh` の禁止構文の検出は、README や Lean の docstring（文章）の中の語も数える。サイクル 26 の文章に英単語 `admit`（"need not admit ..."）があって誤検出で FAIL した（監督役が `allow` に言い換えて通した）。docstring・README・設計ノートの中でも、`sorry`・`admit`・`native_decide` などの語は書かないこと（言い換える）。

## I-13: 境界の入力の台帳（ユーザー承認 2026-11-10）

サイクル 62〜68 の報告は、毎回「新しい言語意味論の選択はしていない」と書き、質問ノートは 0 件だった。一方で、判断が要る所は「caller が渡す入力」として外に出されている（ソース同一性の map、ambient な端点のスロット map、binder の写像、invocation のキー、グラフ、注釈、有限の visit 列、など）。橋 1（実ソースからの生成）で、これらを実際に導く側に回ったとき、仕様が黙っている所が手戻りになる。

次のいずれかのサイクル（部分目標として 1 サイクル使ってよい。他の部分目標より先でなくてよいが、サイクル 72 までには出すこと）で、**台帳** `notes/design/<date>-boundary-inputs-ledger.md` を作ること:
1. Lean のモデルの中で caller が渡している入力を、モジュールごとに全部列挙する（名前、型、どの定理が前提にしているか）。
2. 各入力について、「実ソースからどう導く予定か」（導出の素案、または、導けない理由）と、「仕様（`spec/`）がその答えを持っているか、黙っているか」を書く。仕様の根拠は条番号で示す。
3. 仕様が黙っている入力は、そのまま質問の候補として、**遅延案を先頭に、Yulang の例つきで**、`notes/questions/` に 1 件ずつ起こす（一度に全部でなくてよい。決めてよいと思う案を勝手に採用しない）。
参考に、監督役が報告から拾った候補: (a) 再訪したとき同じ名前を共有するか（invocation の同一性）、(b) head にも等式にも出ない where の変数、(c) head に同じ変数が 2 回出る非線形 head。これに限らず、台帳で見つかったものを全部書くこと。

## I-14: 1 時間モードの試行（ユーザー承認 2026-11-11）

起動の間隔を、30 分から **1 時間**に変える試行を、1 日だけ行う（スケジュールの変更はユーザー側。変更後の最初の起動から適用）。**試行の間だけ**、次を適用する（I-11 の上限 25 分を置き換える）:
1. 1 サイクルは**最大 50 分**まで使ってよい。開始時に `date` を記録し、**25 分の時点で、壊れない形で途中公開**する（公開が止まったときの復旧を速くするため）。心拍は 10 分ごと（今のまま）。
2. 部分目標は、**サイクルをまたぐ価値のある大きさ**を選んでよい。ただし、時間を埋めるための補題は足さない（I-11 のまま）。1 つの大きな相互帰納や、探索的な証明のように、頭の中に状態を保ち続ける必要がある仕事を、優先して選んでよい。
3. 報告の先頭に、「このサイクルは何分使ったか」「部分目標が、25 分では収まらなかったか」を書く（監督役が、モジュール数・モジュールの大きさ・定理数を、30 分モードと比べるため）。
4. 全体検証は禁止のまま（焦点ビルドだけ）。公開は 1 回の一括 API（拒否されたら、正規の GitHub API で非 force・expected-head を指定した一括公開）のまま。

## I-15: 1 時間を使い切る（ユーザー指示 2026-11-11: 「フルに証明してほしい。時間がもったいない」）

I-11 の「時間を埋めるための補題は足さない」は、「部分目標が閉じたらそこで終わる」という意味ではない。**終わるのは、時間が来たとき（約 50 分）か、設計の判断で止まったときだけ**。部分目標が閉じたら、**その場で次の部分目標に進むこと**（サイクルを分けない）。
1. **次の部分目標の選び方**: `notes/design/2026-11-11-b4-gap-analysis.md` の「残りの作業パッケージ」（状態更新 driver、一般の Form の materialization、4 分類の帰納的な判断、K2 の組み込み、候補の順序と辞書の観察同値、辞書の全モデルでの健全性、宣言のモデルへの where の関連等式の入れ物、全部を束ねる `B4Statement`）から、主定理に最も近いものを選ぶ。**どれも主定理に直接効く仕事なので、「埋め草」ではない**。
2. 1 つの部分目標が閉じるたびに、そのモジュールだけを**途中公開**する（壊れない形。25 分の時点の公開は、そのうちの 1 回でよい）。公開した分は、監督役が次の起動までに検証して統合できる。
3. 止まってよいのは、(a) 約 50 分に達したとき、(b) 設計の判断が要る点に当たったとき（質問ノートを書き、遅延案で進められる別の部分目標へ移る。移れる部分目標が無いときだけ止まる）、(c) 全体検証でしか確かめられない問題に当たったとき、のいずれか。
4. 報告には、(i) 閉じた部分目標の一覧（それぞれの所要時間）、(ii) 終了の理由（上の a/b/c）、(iii) 次のサイクルの最初の部分目標の候補、を書く。時間が余って終了した場合は、その理由を書く。

## I-16: 証明の優先順位（監督役が決める。ユーザー委任 2026-11-11）

ユーザーは、証明の**進め方の優先順位**の決定を監督役に任せた（言語の意味論の判断は、今まで通りユーザーに聞く。質問ノートの作法も変えない）。I-15 の「主定理に最も近いものを選ぶ」は、以下の順で読み替える。上から順に、前の項目が閉じるか、設計の判断で止まったときだけ次へ進む。

**背景**: サイクル 106〜110 は、driver と飽和の有限断片を広げる仕事が続いた（どれも正しく、検証済み）。一方で、B4 の主定理は Lean にまだ文として存在せず（`MainStatementsDraft.lean` は settled 断片のみ）、「あと何が要るか」が報告の言葉でしか追えない。また、ギャップ分析の (2) の 4 分類と (4) の辞書は、ほぼ着手されていない。これまでモデルの誤りが 3 回見つかっているので、**手つかずの所を早く薄く通して、誤りを早く見つける**ことを優先する。

### P0（次のサイクルの最初の部分目標）: B4 の骨格
1. 承認済みの主定理（`notes/design/2026-11-08-b4-main-statement-draft.md`）の 5 項を、**量化子もそのまま**に、Lean の `B4Statement` として書く。新しいモジュール（例: `Yulang/B4Skeleton.lean`）に置く。既存の定義を使い、足りない概念（`Classify` など）は、その定義だけを先に書いてよい（証明は後）。
2. まだ証明していない部分を、構造体 `B4Bridges` の**フィールド**として並べる（橋 5 本と、ギャップ分析の残りのパッケージに対応させる。フィールド名と docstring で、どのパッケージか分かるようにする）。そして `theorem b4_of_bridges : B4Bridges … → B4Statement …` を証明する。
3. **禁止**: フィールドに、結論そのもの（またはほぼ同じ文）を入れること。各フィールドは、主定理より真に小さい主張であること。迷ったら、設計ノートに「このフィールドが結論を言い換えていないか」の説明を書く。
4. 骨格ができたら、以後の報告の先頭に「`B4Bridges` の未証明フィールド: k 本 / 全 m 本」を書く（I-4 の「橋の本数」を、この数で置き換える）。
5. 監督役は、骨格の文が承認済みの主定理と一致するかを読む。ずれがあれば次の inbox で直す。

### P1: 4 分類の判断（パッケージ 3 と 4）
独立な帰納的判断 `Classify`（pending / selected(k, ds) / ambiguous / rejected）と、実行版との iff。K2 の拒否規則もこの中に入れる。最初は、すでに `resolve_exact` がある断片で iff を通し、そこから広げる。

### P2: 辞書の健全性を薄く端まで通す（パッケージ 6）
最も単純な断片（where なし、候補 1 つ）で、辞書の構成 → 全モデルでの健全性を、まず端まで通す。広げるのはその後。ここでモデルの誤りが見つかれば、設計ノートと質問ノートを書く。

### P3: 候補の順序独立と辞書の観察同値（パッケージ 5）

### P4: driver と materialization の一般化（パッケージ 1, 2）
`B4Bridges` のどれかのフィールドを閉じる・縮めるのに必要な分だけ。

### P5: 宣言のモデル（橋 1、パッケージ 7、T13 の Lean）
関連 sugar の検査範囲（`2026-11-10-cycle70-associated-sugar-checking.md`）がまだ未決定なので、そこに触れる所は遅延案で進めるか、質問ノートで止める。

### 全体の規則
- 各部分目標は、**`B4Bridges` のどのフィールドを閉じる（または縮める）か**を、開始時に心拍の `activity` に書く。どのフィールドにも効かない拡張は、後回しにする。
- 優先順位は、監督役が inbox を更新して変える。dot は、自分の判断で順序を入れ替えない（ただし、上の項目が設計の判断で止まったときに下へ進むのは、I-15 の通り）。

## I-17: 主定理の文の修正（ユーザー決定と監督役のレビュー, 2026-11-11）

サイクル 112 の `pending_empty_survivors_obstruction` と `rejected_child_has_no_completed_readback` を受けて、承認済みの主定理の草稿に補遺を足した（`notes/design/2026-11-08-b4-main-statement-draft.md` 末尾）。

1. **保留が拒否より先（ユーザー決定）**: `RejectReason` の「候補ゼロ」は、`¬ RootPending` のときだけ。`RootK2`・`CandidateK2` も、それぞれが検査の開始を前提にしているかを確かめ、`RootPending` と重ならないようにする（重なるなら同じく `¬ RootPending` を付ける。迷ったら設計ノートに書く）。
2. **結果は診断ツリー**: 主定理 (2) を、実行版が返す診断ツリーと、独立な `Resolves (Local …) d tree` の一致として述べる。4 分類への写像は `Completed` のツリーだけ。
3. **やり方（削除しない）**: `Main.lean` の旧 `B4Target.Statement` は消さない。新しいモジュール（例: `Yulang/B4TargetV2.lean`）に、修正した `Statement`（量化子は旧と同じ）を書き、旧との差分（どこが違うか、なぜか）を docstring に書く。`B4Skeleton` の `B4Bridges` と `b4_of_bridges` を新しい target へ移す（旧のものは残し、「旧 target 向け」と docstring に書く）。修正後の target で、`pending_empty_survivors_obstruction` に当たる阻害が**もう起きない**ことを、定理で示す（排他性の補題: 新しい `Classify` は関数的）。
4. これを次のサイクルの**最初の部分目標**とする（I-16 の P0 の仕上げ）。その後は I-16 の P1 以降に戻る。報告の「`B4Bridges` の未証明フィールド k/m」は、新しい target の構造体で数える。

## I-18: 断片の正確性をやめ、一般の入れ物を下から作る（監督役, 2026-11-11）

Astra の棚卸し（`notes/design/2026-11-11-astra-general-boundary.md`、`lean/Yulang/GeneralSourceBoundary.lean`）で、`B4Target.SourceBoundary` の 13 項目のうち、一般の言語で定義できるのは部品 3 つ（Models、グラフ上の未解決、グラフ上の K2）だけで、残り 10 項目は断片の版しかないと分かった。断片ごとに独自の `Classify` を作って正確性を示す仕事は、主定理の枠へ差し込めないので、**これ以降は新しく始めない**（I-16 の P1〜P5 をこの I-18 で置き換える。I-17 の `B4TargetV2` は今まで通り最初にやる）。

順序（上から。前の項目の定義ができたら次へ。証明は定義の忠実性を確かめる小さな定理と、spec の例から）:
1. **宣言の入れ物と検査**: where の子と、その関連型の等式を持てる宣言（`Roles.Impl` の拡張ではなく新しいモジュール）と、spec 6.3 の宣言検査（隠れた field の除去、同 tag の併合、捕捉後の初めての併合の拒否、関連型の決定）を、実行と独立に定義する。→ `Vocabulary.Registry` と `Checked`。関連 sugar の検査範囲（`2026-11-10-cycle70-associated-sugar-checking.md`）に当たったら、質問ノートで止めて遅延案で進める。
2. **状態と需要**: 一つの共有の状態（通常制約、区間の上下端、グラフの識別子）と、多引数の正規化された需要（関連型の出力の義務つき）。ソースの下界の観察と、グラフの `.unresolved` をつなぐ。多引数の保留は草稿の補遺 3（ユーザー決定）に従う。→ `State`、`Demand`、`Models`、`RootPending`、`RootK2`。
3. **候補**: 捕捉、区間の伝播、同じ変数の併合、where の子の生成を一つの判断にまとめる。→ `Survivor`、`InspectionPending`、`CandidateK2`。
4. **進行**: 一般の状態更新と需要の再生成。→ `Step`、`Stable`、`Generated`。
5. **辞書**: ソース義務で索引づけた証拠と比較。→ `Evidence`、`Reorders`、`DictionaryEquivalent`。
6. 全部を `GeneralSourceBoundary` のインスタンスにし、`B4TargetV2` の骨格のフィールドを一つずつ閉じる。

**分担**: 監督役は Astra（Codex）にも、この順序の別の項目を渡す。衝突を避けるため、dot は**自分が始めた項目を心拍の `activity` に書き**、監督役が inbox の末尾に「Astra 担当: 項目 n」と書いた項目には手を出さない。既存の断片モジュールは消さない（部品として使ってよい）。
報告には、13 項目それぞれの状態（一般の定義あり／断片のみ／MISSING）の表を毎回付ける。

- Astra 担当: 項目 2（状態と需要）。2026-11-11 開始。
- Astra 担当: 項目 1（宣言の入れ物と検査）も Astra に移す（2026-11-12、dot のサイクル 119 が止まっていて、項目 3 が項目 1 を待つため）。dot は I-17 のあと、項目 5（辞書: `Evidence`、`Reorders`、`DictionaryEquivalent`）の定義から始めること。項目 1・2 の定義（`GeneralSourceState`、`GeneralSourceK2` と、Astra がこれから足す宣言のモジュール）を部品として使ってよい。

## I-19: `B4TargetV2` の `Local` に、検査の保留を足す（監督役のレビュー, 2026-11-12）

サイクル 119 の `B4TargetV2` は I-17 を正しく反映している（拒否の 3 理由を `¬ RootPending` で守る、結果は診断ツリー、4 分類は `Completed` だけ）。ただし、一つ穴が残っている: `SafeKnown` は `¬ InspectionPending` を要求するのに、`Local` / `Classify` には「下界の頭は分かっているが、候補の検査が終わっていない」ときの規則がない。そのため、`¬ RootPending ∧ InspectionPending` で K2 も候補ゼロも成り立たない需要（安定した状態でも起こりうる。最終の保留）には、どの `Local` も当てはまらず、`Exact`（実行版のツリー ↔ `Resolves`）が成り立たない。Astra の棚卸し（`notes/design/2026-11-11-astra-general-boundary.md`「Why the frozen target …」の最後の段落）も同じ点を指摘している。

直し方（新しい意味論の選択ではなく、承認済み草稿の順序をそのまま写す。草稿: K2 は曖昧より先、selected/ambiguous は「K2 の拒否がなく、未解決の検査もなく」）:
1. 新しいモジュール（例: `B4TargetV3.lean`。V2 は消さない）で、`Local` と `Classify` に `inspectionPending` 規則を足す: `¬ RootPending → InspectionPending → ¬ RootK2 → ¬ CandidateK2 → Local … .pending`（結果は同じ `.pending`。区別が要るならツリーの葉に理由を持たせてよいが、4 分類では pending）。
2. 候補ゼロの拒否（理由 iii）と `InspectionPending` が重ならないことを、`SourceBoundary` に足す仮定ではなく、**新しい `RejectReason` の定義側**で守る（理由 iii を `¬ InspectionPending` でも守る）。K2 の 2 理由は守らない（K2 は検査の保留より先）。
3. `Local` の関数性（各需要について高々一つの frontier）と、**全域性の補題**（`SourceBoundary` の各述語が排中律で決まるとき、どの需要にも少なくとも一つの `Local` が当てはまる）を証明する。全域性は、V2 の回帰（空ソースの重なり、子の拒否）に加えて、「検査の保留」の回帰例で確かめる。
4. `B4SkeletonV2` の合成も新しい target へ移す。報告の「未証明フィールド k/m」はこの新しい構造体で数える。
これは I-18 の項目 5 より先にやる（1 サイクルの最初の部分目標の大きさ）。
- Astra 担当: 項目 3（候補: `Survivor`、`InspectionPending`、`CandidateK2`）。2026-11-12 開始。dot は項目 3 に手を出さないこと。

## I-20: 同じ入力の需要をまとめる規則（ユーザー決定 2026-11-12）

spec 6.3 に「同じ入力の需要はまとめる」を追加した: 同じ role の需要が二つあり、すべての名前なしの引数が同じもの（同じソースの識別子、または等式で同じと示せる）を指すなら、関連型の出力を等しいとし、需要を一つにまとめる（保留のままでも）。I-18 の項目 4（`Step`）の規則の一つとして入れること。Lean では、(a) この更新が、関連型が head から決まること（`HeadDeterminesAssociated` 相当、Astra の `GeneralDeclarations.capture_determines_associated`）から、解決できる需要についてモデルを失わないこと、(b) 名前なしの引数の一つでも違う識別子なら（等式で同じと示せないなら）まとめないこと（Yulang2 の「共通の型変数」条件は使わない）、を定理にする。項目 4 の担当が決まるまでは、着手しない。

## I-21: 担当の更新（監督役, 2026-11-12）

Astra の項目 3d で、`SourceBoundary` の 13 項目のうち 9 つが一般の nominal carrier の上で定義された（`GeneralNominalLocalBoundary.recursiveFields`、設計ノート `2026-11-11-astra-general-boundary.md` の Item 3d の表。いくつかは言語全体の網羅性が部分的）。残りは `Step`、`Stable`、`Generated`、`Evidence` の 4 つ（`GeneralNominalLocalBoundary.Remaining`）。
- **Astra 担当: 項目 4（`Step`、`Stable`、`Generated`）**。I-20（同じ入力の需要をまとめる）もこの中で入れる。dot は手を出さない。
- **dot 担当: 項目 5 の仕上げ = `Evidence`**。サイクル 122〜128 の辞書の部品（レシピ、読み戻し、記録、frame）を、Astra の新しい `GeneralNominalRecursiveCandidates.Survivor`（分岐の条件、projection、繰り返しの捕捉の frame）に対する一般の `Evidence` として定義し、V3 骨格の `evidenceNode` フィールドを、この具体的な境界について**証明する**ことを目標にする。これが `B4Bridges` の最初の 1 本になる。Astra のモジュールの定義は変えず、使うだけにする。
報告の「未証明フィールド k/m」は、引き続き V3 の構造体で数え、閉じたフィールドがあれば、どの具体的な境界についてかを書くこと。

## I-22: K2 を「循環の上にある根」に広げる（ユーザー決定 2026-11-12）

spec 6 の K2 の決定に追記した: 根（または head の非変数 pattern が調べる位置）が、型のグラフの循環の上にあれば K2。循環は名前つきの型の引数を通ってよい（body は開かない）。`len (nest 0)`（μ ≈ list μ）は拒否、`len [loop 1]` は通る。Astra が項目 4 の続きとして実装する（`RootK2`・`CandidateK2` の修正と、停止の証明）。dot の `Evidence` 側は、K2 で拒否された需要に辞書を作らないことだけ確かめればよい。

## I-23: `evidenceNode` を安定した状態に限る（監督役, 2026-11-12）

サイクル 130 の阻害（全 state 橋の形式的阻害）は、骨格の分け方の問題だと判断する: V3 の `EvidenceNode` は**任意の** state について「選ばれた head と子の証拠 ⇒ 親の証拠」を全モデルで要求するが、選択の条件（分岐の制約、出力の等式）はまだ state に書き込まれていないので、元のモデルの中に反する モデルがある。主定理の (4)（`DictionarySound`）が要求するのは、実行版の**最終状態**（`(e.run r s d).1`）についてだけで、その状態は `closure` で root と生成された全需要について `Stable` になる。
直し方（新しいモジュール、V3 は消さない）: `B4SkeletonV4` で、`evidenceNode` の前提に `b.Stable r s d`（と、子についての `Stable`、または「選択が state に記録済み」を表す述語）を足し、`b4_of_bridges` が通ることを示す（`DictionarySound` の証明で、最終状態の root と子が `closure` により `Stable` であることを使う）。そのうえで、Astra の `Step` / `Stable`（`GeneralNominalSaturationSteps`。安定なら選ばれた packet が `Committed` で、その制約が全モデルで成り立つ）と、サイクル 130 の「記録による修復条件」をつないで、具体的な境界について `evidenceNode`（V4 版）を証明することを目標にする。Astra のモジュールの定義は変えない。

## I-24: `Audit.lean` を凍結し、監査の追記は小さな別ファイルへ（監督役, 2026-11-12）

サイクル 131〜136 の公開が止まり続けている原因は、`lean/Audit.lean` が約 690 KB（10,800 行）まで育ち、追記のたびにファイル全体の blob を公開しようとして失敗している（サイクル 135 の「Audit blob の作成が未確認（404）」）ことだと判断する。
- **今後 `lean/Audit.lean` には何も追記しない**（凍結）。
- 新しい `#print axioms` の行は、**新しい小さなファイル** `lean/Audit/<名前>.lean` に書く（例: `lean/Audit/Cycle136.lean`。1 ファイルは数十 KB 以下を目安に。必要な `import` を先頭に書く）。既存の `lean/Audit/*.lean` も追記のみ。
- `tools/verify-lean.sh` はこの形に対応済み（`Audit.lean` と `lean/Audit/*.lean` を全部実行し、公理を検査する。新しいファイルとして `lean/Audit/*.lean` を許可）。
- サイクル 131〜135 で手元に溜まっている監査の行も、`Audit.lean` に足さず、`lean/Audit/` の新しいファイルに移してから公開すること。`Yulang.lean` も大きいので（約 1,800 行）、公開が通らなければ同じ理由を疑い、報告に書くこと（監督役が分割を検討する）。
- I-24 追記（2026-11-12）: `lean/README.md`（約 560 KB）も同じ理由で凍結する。モジュールの説明の追加は、`notes/design/<日付>-<内容>-module-guide.md` のような新しい小さなファイルに書く（サイクル 136 のやり方のまま）。`Yulang.lean` への import の追記は小さいので続けてよいが、公開が止まったら同じ理由を疑うこと。

## I-25: 初期状態と到達可能性を target / 骨格に入れる（監督役, 2026-11-12）

サイクル 138 の `no_evidenceNode`（到達不能な raw journal での反例、`not_sourceFormed` つき）への判断（質問ノート `2026-11-12-cycle138-stable-journal-evidence-scope.md` の末尾）: 草稿の「任意の状態 Σ」は journal を含まない。Σ を journal が空の初期状態として埋め込み、橋は到達可能な状態だけを量化する。
1. `B4TargetV5`（新しいモジュール。V3/V4 は消さない）: `SourceBoundary` に `Initial : Registry → Demand → State → Prop` を足した構造（または V3 の境界を包む構造）を作り、`Statement` の 5 項は `∀ s, Initial r d s → …` で量化する（それ以外の量化子は V3 と同じ）。docstring に「草稿の Σ = journal が空の初期状態」と書く。
2. `B4SkeletonV5`: 状態を量化する各フィールド（`progress`・`execution`・`halted`・`closure`・`stepModels`・`frontierLocal`・`whereAccessible`・`completedReadback`/`treeExecution`・`canonicalLocalOrder`・`evidenceNode`）を、`Reachable r d s`（ある初期状態から `Steps (b.Step r d)` で到達）を前提に取る形にし、`b4_of_bridges` を示す。
3. 具体的な境界では `Initial` = `InitialSource`（空 journal）、`Reachable` ⇒ `SourceFormed` を示し、サイクル 138 の正例（SourceFormed・Stable・現在の Evidence）を、V5 の `evidenceNode` の証明へつなぐ。Astra の 5 本（`closure`・`stepModels`・`frontierLocal`・`localIdentity`・`dictionaryRefl`）も V5 へ移す（前提が弱くなるだけなので、移し替えで通るはず）。
- I-24 追記（2026-11-13）: 新しいモジュールは、必ず `lean/Yulang.lean` から import すること。`lean/Audit/*.lean` からだけ import すると `lake build` が組み立てず、監査ファイルの実行が失敗する（サイクル 153 で起きた。監督役が import を足して直した）。`tools/verify-lean.sh` もこれを検査するようにした。

## I-26: 片付いていない impl の出力を根拠にした展開は保留（ユーザー決定 2026-11-13「遅延」）

Astra の新しい終了性の分析（`notes/design/2026-11-13-termination-fresh-analysis.md`）が、輪にならない蓄積のポンプで、輪だけの保留（補遺 5・6）では需要が無限に増えることを示した。ユーザーの決定で、spec 6.3 と B4 草稿の補遺 7 に記録した: 片付いていない需要（impl を選んだが where の子に保留が残る）の関連型の出力は、ほかの需要の、候補を調べるのに要る入力の頭の根拠にしない。ソースの制約か片付いた需要の出力が根拠になれば再開する。等式は通常の制約・まとめ・K2 には使う。
- Astra が終了性の側（ガードの実装と停止の証明）を担当する。dot の `Evidence` 側は、このガードで保留になった需要に辞書を作らないことだけ確かめればよい。`Stable` の定義が変わる場合は、Astra の新しいモジュールに合わせる（Astra の定義は消さない）。

## I-27: 前のサイクルのファイルも追記のみ（監督役, 2026-11-13）

サイクル 166 が、サイクル 165 で公開済みの `lean/Yulang/GeneralDictionarySharedCapturedInstallable.lean`（simp 引数の整理、`set_option` の削除）と `lean/Audit/Cycle165FinalDependencyGate.lean`・`Cycle165PublicTypes.lean`（import と `wanted` の追加）をその場で書き換えたため、`tools/verify-lean.sh` が FAIL した（既存行の削除・変更）。監督役がこの 3 ファイルを統合ブランチの版に戻してから統合した（意味の変化なし、ビルドと監査は PASS）。
- 公開済みのファイルは、前のサイクルのものでも**追記のみ**。既存の行（`set_option`、simp の引数、`wanted` のリストを含む）は書き換えない。
- 新しいモジュールの公理チェックは、新しい `lean/Audit/<名前>.lean` に書く（既存の監査ファイルの `wanted` には足さない）。
- 戻した結果、`GeneralDictionarySharedCapturedInputReady` と `GeneralDictionarySharedCapturedProducer` は、サイクル 166 の監査パートには入っていない可能性がある。`tools/AxiomGate.lean` が全宣言を検査しているので公理は確認済みだが、次のサイクルで新しい監査ファイルに入れておくこと。

## I-28: 終了性が示された Step に合わせる（監督役, 2026-11-14）

Astra が、根の入力がソースで決まった型（ground root）のとき、実際の検査つき Step（`GeneralNominalActualInspectionSteps.Step`）が止まることを前提なしで証明した（`GeneralNominalGroundHeadMatching.ground_class_p_accessible`）。この Step は、片付いていない出力の保留（I-26）、区間の共有の保持、実際に調べる位置での K2 を含む。
- V5 の骨格への差し込み口は `GeneralNominalActualBoundary.boundary`（ground 版は `groundBoundary`、点のソース版は `GeneralNominalActualPhaseBoundary.boundary`）。6 本の構造フィールドと ground の progress は証明済み。
- 今後の `evidenceNode`・`generatedChildren`・`treeExecution` などは、この境界の Step と `Stable` に向けて証明すること（古い feedback / value / settled の境界は消さないが、新しい成果はこちらを対象にする）。
- 局所の分類（Local / pending / K2）を新しい検査（shared generation、actual-position Safe / AlternativesSafe）にそろえる作業は、監督役が別の Astra に頼んでいる。dot はその定義を待たずに、既存の `Local` で示せる部分から進めてよい。食い違いを見つけたら報告に書くこと。

## I-29: 実際の引数の名前（中心）を表現に置く（ユーザー決定 2026-11-14）

spec 6.5 に追記した: 不変な引数は区間に加えて中心（実際の引数の名前）を持つ。「共有の証明が無ければ保留」という実装上の検査は、意味の規則ではない（B4 草稿の補遺 8）。監督役は Astra に、中心つきの表現と、それを使う Step（共有の証明が常にある Step）への移し替えを頼む。dot は I-28 の境界で作業を続けてよい。中心つきの Step が統合されたら、そちらへ移す指示を出す。

## I-30: `evidenceNode` を中心つきの ground 境界で証明する（監督役, 2026-11-14）

Astra の二人目が、中心つきの Step（spec 6.5 の中心、補遺 8）の上で、根の入力が点で決まった型（ground）の境界 G = `GeneralNominalCenteredGroundBoundary.groundBoundary` について、V5 の 14 フィールドのうち 10 本を証明した（`GeneralNominalCenteredGroundComposition.bridges`、`composition : Remaining roles → B4TargetV5.Statement G executor`）。残りは `whereAccessible`・`canonicalLocalOrder`・`evidenceNode`・`generatedChildren`。
- **dot の担当は `evidenceNode`（`B4SkeletonV5.EvidenceNode (groundBoundary roles)`）**。I-28 の actual 境界での Evidence の成果を、この G に向けて移す・証明し直すこと。正確な型は `GeneralNominalCenteredGroundComposition.Remaining.evidenceNode`。
- 残りの 3 本は Astra が担当する（まとめ終わってから選ぶように分類を強めた G' を作る可能性がある。そのときは G' の evidenceNode に移すよう追って指示する）。
- 前のサイクルのファイルは追記のみ（I-27）。コメントに `admit`・`sorry` などの語を書かない（検査が拾う）。

## I-31（2026-11-14）import の並べ替え・空行の削除をしない

cycle 181〜183 で `lean/Yulang.lean` の import を並べ替え、いくつかのファイルの末尾の空行を消したため、統合の検査（行の削除の禁止）で落ちた。監督が元の並びに戻し、新しい import だけを末尾に足した（`fix/dots-183`）。
- `lean/Yulang.lean` は**末尾への追記だけ**。既存の行の移動・重複の整理・空行の削除をしない。
- 他の worker のファイル（末尾の空行を含む）を書き換えない。
- 新しいモジュールは必ず `lean/Yulang.lean` から import する（cycle 177 で漏れた）。
- `lake build --wfail` で警告も失敗になる（cycle 178 で使っていない simp 引数が落ちた）。

## I-32（2026-11-14）evidenceNode の向け先

Astra は境界を G′ → head-only の後継（`GeneralNominalCenteredHeadWFBoundary.boundary`、V6 = `B4TargetV6`）へ移した。理由: ユーザーの決定「名前無し区間は引数で，名前あり区間は出力」（spec 6.3）。候補は head だけで照合し、出力のぶつかりは型エラー（V6 の `OutputConflict`）。
- evidenceNode は、V6 の Classify（出力のぶつかりがないことが選択の条件）の上で書き直す必要がある。今の G 向けの作業は続けてよいが、移し先はこの WF 境界になる。
