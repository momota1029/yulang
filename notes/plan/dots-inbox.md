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

## I-33（2026-11-15）evidenceNode の移し先（確定）

Astra は V6 の後継境界を組み上げ、12 の性質・停止性・正規化 executor の順序非依存を前提なしで証明した。境界は `GeneralNominalCenteredHeadMatStepBoundary.boundary roles`（全部の型の形を翻訳、根拠のある頭部だけ覚える＝spec 6.3 の 2026-11-15 の決定、head だけで照合）。出力の割り当ての衝突を直した後継（`GeneralNominalCenteredHeadAlloc...`）に移る予定なので、最終的な移し先はそちらになるが、型の形は同じ。
- dot の担当は次の型（`G := GeneralNominalCenteredHeadMatStepBoundary.boundary roles`）:
  `B4SkeletonV5.EvidenceNode (B4TargetV6.prior G)`。
  展開形は notes/design/2026-11-15-centered-head-mat-output-target-collision.md の「Exact evidence interface for dot」。
- 前の G / G′ 向けの evidenceNode の作業は、この境界へ移してよい。モデルは「全部の型の形を翻訳した journal」の Models なので、古い packet の解釈には頼らないこと。
- I-31（import は追記だけ）、I-27（前のサイクルのファイルは追記だけ）は引き続き守る。`pp.universes true` は監査ファイルに入れない（公理の検査が名前を読めなくなる）。

## I-34（2026-11-15）I-33 の型を取り下げる。dot を主担当にする

cycle 199 の反例（`GeneralDictionaryMatPriorConflict199.not_prior_evidenceNode`、Alloc 境界は `lean/Audit/Cycle199AllocPriorCheck.lean`）は正しい。I-33 で指定した `B4SkeletonV5.EvidenceNode (B4TargetV6.prior G)` は、OutputConflict で正しく拒否される状態にも辞書を要求するので成り立たない。監督役の指定の誤りで、意味論の問題ではない。この型は取り下げる。

- **新しい担当（選ばれた場合だけの evidenceNode）**: `G := GeneralNominalCenteredHeadAllocBoundary.boundary roles` について、`B4SkeletonV5.EvidenceNode` と同じ形に、`Unique b r s d key children` の後ろへ前提 `¬ G.OutputConflict r s d key` を足したもの。dot は自分のモジュールにこの定義を置いて証明してよい。
- Astra は V7（まとめた需要の出力の食い違い `MergedOutputConflict` を拒否に足したもの。spec 6.3 の 2026-11-15 の決定 2）の境界と、この形の field から `DictionarySound` を導く合成を作っている。統合されたら、正確な名前を追って書く。その V7 の field は前提に `¬ MergedOutputConflict` も持つ。dot の V6 版からは、前提を一つ足すだけで移せる見込み。
- **運用の変更（ユーザーの指示, 2026-11-15）**: Astra を回し続けるのはやめる。残りの項目は dot が主担当になる。
  1. 上記の evidenceNode（selected-only）。
  2. `GeneratedChildren`（`GeneralNominalCenteredHeadAllocCompletion` の `HeadBaseline` / `PacketAssembly` / `ChoiceFromCommon`）。Astra が見つけた障害: 既に子を記録して selected のまま残る親（journal にモデルがない）では、一般の `HeadBaseline` は偽になる。「既にある子」と「新しい据え付け」を分けて述べ直す必要がある。詳細は Astra の V7 のノートが統合されてから書く。
  3. K2 の射影の網羅。
- 反例で型が偽と分かったら、今回のように閉じた反証と、型を遅らせる案を書いて止まること。勝手に型を弱めない。この進め方でよい。

## I-35（2026-11-15）V7 の正確な担当型

Astra の最後のターンが統合された（以後 Astra は回さない。I-34）。正確な担当は次の 2 本で、両方とも dot が担当する。境界は `b := GeneralNominalCenteredHeadAllocV7Boundary.boundary roles`。

1. `B4SkeletonV7.EvidenceNode b`（別名 `GeneralNominalCenteredHeadAllocV7Composition.EvidenceNode roles`）。前提は `B4TargetV7.Local b r s d (.selected key children)` で、SafeKnown、head の一意性、`¬ OutputConflict`、`¬ MergedOutputConflict` を含む。展開形は `notes/design/2026-11-15-centered-v7-merged-output-conflict.md` の「Exact evidence field for dot」。cycle 199 の反例は、この field では空虚に成り立つ（`GeneralNominalCenteredHeadAllocV7Cycle199Regression.evidenceAt`）。I-34 の V6 版で始めた作業は、この型へ移す。
2. `B4SkeletonV7.GeneratedChildren b`（別名 `GeneralNominalCenteredHeadAllocV7Composition.GeneratedChildren roles`）。

この 2 本から主定理が出る: `GeneralNominalCenteredHeadAllocV7Composition.composition node generated : B4TargetV7.Statement b (GeneralNominalCenteredHeadAllocV7Executor.executor roles)`。ほかの前提はない。
- 注意: 一般の `HeadBaseline` / `SelectedCompletion` は偽（`GeneralNominalCenteredHeadAllocV7ParentBaseline.not_headBaseline`, `not_selectedCompletion`）。子をすでに記録した selected の親があるため。GeneratedChildren をこの経路で示そうとしないこと。`PacketAssembly` と `ChoiceFromCommon` は未解決で、反証もされていない。
- 優先順位: EvidenceNode を先に。K2 の射影の網羅はその後。

## I-36（2026-11-15）根拠の判定を role の既定値に対応させる（dot の担当）

cycle 202 の反例（`GeneralDictionaryAllocDefaultCounterexample202.not_selected_evidenceNode`, `not_v7_evidenceNode`）は正しい。原因は担当型ではなく、境界が受け継いでいる根拠の判定（`GeneralDictionaryRecursiveEvidence.Instance` → `RequestReady.RootDefined`）が、関連型の明示的な式しか認めないこと。spec 6.1（確定, 2026-11-04）では、role に default があれば impl は関連型を省略できる。したがって直すのは判定の側で、意味論の問題ではない。監督役は `notes/questions/2026-11-15-selected-default-evidence-target.md` の「Possible repair」を採る。

- 次の順で進めること:
  1. 新しい根拠の判定を作る。選ばれた impl について、関連型の本体が明示か default かを記録し、どちらも total expression で解釈する。古い判定は消さない（追記のみ）。
  2. V7 の Alloc 境界と同じ境界で、`Evidence` だけをこの判定に差し替えた後継の境界を作る。12 の性質と Step・Stable・Local・Models は `Evidence` に依存しないはずなので、そのまま移す。依存していたら報告すること。
  3. その後継で `B4SkeletonV7.EvidenceNode` を証明する。cycle 199 と 202 の 2 つの反例が、どちらも問題にならないことも示す（199 は拒否で空虚に成り立ち、202 は default で根拠が立つ）。
  4. 合成（`GeneralNominalCenteredHeadAllocV7Composition.composition` に相当するもの）を後継の境界へ移す。
- 新しい判定は、明示の式と default の両方を認める以外の点で、古い判定より緩くしないこと。新しい判定が spec の意味と一致することを示す小さな例（明示 1 つ、default 1 つ、上書き 1 つ）を付けること。
- 明示の式だけの断片で証明できても、それを I-36 の完了とは呼ばない（名前を分ける）。cycle 202 のノートの方針どおりでよい。
- GeneratedChildren は cycle 202 の分割（`FreshCompletion`）でよい。新しく据え付ける場合の証明は、EvidenceNode の後に回す。

## I-37（2026-11-15）根拠の判定を式の意味で決める。古い歯止めはまとめて点検する

cycle 204 の default の直しは正しい（`DefaultSelected204.evidenceAt`, `DefaultRejected204.evidenceAt`）。cycle 204 の反例（`GeneralDictionaryDefaultEvidence204JoinCounterexample.not_evidenceNode`）も正しい。原因は、I-36 で監督役が「明示と default のほかは古い判定より緩くしない」と書いたことにある。この指示は取り下げる。

- **方針**: 根拠の判定（Evidence）は、操作の側の Models と同じく、式の意味（total expression）で決める。古い部分的な変換器の構文的な歯止め（`generated_ready` / unknown=false など）は残さない。`notes/questions/2026-11-15-cycle204-total-expression-evidence.md` の「Possible next repair」を採る。言語の意味は変えない。
- **点検はまとめて行う**: 歯止めが 1 周に 1 つずつ見つかっている（199 は拒否、202 は default、204 は部分変換器）。次の周では、新しい Certificate に残っている全部の条件を一覧にすること。それぞれについて、次の 3 つのどれに当たるかを書く。
  - (a) Step・Stable・Models・Local・Frame から導ける（導いて、条件から外す）。
  - (b) 意味の対応物に置き換える（total expression の等式、根拠の出どころ、順序つきの子）。
  - (c) 本当に必要で、反例があっても外せない。この場合は、その反例と理由を書いて止まる。
  一覧は design ノートに書くこと。
- 古い判定とのつながりは、古い判定で扱えていた範囲で新しい判定が成り立つこと（old → new）を示せばよい。逆向き（new → old）は要らない。
- 守ること: 選ばれる入力を勝手に狭めない。constructor の解釈が単射だと仮定しない。結論を仮定に入れない。明示だけの断片などの部分的な結果には、別の名前を付ける。
- その上で `B4SkeletonV7.EvidenceNode` を後継の境界で証明する。反例が出たら、I-34 のとおり閉じた反証と案を書いて止まる。

## I-38（2026-11-15）据え付けに role の既定値の出力を含める（操作の側の直し）

cycle 206 の判定の直し（`TotalEvidence206`, `TotalBoundary206`, `TotalJoin206` など）は正しい。新しい反例（`GeneralDictionaryDefaultGap206Counterexample.not_evidenceNode`）も正しい。原因は操作の側にある: packet の emitted schema が role の default の出力を含まないので、`Committed` が default の式を確かめずに成り立ち、据え付けが起きない。spec 6.1（確定, 2026-11-04）では、impl が関連型を省略すると default が使われる。したがって、選ばれた impl の出力の等式に default の本体を含めるのが spec どおりの動きで、意味論の変更ではない。`notes/questions/2026-11-15-cycle206-default-commitment.md` の「Possible next repair」の 1 つ目を採る。

- **やること**:
  1. emitted schema（据え付けで足す出力の等式）に、明示・default・上書きのすべてを、本体の出どころつきで入れる。`Committed` がそれを確かめるようにする。別の遷移（effect-completion）を足す案は採らない。
  2. Step を変えた後継の境界を作り、12 の性質（progress、停止性、closure、stepModels、canonicalLocalOrder など）を証明し直す。前の証明を使い回せるところは使い回す。古いモジュールは追記のみ。
  3. 合わせて、まとめた需要と、子をすでに記録した親についても、default の出力を同じように扱えているか確かめる（I-37 のとおり、一度にまとめて点検する）。
  4. その境界で `B4SkeletonV7.EvidenceNode` を証明する。cycle 199・202・204・206 の 4 つの例を回帰として残す。206 の例は、据え付けが default の等式を足すので bottom のモデルが消える、という形で問題がなくなるはず。
- 守ること: 選ばれる入力を狭めない。出力の等式を弱めない。結論を仮定に入れない。反例が出たら I-34 のとおり止まる。
- 一周で終わらない大きさなので、途中の成果は checkpoint として公開してよい。12 の性質を証明し直すところまでで 1 周を使ってよい。

## I-39（2026-11-15）evidenceNode の全体の計画を先に書く

cycle 209・210 の部分的な結果（`SemanticReplay209`, `NominalFrame210` など）は正しく、制限の書き方も正確でよい。ただ、制限つきの断片が周ごとに増えていて、無条件の `B4SkeletonV7.EvidenceNode`（I-38 で直した境界）までの距離が見えない。
- 次の周は、Lean の断片を増やす前に、design ノートに**無条件の EvidenceNode までの証明の計画**を書くこと。
  - 選ばれた節点を場合に分けて、全部の場合を挙げる。例: 新しく据え付けた親、記録済みの親（入力が点・区間）、頭の形（変数・名前つき・構造・scalar）、merge の後、refresh の後。
  - それぞれの場合について、いまある定理で済むのか、どの補題が足りないのかを書く。
  - 足りない補題が偽かもしれないところは、先に小さな反例を探す。
  - FreshCompletion（generatedChildren の、新しく据え付ける場合）についても同じ表を作る。
- 計画を書いたら、残り時間で、一番大きな穴を埋める補題から進めてよい。
- 計画の途中で、言語の意味を決めないと進めない場所が見つかったら、例を付けて質問のノートに書くこと（監督役がユーザーに聞く）。

## I-40（2026-11-15）FreshCompletion は外す。残りは EvidenceNode の 1 本

cycle 211 の計画（`notes/design/2026-11-15-cycle211-whole-evidence-plan.md`）と結果を受け入れる。
- `GeneralDictionaryDefaultFreshProbe211Refutation.not_freshCompletion` は正しい。FreshCompletion は監督役が割り当てた補助で、それが強すぎた。取り下げる（質問ノートの遅延案どおり。選択の歯止めやモデルの存在の仮定は足さない）。
- `GeneralDictionaryDefaultComposition211.composition` により、I-38 の境界の `B4TargetV7.Statement` は `B4SkeletonV7.EvidenceNode (DefaultBoundary208.boundary roles)` だけを前提にする。GeneratedChildren はもう要らない。**B4 の残りはこの 1 本**。
- 次の担当: この EvidenceNode を無条件に証明する。計画の「Dependency graph and largest missing bridge」のとおり、(A) ChoiceCompatible と (B) 一つの代入で journal・packet・effect を同時に満たすこと、を選ばれた節点の範囲で示す。それが偽になる場所では、記録済みの証明書の持ち越し（replay）で埋める。
- EvidenceNode は journal のモデルごとの主張なので、モデルが空の状態では空虚に成り立つ。(B) が要るのは、モデルがある状態だけ。計画の「Counterexample-first tests」を先に回し、(A)・(B) が偽になる例を探してから証明に入ること。
- 制限つきの名前つき型の断片（`NominalFrame210` の類）は、計画の表で必要と分かった場合だけ足す。

## I-41（2026-11-16）型変数を共有する impl は、実際の引数の等式を足す（ユーザー決定）

dot が止まっている間に、監督役が Astra を 1 ターンだけ使い、cycle 217 の候補を確かめた。結果は本物の反例だった（`GeneralDictionaryGroundCopy218SaturatedRefutation.not_evidenceNode`, `positive_premises`、ノート `notes/questions/2026-11-16-cycle218-ground-copy-counterexample.md`）。
- 反例の中身: `impl P (Foo 'x 'y): where 'x: R 'y` と `impl R 't 't` がある。子の需要 `R (:{tick int}) (:{tick bool})` の区間がまだゆるいうちに、`impl R 't 't` が区間だけで選ばれる。親を据え付け直して根全体が安定した後でも、古い子が selected のまま残り、辞書の根拠がない。
- **ユーザーの決定（spec 6.5 に追記, 2026-11-16）**: 候補の照合は今までどおり区間の端点と既知の頭だけで行う。型変数を共有する impl を選んだら、その位置の実際の引数（中心）どうしが等しいという等式を制約として足す。矛盾すれば、その需要の拒否（型エラー）として報告する。OutputConflict と同じ扱いで、保留は作らない。
- **dot の担当**:
  1. 据え付けの effect / packet に、選んだ宣言の head の型変数の共有から来る、中心の等式を含める（I-38 で default の出力を入れたのと同じ場所）。
  2. 拒否の理由に「共有の等式が矛盾する」を足した後継の target（V8。V7 と同じく、曖昧が先で、保留にはしない）と、その境界を作る。12 の性質を移す（I-38 のときのように Step が変わるなら証明し直す）。
  3. 218 の反例が、後継の境界では拒否になることを回帰として示す。
  4. 後継の境界で EvidenceNode を証明する（cycle 211 の合成を移す）。199・202・204・206・218 の回帰を残す。
- 218 周目の途中の成果（Lean）は公開前に止まったため、残っていない。Astra の 218 のモジュール（`GeneralDictionaryGroundCopy218*`）が統合に入っている。I-34（反例で止まる）、I-31（import は追記だけ）は引き続き守る。

## I-42（2026-11-17）検証が済んだ成果は、毎周必ず公開する

cycle 222〜225 で、検証の済んだ成果を「publication hold」として手元に留め、公開しなかった（ユーザーの依頼で、まとめて公開された）。これは standing orders（公開は 30 分ごと、周の途中でも）に反する。公開に承認は要らない。
- 毎周、検証が済んだ成果（Lean・監査・ノート・報告・heartbeat）を `work/dots-main` に公開すること。手元に留めない。前の周の成果が未公開なら、それも含めて公開する。
- 公開が技術的に失敗したら（API のエラーなど）、その内容を heartbeat に書いて、次の周の最初に公開をやり直す。
- 1 周を数分で終えて残りの時間を使わないのは避ける。I-41 の V8 の EvidenceNode に向けて、計画の次の穴に時間を使うこと。

## I-43（2026-11-17）凍結ファイルは戻さない

cycle 220 で `lean/Audit.lean` と `lean/README.md` に行を足し、220〜225 のまとめての公開でそれを消した（「freeze repair」）。統合の検査は行の削除を禁じているので、監督役が統合ブランチの版を残す直しを入れた（`fix/dots-225`）。
- `lean/Audit.lean` と `lean/README.md` には、今後は足しも消しもしない。統合ブランチにある今の内容を、そのまま保つ。
- 新しい監査は `lean/Audit/<Name>.lean` に置く（今までどおり）。
- 1 周の上限（ユーザーが決めた 25 分）の中で、できるだけ I-41 の V8 EvidenceNode の次の穴に時間を使うこと。

## I-44（2026-11-17）見直し後は、区間の集約の名前を作り直す（監督役の決定）

cycle 230 の反例（`GeneralDictionaryUpper230Regression.not_evidenceNode`）は正しい。質問ノート `notes/questions/2026-11-17-cycle230-stale-aggregate-evidence.md` への答え:
- **意味の上では、この需要は辞書が立つのが正しい**。`impl P (Foo 'a 'a)` に対して `P (Foo W W)` を求めており、二つの実際の引数はどちらも W で、出力は O。spec 6.3・6.5 のどの規則でも拒否にはならない。だから選択肢 4（拒否）は採らない。言語の意味は変えない。
- 原因は表現の側にある。据え付けで予約した区間の集約の名前（purpose 0/1 の lo/hi）を、見直し（Reobserve）で端点が変わった後も使い回している。そのため、古い packet の等式 lo≃O と新しい lo≃W がぶつかる。集約は「その時点の取り込みの端点」を表すためだけの名前で、見直しをまたいで固定する意味はない。
- **採る直し: 選択肢 2**。見直しや据え付け直しで取り込みの端点が変わったら、集約の名前を新しく割り当てる（観測の版を割り当ての鍵に含める。cycle の HeadAlloc で `pair(clause.id, equation.id)` を鍵にしたのと同じ考え方）。古い集約の等式は journal に残してよい。古い名前は新しい packet から読まれなくなるので、ぶつからない。
- dot の担当:
  1. 版つきの割り当てを入れた後継の境界を作る（V8 の分類はそのまま）。source の識別子・共有・単調性・停止性と 12 の性質を移す。
  2. 230 の例が、後継の境界では辞書が立つ（EvidenceAt が中身のある形で成り立つ）ことを回帰として示す。199・202・204・206・218 の回帰も残す。
  3. そのうえで EvidenceNode を進める。
- 選択肢 3（古い証明書の持ち越し）は、2 で済まない場合だけ検討する。

## I-45（2026-11-17）一点で確定した型の記述は、見直しで付け替えない（ユーザー決定）

cycle 239 の反例（`GeneralDictionaryVersionLoopNontermination239.initial_no_acc`, `no_saturation`, `no_statement`）は正しい。I-44 の版つきの割り当てだけでは、手順が止まらない。質問ノート `notes/questions/2026-11-17-cycle239-versioned-iteration-nontermination.md` への答え:
- **ユーザーの決定（spec 6.5 に追記, 2026-11-17）: 選択肢 2 を採る**。見直し（Reobserve / observation revision）が細かくしてよいのは、まだ一点でない部分だけ。一点で確定した source の記述（descriptor）は、意味の同じ別の名前へ付け替えない。どのプログラムが通るかは変わらない。選択肢 3（版の正準化）は採らない。
- dot の担当:
  1. 見直しの規則にこの条件を足した後継の境界を作る（版つきの割り当て（I-44）と mixed trusted cache（cycle 234）はそのまま）。
  2. 239 の反復が、後継の境界では起きないことを回帰として示す。
  3. 停止性（Acc）を後継の境界で証明し直す。版の数が有限になる理由（一点の記述が固定され、ゆるい部分の細分化は有限回）を明示すること。
  4. 230・206・218 などの回帰が、後継の境界でも成り立つことを確かめる。
  5. そのうえで EvidenceNode を進める。
- 「一点で確定した記述を固定すると、本来なら得られた細分化を逃す」例が見つかったら、反例として書いて止まること（意味の完全性に関わるので、監督役がユーザーに聞く）。

## I-46（2026-11-17）コメントにも検査が拾う語を書かない

cycle 231 と 237 で、コメントの英文に `admit`（「equations admit」「trace admit one」）が入り、統合の検査（追加行に sorry / admit などがないか）で落ちた。監督役がコメントの語を言い換えて統合した（`fix/dots-231`, `fix/dots-239`）。
- Lean ファイルでは、コメントや docstring を含めて、`sorry`・`admit`・`native_decide` などの語を書かない（I-30 の再確認）。英文で「認める」と言いたいときは `have`・`allow`・`permit` などを使う。
- 公開の前に、自分の追加行に `grep -nwE 'sorry|admit|native_decide'` をかけて確かめること。

## I-47（2026-11-17）集約の名前の扱いを、停止性の議論つきで設計し直す（設計を先に）

cycle 240 の反例（`GeneralDictionaryLooseIterationNontermination240.initial_no_acc`, `no_saturation`, `no_statement`）は正しい。I-45（一点の記述を付け替えない）を足しても、非点の根の区間が新しい同値な source を参照し続けて、反復が終わらない。原因の根は I-44 にある。版ごとに新しい source の識別子を作るので、識別子が際限なく増える。これは監督役の判断の誤りで、言語の意味の問題ではない。
- 次の周は、Lean を書く前に design ノートを書くこと。次の 2 案を比べる。
  (a) **置き換え（rebase）**: 同じ計画（同じ宣言・同じ需要の識別子）を据え付け直すときは、新しい版の名前を作らない。その計画だけが持つ集約の等式（lo/hi など私的な名前の等式）を、新しい端点の等式で置き換える。私的な名前は source を制約しないので、置き換えで source の制約は失われないはず。この点の証明の見通しを書くこと。
  (b) **意味で正準化した版**: 版の鍵を、端点の名前ではなく、意味で同じものの類にする。有限個で止まる理由（たとえば ground の source の質量による上界）を書くこと。
- それぞれについて、停止性の議論の骨組み（何が減るのか、有限になるのか）を書く。199・202・204・206・218・230・239・240 の回帰がどうなるか（辞書が立つ、拒否、止まる）の見込みも書く。I-45 の条件を残すかどうかも書くこと。
- そのうえで、一方を選んで理由を書き、後継の境界の実装に入ってよい。どちらも駄目なら、その理由と反例の見込みを書いて止まること。
- 言語の意味（どのプログラムが通るか）を変えないと進めない場所が出たら、Yulang の例を付けて質問のノートに書くこと（監督役がユーザーに聞く）。

## I-48（2026-11-18）停止性（Acc）の見通しを、残りの部品より先に確かめる（監督役の判断）

cycle 241〜250 で、置き換え（I-47 (a)）の部品はよく積めている（有限 owner、実 journal 全 field、source からの初期化、有限 owner 実行器）。ただし、これまでの道（I-44・I-45）は、部品を積んだ後に停止性の反例（239・240）で倒れた。同じことを避けるため、順番を変える。
- 次の周は、Lean を増やす前に design ノートを書くこと。中身:
  1. **停止性の測度の候補**: 新しい source の一歩（Step）で何が減るのか、または何が有限集合に収まるのか。distinct owner の数、term の大きさ、予約 slot、public escape のそれぞれに上界を与える理由を書く。cycle 250 の「次の候補 3」をここで先に考える。
  2. **239・240 の反復の型**を、置き換えの下で再現しようとしてみること。再現できたら、それは反例なので、閉じた Lean の反例として書いて止まる（I-47 と同じ扱い。言語の意味の問題でなければ監督役が表現を決める）。
  3. **EvidenceNode までの残りの義務の一覧**: 停止性、mixed-time packet compiler、Permitted の導出、12 の性質と回帰（199〜240）の移植。それぞれの依存関係と、どれが一番危ないかを書く。
- 停止性の見通しが立ったら（測度が決まり、反例の型が再現しないと説明できたら）、Acc の Lean から入ってよい。packet compiler や Permitted は、その後でよい。
- 見通しが立たない場合は、その理由を書いて止まること。部品を増やす周を続けないこと。
- 言語の意味（どのプログラムが通るか）を変えないと進めない場所が出たら、Yulang の例を付けて質問のノートに書くこと（監督役がユーザーに聞く）。

## I-49（2026-11-18）停止性の設計を再開する: 有限性は source の規則から作る（監督役の決定）

cycle 251 の停止（I-48 の停止条件に当たった）は正しい判断だった。`SnapshotGrowth251`（`raw2 = union(var2, var2)` の snapshot 更新で木の高さが伸び続ける）は表現側の例で、言語の意味の問題ではない。止まったままにせず、次の方針で停止性の設計を再開すること。言語の意味（どのプログラムが通るか）は変えない。使うのは spec にすでにある規則だけである。

1. **owner（root demand identity）の有限性は、spec 6.3 の「where は head より構造的に小さい」から作る。**
   - 子の需要の型の大きさは、親の head の大きさより真に小さい。大きさは `union(P, P) → P` に縮約した後の形で数え、隠れた field を除いた後の型で数える（spec 6.3、2026-11-07 の決定）。
   - K2（spec 6 章末「確認してほしい点」、確定 2026-11-12）で、解決に入る goal は構造的な再帰型を含まない有限木だけである。
   - したがって ground な source の goal から到達できる root の型は、「source と宣言に現れる有限個の型構築子・名前」の上で、大きさが根以下の型の有限集合に入る。owner の key `(root identity, declaration id)` は、この有限集合 × 有限個の宣言から取る。実行中の再生成を数えて有限と言わないこと（251 が指摘した循環を避ける）。
2. **私的な集約の名前（lo/hi などの予約 slot）の右辺は、正規形で持つ。**
   - lo の右辺は「原子の有限集合の union」、hi の右辺は「原子の有限集合の intersection」として持つ。平らにして重複を除く（`union(P, P) → P` と同じ縮約）。
   - 原子は、source に現れる名前と端点の項（固定した有限の basis）から取る。**私的な slot の名前を原子にしない**。つまり、私的な slot の右辺は私的な slot を読まない。snapshot は、この正規形に代入してから平らにする操作とする。
   - こうすると、右辺の取りうる値は basis の部分集合の有限個に収まる。`SnapshotGrowth251` の自己参照する raw は、この不変条件で除かれる（または正規化で消える）ことを示すこと。
   - compiler の各段がこの不変条件を保つことを証明する。保てない source 到達の例が出たら、閉じた反例として書いて止まる。
3. **構成子の深さは、source の深さで抑える。**
   - 新しい構成子の項が作られるのは、同じ head の端点を併合するとき（spec 6.5: 区間の端点が不変な引数を持つときは、内側でも同じ規則で併合する。確定 2026-11-08）だけのはずである。
   - 状態に現れる型の項の深さが、source と宣言の項の深さの最大値 D で抑えられる不変条件を書いて証明する。これが偽になる source 到達の例が出たら、反例として止まる。
4. **私的な名前が外へ出ないこと。**
   - 公開する binder・output・child の target は、公開する前に public basis 上の正規形へ解いてから読む、という不変条件を書く。私的な名前が public demand identity や owner key に戻らないことを示す。
5. **測度。**
   - 上の 1〜4 が成り立てば、`(まだ据え付けていない owner の数（1 の有限集合から）, 各 owner の区間の残りの細分化の段数の和)` の辞書式で下がるはずである。
   - 細分化の段数が有限なのは、2・3 で右辺が有限個に収まり、I-45 で一点の記述は固定され、細分化は単調だからである。
   - 239・240 型の反復が、この測度の下で起きないことを回帰として示す。
- 順番: 設計ノート（1〜5 の不変条件と、それぞれの証明の見通し）→ 不変条件の Lean → Acc。packet compiler・Permitted・12 の性質の移植は、その後でよい。
- 1〜4 のどれかが source 到達の例で破れたら、閉じた反例を書いて止まる。それが表現の問題なら、監督役が直し方を決める。言語の意味を変えないと進めないなら、Yulang の例を付けて質問のノートに書くこと（監督役がユーザーに聞く）。
- 止まっている間も、設計研究は続けてよい。毎周、何を考えたかを公開すること（I-42）。

## I-50（2026-11-18）深さの上界は、出力の依存に沿った加算で取る（監督役の決定）

cycle 252 の反例（`GeneralDictionaryOutputDepthInstall252.point_public_readback_exceeds_max`）は正しい。I-49 の 3（「状態の型の深さは source と宣言の項の深さの最大値 D で抑えられる」）は誤りだった。associated output の template に入力を代入すると、深さは足し算で増える（入力 `F(Int)`、template `F(F(a))` → `F(F(F(Int)))`）。これは監督役の判断の誤りで、言語の意味の問題ではない。言語の意味（どのプログラムが通るか）は変えない。

- **採る上界: 候補 (a)。出力の依存に沿って、深さを加算で抑える。**
  - 各 owner の出力の ground な深さ ≤（その template の深さ）＋（その owner の入力の ground な深さの最大）。
  - owner の入力は、source の項か、ほかの owner の出力である。owner は I-49 の 1 で有限個（`GeneralNominalSourceOwnerCandidates252`）。
  - 出力の依存が非循環なら、深さは「source の深さ ＋ 依存の鎖に沿った template の深さの和」で抑えられる。鎖の長さは owner の数以下なので有限である。
  - 出力の依存が循環する場合は、出力が自分自身を真に含む型との等式になる。spec の K2（構造的な再帰型を含む goal は解決しない）または既存の矛盾の扱いで、拒否・報告になるはずである。そうなることを示すこと。そうならない source 到達の例が出たら、閉じた反例として止まる。
- **候補 (b) も併用してよい。** journal の生の構文は、var を参照したまま template の深さに留まる（252 の観察）。生の構文の有限性（名前と template の有限個）と、ground な readback の深さの上界（上の加算）は、別々の補題として分けて書くこと。どちらの意味の「深さ」かを、定理ごとに明記すること。
- **I-49 の 2 の残り（basis の閉包）:** 正規形の pool は、「source の名前 ＋ 有限個の owner の出力の名前（参照として。展開しない）」とする。`SnapshotNormal252` が仮定にしている「旧 atom の代入結果が pool に閉じる」を、この pool について source 到達の状態で示すこと。
- **I-49 の 4（私的な名前の漏れ）と 5（測度）:** そのまま続ける。5 では、同じ内容の見直しを除いたうえで、各 Step が新しい fact を真に増やす（または細分化の段数が真に減る）ことを示す。
- 順番: 上の上界と閉包の設計ノート → Lean → 4 → 5（Acc）。
- また上界が破れる source 到達の例が出たら、閉じた反例を書いて止まる。表現の問題なら監督役が決める。言語の意味を変えないと進めないなら、Yulang の例を付けて質問のノートに書くこと。

## I-51（2026-11-18）監査ファイルどうしを import しない

cycle 254 の `lean/Audit/Cycle254Full.lean` が `import Audit.Cycle254Usage` を書いていた。`Audit` は lake の library ではないので、統合の検査（各 `lean/Audit/*.lean` を単独で `lake env lean` にかける）で `unknown module prefix 'Audit'` になり落ちた。監督役がその import 行を消して統合した（`fix/dots-254`）。
- `lean/Audit/*.lean` は、`Yulang.*` のモジュールだけを import すること。ほかの監査ファイルを import しない。
- 使用例（Usage）の宣言も監査したいときは、使用例を同じ監査ファイルに入れるか、使用例の側に監査を書く。
- 公開の前に、自分の追加した監査ファイルを `cd lean && lake env lean Audit/<Name>.lean` で単独に通して、exit code を確かめること。

## I-52（2026-11-18）後継の Step を先に定義する（監督役の判断）

cycle 252〜257 で、有限性の部品はよくそろった。そろったのは、出力の加算深さ、owner の有限候補、正規形と固定 basis、極性別の支持、保持済み定義の除去、固定 binder fact による journal の有限 View である。ただし、調べている対象はまだ古い Step（止まらないと分かっているもの）の到達 family である。後継の Step が定義されていないので、Acc の主張を書く場所がない。
- 次の周は、**後継の Step（rebase 版）を Lean で定義する**ことを最優先にする。部分的でよい。
  - 状態: 正規化した集約（I-49 の 2、cycle 252/255 の basis）と、固定 binder fact（cycle 257）を持つ有限の表現。履歴は再生せず、保持済み定義の除去（cycle 256）で圧縮する。
  - 一歩: 古い Step と同じ観測と据え付けを行うが、集約の名前は owner の slot に置き換えで書く（I-47 (a)）。
  - 古い Step との対応: 公開モデルの射影が一致すること（健全性・完全性）。対応の補題がまだ証明できない箇所は、その場所を明記する。
- 定義ができたら、その上で次の 2 つを先に示す。
  1. I-45 の到達 family と、239・240 の反復が、後継の Step では有限回で止まること（具体的な回帰）。
  2. 一般の Acc のための測度の候補を、後継の Step の上で書く（I-48 の 1）。
- 古い Step の family について、有限 View の結果をこれ以上増やすのは、後継の Step を定義した後にすること。
- 後継の Step を定義しようとして、表現の選択が必要になったら、選択肢を design ノートに書いて先に進めてよい（表現は監督役が後で決め直せる）。言語の意味（どのプログラムが通るか）を変えないと定義できない場合だけ、Yulang の例を付けて質問のノートに書くこと。

## I-53（2026-11-19）新しいモジュールは必ず `lean/Yulang.lean` に import を足す

cycle 262〜264 で、新しい 71 モジュールが `lean/Yulang.lean`（barrel）に入っていなかった。統合の `lake build` は barrel から辿れるモジュールしか作らないので、監査が `.olean` を見つけられずに落ちた（「only audit parts import it, so lake build skips it」）。監督役が barrel に 71 行を足して統合した（`fix/dots-264`）。
- 新しい `lean/Yulang/*.lean` を足したら、同じ公開の中で `lean/Yulang.lean` の末尾に `import Yulang.<Name>` を足すこと（I-43 の「barrel 追記のみ」のとおり）。
- focused build（個別の `lean` 実行）だけでは、この抜けに気づけない。公開の前に、自分の追加したモジュールが全部 barrel にあることを確かめること。例: `for f in <追加したファイル>; do grep -qx "import Yulang.$(basename $f .lean)" lean/Yulang.lean || echo MISSING $f; done`

## I-54（2026-11-20）B4 の本線に戻る。Rust CST の接続は監督役に頼む（監督役の判断）

cycle 292〜295 は、保存済みの Rust CST を Lean の role 表へ渡す道を作った。境界の引き方（回復診断と選択の分離、範囲でなく path で所属を決める、`SourceNodeKey` を意味 ID にしない）は正しい。ただ、この道は B4 の主定理には要らない。B4 の statement は Lean の registry と goal から始まり、Rust のパーサを前提にしない。
- 次の周からは、B4 の本線に戻ること。優先順:
  1. 一般の source に対する observer / compiler の完全性（cycle 279〜281 の「棄却される割り当て」の有限性、cycle 283〜284 の索引の扱い）。
  2. 据え付け前の保留・見直しの相を含む停止性（cycle 285 の次の候補 1）。
  3. EvidenceNode の再帰（cycle 273・276・282・287〜290 の結果を一般の node へ）。
- Rust CST の実物が必要になったら、自分で Rust を探さず、質問ノート（`notes/questions/`）に「どの source をどの関数で parse した結果が欲しいか」を書くこと。監督役の環境には Rust があるので、監督役が実行して結果を `notes/verification/` に置く。
- 292〜295 の CST 関連の定理は、そのまま残してよい（凍結しない、消さない）。

## I-55（2026-11-21）停止性は B4 の証明目標から外す。健全性を先に閉じる（ユーザーの指示）

ユーザーの指示（2026-11-21）: 「健全性が知りたいのであって、停止性はそんなに気にしなくていい」。`notes/design/2026-11-08-b4-main-statement-draft.md` の主定理のうち、(1) の「飽和の停止」を証明目標から外す。言語の受理範囲は変えない（spec 6.3 の宣言検査・K2・保留の規則はそのまま）。変えるのは、Lean で何を証明するかだけ。
- 主定理の (2) は部分正当性で述べ直す: **`Sat` が停止して返したなら**、その診断ツリーは安定状態の宣言的な `Classify`（`Resolves Local d tree`）と一致する。停止は仮定にしてよい。実行の到達経路についての帰納で示し、`Acc`・測度・最大手数・停止までの手数は要らない。
- 最優先は (4) 辞書の健全性: `Classify_R(Σ*, d) = selected(k, ds)` なら、`Models(Σ*)` の任意のモデルで `ds` が構成する証拠が成り立つ。つまり、**子も選ばれる一般の EvidenceNode の再帰**を閉じること（cycle 299〜301・307・308 の結果を一般の node へ）。前提が空で成り立つ EvidenceAt は、この項の進捗に数えない。
- 次に (2)（部分正当性）と、その途中で要る observer / compiler の正しさ（I-54 の 1）。cycle 308 の 6 のとおり、現在の readback だけに依存する表現では足りないので、履歴の側の証拠を持つ表現で述べてよい。
- (3) 順序独立と (5) 偽の拒否がないことは、(4) と (2) の後。
- やめること: raw 停止性、`Acc`、停止までの手数の区間、stutter の上界、有限商の最小性、双模倣の最小クラス数。既にある定理は残してよい（消さない、凍結しない）。(4) や (2) の証明に有限性が本当に要る場所が出たら、その場所に限って仮定として置き、design ノートに書くこと。
- 各周の報告に、「(4) と (2) にあと何本の橋が要るか」を書くこと。
- (4) と (2) が閉じたら、停止性は **Lean ではなく紙の証明**で扱う（ユーザー承認 2026-11-21）。`notes/design/` に、数学の文章で「宣言検査の Paterson 的な下降と K2、補遺 5〜7 の保留（片付いていない impl の出力を入力の根拠にしない）によって、出力の補充が有限回で尽き、飽和が停止する」論証を書く。raw Step の表現・有限商・Acc は使わず、需要の木と出力の依存だけで述べる。論証が通らない場所が見つかったら、それは言語の反例の候補なので、Yulang の例を付けて質問ノートに書くこと（宣言時の拒否より遅延の案を先に）。実装では深さの上限で打ち切って報告し、その上限に当たらないことを実例で確かめる。

## I-56（2026-11-21）健全性は宣言的な状態で示し、solver はその詳細化として扱う（ユーザー承認）

cycle 316 で、現在の mixed/source 境界について `EvidenceNode` が偽になった。原因は where 端点の番地の衝突で、solver の帳簿（journal・slot・番地）の表現の誤りであって、言語の意味の誤りではない。それが「健全性の反例」として現れたのは、B4 の (4) の「状態」が solver の内部状態そのもので、`Classify`・`Models`・`Evidence` がその帳簿の上で定義されているからである。層を分ける。

1. **(4) を宣言的な境界で証明する（最優先）。** 新しい境界を定義する。状態は通常の制約・区間・モデルの集合だけで、dictionary journal・slot・番地・install の履歴を含まない。その上で `Classify`（承認済み素描のとおり、`pending`/`selected`/`ambiguous`/`rejected` と診断木）と `Evidence` を書き、次を**任意の状態**について示す。
   - `Classify_R(Σ, d) = selected(k, ds)` なら、`Models(Σ)` の任意のモデルで `ds` の証拠が成り立つ。
   - 証明は辞書の木についての帰納法で行う。核は「局所的に選ばれた候補なら、どのモデルでも実引数の中心が impl の head に合い、where の子の需要がそのモデルの捕捉で作られる」という局所補題。既存の局所 exactness（Astra の断片、cycle 309〜313 の局所選定・`HeadEquations`・捕捉の部品）を再利用してよい。
   - executor や Step には触れない。停止性も使わない。
2. **(2) を射影で述べ直す。** solver の到達状態から宣言的な状態への射影（帳簿を消し、通常制約と区間だけを残す）を定義し、「solver が停止して返したなら、その診断木は射影した状態の宣言的 `Classify` と一致する」を目標にする。cycle 316〜318 の版つき where 端点・記録行の由来・新規と再利用の混在は、この (2) の証明の部品として使う。番地の衝突のような帳簿の誤りは、ここで「仕様と一致しない」として見つかるべきもの。
3. **(1) 停止性は I-55 のまま。** (4) と (2) の後に、solver 側について紙の証明で扱う。
4. 移行の扱い:
   - 現在の mixed 境界での `EvidenceNode` の証明を続けて閉じようとしないこと。cycle 316 で偽と分かっている。
   - 既にある定理は残してよい（消さない、凍結しない）。
   - 宣言的な境界を定義するときに、どのプログラムが通るかを変える選択が必要になったら、Yulang の例を付けて質問ノートに書くこと（遅延の案を先に）。表現の選択だけなら design ノートに選択肢を書いて進めてよい。
5. 各周の報告に、「宣言的な (4) にあと何本の橋が要るか」と「(2) にあと何本か」を分けて書くこと。

## I-57（2026-11-21）凍結ファイルが切り詰めた出力で上書きされた。元に戻し、二度と書かないこと（監督役の判断）

cycle 321 の公開で、凍結している二つのファイルが、ツールの切り詰めた読み出しで上書きされていた。
- `lean/Audit.lean`: 10907 行 → 1231 行。先頭行が `Warning: truncated output (original token count: …)`、途中に `…tokens truncated…` がある。最初に入ったのは `b9835b279`。
- `lean/README.md`: 4738 行 → 699 行。`426884800` から。
どちらも I-43 などで凍結したファイルで、変更してはいけない。監督役が `fix/dots-321` で `integration/m1-final` の版にバイト単位で戻して統合した。cycle 321 のほかの変更（新しい `lean/Yulang/*.lean`・`lean/Audit/*.lean`・barrel・notes）はそのまま統合した。
- 次の公開で、`work/dots-main` の `lean/Audit.lean` と `lean/README.md` を `integration/m1-final` の版にバイト単位で戻すこと（`git checkout origin/integration/m1-final -- lean/Audit.lean lean/README.md` と同じ結果）。
- 以後、この二つのファイルを読み書きしないこと。新しい監査は `lean/Audit/<Name>.lean`、説明は `notes/` に書く。
- 大きなファイルを、切り詰められうる経路（ツールの表示出力など）で読んで書き戻さないこと。公開の前に、変更したファイルに `truncated output` や `tokens truncated` が入っていないかを確かめること。例: `git diff --name-only <前回の公開> HEAD | xargs grep -l -e 'truncated output' -e 'tokens truncated'` が何も出さないこと。
- 公開の前に、`git diff --stat <前回の公開> HEAD -- lean` で、既存ファイルから行が消えていないことも確かめること（`tools/verify-lean.sh` の「削除行なし」と同じ検査）。

## I-58（2026-11-22）反復する impl 変数の実値一致は、選定が足す等式から取る（監督役の判断、既決の仕様の指摘）

cycle 320（`Repeat320.realization_not_universal`）、327、328（`OpaqueRepeatCut328.exact_cut`）で、同じ impl 型変数が二か所に現れるとき、端点の観測だけからは「同じ実値」が出ないことを確かめた。これは正しい。そのうえで、仕様はこの点をすでに決めている。

- `spec/06-roles.md` 6.5（確定 2026-11-16、ユーザーの決定「選んだら等式を足す」）: 候補の照合は区間の端点と既知の頭だけで行い、中心は見ない。`impl R 't 't` のように同じ型変数を二度使う impl を**選んだら**、その位置の実際の引数（中心）どうしが等しいという等式を制約として**足す**。足した等式がほかの制約と矛盾すれば、その需要の拒否（型エラー）。共有を示せないことを理由に保留にはしない。
- 同じ節の「同じ入力の需要はまとめる」（2026-11-12）と「実際の引数の名前（中心）は明示して持つ」（2026-11-14）も合わせて読むこと。

宣言的な (4) での扱い:
1. `Classify_R(Σ*, d) = selected(k, ds)` の Σ* は**安定した状態**なので、選定が足した中心の等式（反復する型変数ごと、選ばれた各節点ごと）は Σ* の通常制約に含まれる。反復する binder の実値一致は、端点や全モデルの同値から導かず、この等式の帰結として読むこと。
2. 宣言的な分類では、`selected` の定義に「選ばれた候補の反復変数ごとの中心等式が状態に含まれる（または状態から帰結する）」を入れてよい。これは新しい規則ではなく、上の既決の規則の形式化である。等式を足す前の状態で選ばれたと判定する定義にはしないこと。
3. 等式が矛盾する場合は `rejected` 側の理由に入る。これも既決（足した等式の矛盾は型エラー）。
4. (2) では、solver が選定のときにこの等式を実際に足すことを、射影の不変条件として扱う。

この指摘で受理範囲は変わらない。読みが違うと思う点、または上の規則だけでは決まらない点（たとえば一方の位置が名前つきの出力のとき）が出たら、Yulang の例を付けて質問ノートに書くこと。

## I-59（2026-11-22）cycle 321 の質問への回答と、spec の更新

- `notes/questions/2026-11-21-cycle321-k2-with-unsupported-lower.md` に回答が付いた。ユーザーの決定は「2」（K2 で拒否）。展開は保留したまま、普通の等式（片付いていない impl の出力の等式を含む）から需要の根が名前のない構造的な再帰型だと分かるなら、その需要を `rejected`（K2）とする。B4 草稿の補遺 9、spec 6.3 に記録した。宣言的な `Classify` の rejected の理由にこの場合を入れること。
- 回答が遅れた（8 周）のは監督役の見落とし。以後、質問ノートを書いた周の報告には、質問ノートのパスを「質問」の見出しで書くこと。
- `integration/m1-final` の `spec/06-roles.md` を yulang3 の正本に合わせた。これまで integration の spec には 2026-11-14〜11-17 の決定（名前なし区間は入力・名前つきは出力、合流した出力要求の矛盾は合流した需要の拒否、型変数を共有する impl を選んだら実引数の等式を足す、確定した記述は付け替えない）が入っていなかった。以後の周はこの版を読むこと。

## I-60（2026-11-22）宣言的な (4) の最後の橋を切り直す: 「頭が分かる」を支持付きの読みで定義する（監督役の判断）

cycle 320〜333 で、(4) の残り 1 本はずっと同じ形だった。「独立に定義された承認済みの安定 `Local.selected` から、それが使った頭・捕捉・子・出力の支持付きの読み（named / inline / 区間射影）と receipt が得られる」。これは観測の完全性の主張で、形・モードを一つずつ広げても閉じていない（333 でも「安定な通常伝播そのものから導く一般橋」が残り）。切り方を変える。

1. **宣言的な分類の「頭が分かる」「捕捉が分かる」を、支持付きの読みそのもので定義する。** 承認済みの規則（spec 6.3「保留: 下界の頭が未解決」、補遺 1・3〜8）は、頭が**観測できたとき**に候補を調べ始める、と言っている。だから宣言的な `Classify` の `selected` は、各節点で使った頭・捕捉について、cycle 321〜333 で作った支持付きの読み（`Read`・`Spine`・区間射影、有限の支持表と receipt を含む）を**証人として持つ**判断として書いてよい。読みのない頭は「分かっていない」（保留側）。
2. **(4) はこの分類について示す。** 証人つきの `selected` なら、どのモデルでも辞書の証拠が成り立つ。cycle 320 の辞書の帰納と、321〜333 の読みから実中心・子・固定出力・I-58 の等式を作る部品は、そのまま使えるはず。ここを先に一本の定理として閉じること。
3. **旧 `Local`（証人なしの定義）との対応は (4) から外し、別の補題にする。** 「旧 `Local.selected` なら証人つきの `selected` が存在する」と、その逆を、別の定理として扱う。これは (2) の側（solver が実際にこの読みを持っているか）と同じ種類の問題で、(2) の射影の不変条件として述べてよい。
4. **対応が成り立たない例が出たら。** 旧 `Local` は選ぶが支持付きの読みが存在しない、またはその逆の例が見つかったら、それはどのプログラムが通るかの違いになりうる。Yulang の例を付けて質問ノートに書くこと（遅延の案を先に。ノートを書いた周の報告には「質問」見出しでパスを書く）。旧 `Local` に合わせて分類を広げることは、自分で決めないこと。
5. 報告の本数は、「(4)（証人つきの分類）」「旧 `Local` との対応」「(2)」の三つに分けて書くこと。

## I-61（2026-11-22）cycle 334 の質問への回答: 中心の行に根拠がなくても、根拠のある端点から選ぶ（ユーザーの決定「2」）

- `notes/questions/2026-11-22-cycle334-record-center-withheld.md` に回答が付いた。ユーザーの決定は「2」。下端・上端の頭が根拠つきで分かっていれば、実際の引数（中心）の行の由来が片付いていない impl の出力だけでも、中心の行は使わずに端点から照合し、捕捉を区間として作って選ぶ（record の `{x: 'a, ..'rest}` なら、`'a` は両端の `x` の型の区間、`'rest` は両端の残りの区間）。spec 6.5「実際の引数の名前（中心）は明示して持つ」の下と、B4 草稿の補遺 10 に記録した。根拠は同じ節の既決の規則「解決は区間の端点で行い、中心は型変数の使い回しを表すためだけに使う。共有の情報を失ったことを理由に需要を保留にする規則は足さない」。
- 証人つき分類（cycle 334）への反映:
  1. 「承認済みの区間射影」に、根拠のある両端から record の可視 field と残り（open/closed とも）を区間として捕捉する射影を入れる。中心の行の支持は要らない。
  2. `GeneralDeclarativeWitnessCut334` の状態は、この射影で `selected` になるはず。旧 `Local59 / Staged` との食い違いは、この点については消える見込み。違ったら報告すること。
  3. 反復する型変数がある候補では、端点からの捕捉に加えて、I-58 の中心の等式を足す（等式が矛盾すれば拒否）。中心の行がないことを理由に保留にはしない。
  4. 「中心の行がないから保留」が残るのは、端点の頭自体に根拠がない場合（補遺 7）だけ。
- 宣言的な (4) が証人つき分類で閉じたこと（`GeneralDeclarativeWitnessClassify334.dictionary_sound`）は確認した。射影を足したあとも、同じ定理が通ることを確かめること。

## I-62（2026-11-22）cycle 340 の質問への回答: 旧 `Local` には合わせない。旧 `Local` との対応の群をやめる（監督役の判断）

- `notes/questions/2026-11-22-cycle340-backed-join-read.md` の件は、言語の意味ではなく証明の構成の判断なので、監督役が決める。意味は spec 6.3（2026-11-07、ユーザーの決定「合流前の変数は、合流した後の payload をそのまま捕捉する」「plain の型変数以外は、合流後の payload を分割しない」）で確定していて、支持付きの正規化読み（同じタグの合流を含む）で `selected` にする証人つき分類が正しい。旧 `Local` が pending にするのは旧定義の不足であり、旧に合わせて分類を狭めたり、旧へ正規化読みを後付けしたりしない。
- 旧 `Local` は spec ではなく、以前の Lean の定義にすぎない。I-60 の 3 で「旧 `Local` との対応」を別の群にしたが、これを**目標から外す**。今後の比較の相手は、証人つき分類（宣言側）と実 solver（(2)）の二つだけにする。旧 `Local` と証人つき分類が食い違う例は、spec の文面で判定し、spec が決めていない場合だけ質問ノートにする（遅延の案を先に）。
- (2) の射影の不変条件は、旧 `Local` ではなく証人つき分類（I-58 の等式、I-59 の K2、I-61 の端点からの捕捉、今回の同じタグの合流を含む）に対して述べること。
- 報告の本数は「(4)（I-61 追補を含む）」と「(2)」の二つでよい。既存の旧 `Local` 関連の定理は残してよい（消さない）。

## I-63（2026-11-23）(2) と I-61 追補を「証人の検査器」で閉じる。既存の実行器から作者の証拠を掘り出すのをやめる（監督役の判断）

- 背景: cycle 335 から 347 まで、残りの本数（(4) 1 群、(2) 2 群）が動いていない。cycle 346・347 の報告どおり、元の実行器（C316 の停止 root）は、修正版の物理作者アドレスも release の証拠も持っていない。持っていない証拠を、その実行器の任意の成功停止から取り出すことはできない。この方向の作業はここで止める。
- 新しい構成（表現と証明の計画なので、監督役が決める。言語の受理範囲は変えない）:
  1. **証人の型と検査器。** `GeneralDeclarativeWitnessClassify334.dictionary_sound` が使う証人（`Checked r`・`Coverage r i`・`Declared r d` の材料）を、nested/compound・非点・open/closed の読みまで含む有限のデータ `Witness` として定義する。宣言的な状態と `Witness` を受け取る決定可能な検査器 `checkWitness` を書く。
  2. **検査器の健全性。** `checkWitness s w = true → Checked r ∧ Coverage r i ∧ Declared r d`（同じ宣言的な状態、同じモデル）を示し、334 の定理につなぐ。検査器は全階層を自分で確かめるので、I-61 追補の「一般の producer」は健全性には要らない。
  3. **出力の一致も検査する。** solver の出力（診断の木、順序付きの辞書、固定した出力）が、証人から決まるものと一致するかどうかも検査器が確かめる。主定理の形は「solver が `(出力, 証人)` を返し、検査器が通るなら、その出力は DictionarySound を満たし、証人つき分類と一致する」。
  4. **実行器は証人を出すように拡張してよい。** 実行器（Lean のモデル）の journal や結果に、使った作者・版・release の記録を足すのは実装の層の変更なので許可する。元の C316 実行器がそれを出すことは示さなくてよい。旧 `Local` は I-62 のとおり目標外。
- 完全性は後に回す。「Classify が selected と言うなら、実行器が検査を通る証人を必ず出す」（NoFalseRejection 側、producer の一般性）は、健全性の群とは別の群として、健全性を閉じたあとに扱う。停止性も引き続き目標外。
- 報告の本数は次の三つに数え直す: (S1) 証人の型と検査器の定義、(S2) 検査器の健全性と 334 への接続（出力の一致を含む）、(C) 完全性（後回し）。既存の (4)・(2) の定理は消さず、使えるものは S1・S2 に流用してよい。
- 最初の周では設計ノートを書き、`Witness` に入れる項目の一覧と、検査器が各階層で何を確かめるかを示すこと。大きな Lean はそのあと。

## I-64（2026-11-23）宣言された分散を宣言側（334）に入れる。typed carrier と旧 C334 の橋は作らない（監督役の判断）

- cycle 355 の報告どおり、C334 の `Coverage` は、構成子を primitive か invariant に限っている。spec 6.3 の宣言された分散（共変の unary 構成子と、合流後の payload の丸ごと捕捉）は、この宣言側のモデルの外にある。つまり、334 の `dictionary_sound` が閉じたのは、primitive と invariant の構成子だけの範囲になる。
- 宣言側を正本にする方針（I-56）なので、直すのは宣言側にする。typed carrier の結果を旧 C334 の前提に読み替える橋は作らない。
  1. C334 の宣言的な状態と分類を、宣言表の種類と分散（primitive / invariant / 宣言された covariant・contravariant）で引くように一般化する。既存の primitive・invariant の場合は特別な場合として残す。
  2. 一般化した分類について `dictionary_sound` を示し直す。既存の 334 の証明は流用してよい。
  3. S2 の目標は、一般化した分類と検査器の結果の一致にする。cycle 353〜355 の typed の結果は、この一般化した分類の共変の場合として接続すること。
- 本数の数え方は変えない（S1・S2・C）。上の 1・2 は S2 の一部として数え、閉じたら報告に書くこと。
- 分散の意味そのもの（どの位置が共変か、合流の扱い）は spec 6.3 で確定している。spec が決めていない場合だけ、質問ノートにすること。

## I-65（2026-11-23）健全性を一つの定理で閉じる。例を増やす前に、検査器を一つにまとめる（監督役の判断）

- 背景: cycle 349 から 364 まで、本数は S1・S2・C がそれぞれ 1 群（部分）のまま動いていない。各周の中身は「扱える範囲を一つ広げて、その範囲で正の例と偽物の例を通す」になっている。範囲は確かに広がったが、このやり方では健全性がいつ閉じるのかが決まらない。
- 要点: 証人の検査器は、扱えない形を `false` で返してよい。`false` を返す場合は、健全性の定理の前提が成り立たないので、そのまま正しい。したがって**健全性は、扱える範囲の広さと関係なく、一つの定理として今すぐ閉じられる**。扱えない形が残ることは完全性（C）の問題であって、健全性の問題ではない。
- 次の三つを、この順で、例を増やさずに閉じること。
  1. **一般化した宣言側の健全性（I-64 の残り）。** 種類と分散の表で引く宣言的な分類について、`dictionary_sound` を任意の状態・任意のモデルで示す。範囲を限った版（scoped）ではなく、全称の一つの定理にする。primitive・invariant は特別な場合として含める。
  2. **一つの検査器。** cycle 349〜364 の範囲ごとの検査器を、一つの `check : Problem → Result → Witness → Bool` にまとめる。形で振り分け、扱えない形は `false` を返す。新しい検査の論理は足さない。
  3. **一つの健全性定理。** 任意の `P r w` について、`check P r w = true` なら、同じ宣言的な状態の任意のモデルで、1 の分類の証拠が成り立ち、返された診断木・辞書・固定出力が一致する。範囲ごとに示した既存の定理を、振り分けの各場合で使う。
- 1〜3 が閉じたら、S1 と S2 は閉じたとして報告してよい。そのあとの本数は C だけになる。C は「宣言側の分類が受理するのに、`check` が `false` を返す形」の一覧として数える。構文の形ごとに 1 行で、閉じた行と残りの行が分かるようにすること。
- 1〜3 の間は、新しい fixture は統合した検査器の試験としてだけ足すこと。範囲を広げる作業は、3 が閉じてから C の一覧に沿って進める。
- 報告の「残り」には、1・2・3 のどれが閉じたかを毎周書くこと。最初の周で 1〜3 の定理の形（Lean の文）を設計ノートに固定し、以後はその文を変えずに証明を進めること。
- 停止性と旧 `Local` は引き続き目標外。言語の受理範囲は変えない。

## I-66（2026-11-24）I-65 の 1 を、補題の一覧で数えられるようにする（監督役の判断）

- 背景: I-65 の 1（固定した `dictionary_sound`）は cycle 365 から開いたままで、報告の「残り」はここ数周ほぼ同じ 3 点（早い native の入口、許された位置の K2・優先順位、選んだ出現の受け取り）になっている。実行環境の停止（369〜375 頃）はやむを得ない。ただ、このままでは 1 があとどれだけで閉じるかが分からない。
- 次の周の最初に、設計ノート `notes/design/dots-cycle-<N>-i65-step1-skeleton.md` を一つ書くこと。中身は次のとおり。
  1. 固定した `dictionary_sound` の証明を、名前つきの補題の組み合わせとして上から書き下す。補題ごとに Lean の文（仮定と結論）を書く。最上段の組み立ては、補題をそのまま使えば閉じる形にする。
  2. 補題ごとに状態を一つ付ける。**証明済み**（integration 上の定理名とファイル）、**未証明**、**一部**（証明済みの範囲と残りを 1 行で）のどれか。cycle 365〜378 の既存の定理は、使えるものをここに割り当てる。
  3. 未証明の補題の数を、最後に 1 行で書く。
- 以後の報告の「残り」は、この一覧の未証明・一部の行で書くこと。補題を足す・分ける・言い換えるときは、理由を 1 行で一覧に書き、最上段の文は変えないこと。
- 一覧を書く周は、新しい Lean を急がなくてよい。一覧が書けたら、未証明の補題を一つずつ閉じていく。
- 骨組みを書く途中で、最上段の組み立てが既存の補題では閉じないと分かったら、それも一覧に書くこと（足りない補題として数える）。これは失敗ではなく、残りの量が分かったという成果として扱う。
- 2・3 は引き続き 1 のあと。停止性・旧 `Local`・旧 C334 への橋は対象外。言語の受理範囲は変えない。

## I-67（2026-11-24）S01: release・作者・版は宣言側の状態に入れない。宣言側の「完了」は分類から帰納的に定める（監督役の判断）

- 背景: cycle 381・382 とも、S01（`classifies_unpacks_actual_source`）の残りとして同じ障害を挙げている。C365 の `State` からは、実際の completion/release manifest、作者、有効な版を一意に戻せない。だから入口で外から与えるしかない、という状況になっている。
- 判断: これは `State` に足りない情報があるのではない。**宣言側の分類が solver の概念（release・作者・版・manifest）に頼っている**ことが問題である。I-56 の層の分け方では、宣言側の状態は制約・区間・モデルだけを持ち、solver の journal・番地・release は持たない。release の manifest を `State` に入れて S01 を閉じることはしない。
- やること:
  1. 宣言側では、「出力が片付いている（完了している）」を、solver の release ではなく分類そのものから定める。出力を作る要求が、同じ状態で `.selected d'` に分類されていれば、その出力は完了している、とする。これは分類の導出に沿った帰納（または有限の導出木の上の定義）として書く。spec 6.3 の補遺 7（片付いていない出力の保留）と I-59 の K2 は、この宣言的な完了を使って述べる。
  2. `Classifies` と S01 の入口は、この宣言的な完了だけを見る。作者・有効な版・manifest・grant は、宣言側の導出には現れない。
  3. release・作者・版・manifest は、**検査器と証人の層**（I-65 の 2・3）に置く。検査器は、証人が持つ release の記録が、宣言側の完了（1 の定義）と一致することを確かめる。cycle 351〜379 の release・作者・版の定理は、そこで使う。
  4. 1 の定義に合わせて、C380 の補題の一覧の S01〜S03 の文を見直してよい。見直したときは、理由を一覧に 1 行で書くこと。固定した `dictionary_sound` と `check_sound` の文は変えない（`Classifies` の定義の中身を宣言的にするのは、文の変更ではない）。
- 宣言的な完了の定義で、spec が順序に依存する（どの順で解いたかで受理が変わる）と読める箇所に当たったら、それは意味論の問題なので、質問ノートに書いて止めること（遅延の案を先に）。監督役が owner に聞く。
- 報告の「残り」は、引き続き C380 の一覧の行で書くこと。

## I-68（2026-11-24）補題は一つずつ閉じる。下から、依存の少ない順に（監督役の判断）

- 背景: C380 の一覧ができてから cycle 381〜384 の 4 周で、Lean は毎周 500〜1300 行増えた。それでも「残り 13 = 未証明 3 + 一部 10」は一度も減っていない。各周が 13 件の多くに少しずつ手を入れ、どれも閉じないまま「一部」の範囲だけが広がっている。cycle 349〜364 で本数が動かなかったのと同じ形である。
- やり方を次のように変える。
  1. 一覧に**依存の順**を書く。各補題が、一覧のどの補題を使うかを 1 行で書き、使う補題のない（または証明済みの補題だけを使う）ものから順に番号を振る。
  2. **一周に一つ**、その順で先頭の補題を選び、一覧に書いた Lean の文をそのまま証明して閉じる。文を弱める・場合を限る版は「閉じた」に数えない。ほかの補題には手を入れない。
  3. 閉じられないと分かったら、その補題を**分ける**（例: S12 を S12a・S12b に）。分けた理由と、それぞれの文を一覧に書き、分けた片方を次の周に閉じる。分けることは失敗ではなく、残りの量が正確になったという成果として扱う。
  4. 報告の冒頭に 1 行で「この周に閉じた補題: S__（定理名）」または「閉じた補題なし・分けた補題: S__ → S__a, S__b」を書く。
- 候補として、S12（`general_tree_sound`）と S13（`general_meaning_to_dictionary`）のように木の上の帰納で閉じるものは、S01（全候補の判定）より依存が少ない見込みがある。順番は一覧の依存の順で dot が決めてよい。
- 固定した `dictionary_sound` と一覧の最上段の組み立ては変えない。停止性・旧 `Local`・旧 C334 への橋・fixture の追加は引き続き対象外。言語の受理範囲は変えない。

## I-69（2026-11-24）S13 の芯: 分ける前に「足りない事実」を一文で書く（監督役の判断）

- 背景: S13 は cycle 385 から、S13 → S13a/S13b → S13ba/S13bb → S13bba/S13bbb → S13bbba/S13bbbb と 4 回分かれた。閉じたのは S13a・S13ba・S13bba で、どれも分けたときの構造側だった。辞書の証拠を実際に作る芯は、名前を変えて持ち越され続けている。cycle 391 の報告にも、native については「source body からこの型つきベクタが出ることを、仮定なしには示していない」とある。
- これは、補題が大きすぎるのではなく、**前提から導けない事実がある**兆しだと見る。分け続けても、その事実はどこかの葉に残る。
- 次の周は、S13bbba・S13bbbb を証明する前に、設計ノートに次を書くこと。
  1. それぞれについて、**今ある前提（`Classifies` の定義、`LocalSource`、S13a・S13ba・S13bba の結論、`Fits`）から導けない事実**を一文で書く。例: 「選ばれた出現の本体から、native の型つきベクタが fixed target に書かれること」。
  2. その事実が、本来どこから来るべきかを一行で書く。次のどれかになるはず。
     - (a) **`Classifies`（宣言側の局所規則）が与えるべきなのに、定義に入っていない。** → `LocalSource` / `Classifies` の定義に足す。固定した `dictionary_sound` の文は変わらない。宣言側の規則の中身を spec に合わせて完成させる作業として扱う。
     - (b) **`DictionaryEvidence`（結論）が要求しすぎている。** spec が求めていないことまで結論に入っている。→ 監督役に報告して止める（固定した文の変更になるので、監督役が判断する）。
     - (c) **spec が決めていない。** → 質問ノートにして止める（遅延の案を先に）。
     - (d) 導けるが証明が長いだけ。→ そのまま閉じる。
  3. (a) なら、その周は定義を足して S13bbba か S13bbbb を閉じること。(b)(c) なら、報告の冒頭に書いて止めること。
- S13 系統は、これ以上分けないこと。分けるなら、上の 1・2 を書いたうえで、足りない事実がどちらの葉に残るかを明記すること。
- 固定した `dictionary_sound`・`check_sound` の文と最上段の組み立ては変えない。言語の受理範囲は変えない。

## I-70（2026-11-25）S13bbba: 型の種類の出どころを spec の文で指す。型推論の仕事は B4 の入力にする（監督役の判断）

- 背景: S13bbba は cycle 392〜396 の 5 周続いている。残りの書き方はここ 2 周ほぼ同じで、「同じ子の元の Body を型つきの環境で評価して、その型の種類を where の slot に渡す規則」「既定値・行の型の種類」「混ざった複合と既存の `.declared` の受け取りの対応」になっている。cycle 396 では Lean が増えていない。
- 懸念: 「where の本体を型つきの環境で評価して型の種類を得る」は、**式の型付けそのもの**である。これは role 解決（B4）の規則ではなく、型推論（spec の推論の章、B6 の対象）の仕事である。B4 の宣言側でこれを作り始めると、型推論を B4 の中に作り直すことになり、終わらない。
- 次の周の最初に、設計ノートに次を書くこと。
  1. 残りの規則（上の 3 つ）それぞれについて、それを定める **spec の文**（`spec/` のファイルと見出し、または引用）を指す。
  2. その文が「role 解決の規則」か「式の型付け（推論）の結果」かを 1 行で分類する。
- 判断の方針:
  - **型付けの結果に当たるもの**（where の本体・既定値・行の型の種類など）は、B4 では**入力**にする。宣言側の `State` か要求に、推論が与えた型つきの情報（各出現の型の種類）として持たせ、`Fits` / `Classifies` はそれを読むだけにする。推論がそれを正しく与えることは B6 の義務として、別に書いておく。これは表現と証明の境界の判断であり、言語の受理範囲は変えない。
  - **role 解決の規則に当たるもの**は、これまでどおり `Classifies` の局所規則として定義し、S13bbba を閉じる。
  - spec の文が見つからない、またはどちらとも読めないときは、質問ノートにして止めること（遅延の案を先に）。
- 入力に移した場合は、C380 の補題の一覧と固定した文の前提を見直してよい。`State` に推論の結果を持たせるのは `dictionary_sound` の文の変更ではない（`State` の中身の変更）。見直しの理由は一覧に 1 行で書くこと。
- そのあと、S13bbba を閉じることを最優先にする。分けないこと。

## I-71（2026-11-25）cycle 397 の質問への回答: 内部ベクタの対応は仕様ではない。B6 の型つき RHS をそのまま持つ（監督役の判断）

- `notes/questions/dots-cycle-397-mixed-rhs-declared.md` への回答。これは言語の意味の質問ではなく、Lean の内部表現の選び方なので、監督役が決める（質問ノート自身もそう書いている）。
- 答え: **C386 の `LiteralWriteSyntax`（Pattern 全体と `List Argument`）の並べ方は、spec が定めるものではない。** 以前の Lean が選んだ内部表現にすぎない。record・join の中に declared nominal が入れ子になった RHS（例 `type out = {item: box 'a}`）を、そのベクタのどの位置・順序に置くかを定める正本はない。探さなくてよい。
- 方針:
  1. 保留案のとおり、B4 は B6 が渡す**元の出現つきの型つき RHS**を入力として読み、同じ role の選択・出現・出力番号・固定先への等式を照合する。
  2. 混在の RHS は、平らなベクタに直さず、**B6 が渡す型の項（木）のまま**持つ。意味は spec/04-types・spec/10-inference-core §10.2 の型の意味で、同じモデルの中で比べる。C386 の `.declared` ベクタへの機械的な対応は、証明の義務から外す。
  3. 既存の C386 の受け取りが混在の RHS を表せないなら、受け取りの表現のほうを広げて（型の項を直接持たせて）よい。古い表現に合わせて意味を削らないこと。
  4. 言語に型の判定や拒否を増やさない。fixture も足さない。
- 報告について: cycle 397 と 398 は、通常の報告（`notes/handoff/dots-cycle-N.md`）がないまま次の周に移っていた（398 は時間上限による中間引継ぎだったと 399 の報告にある）。時間上限や実行環境の停止で周が途中で終わるときも、**毎周、最低限の報告を書いてから終えること**。中身は「閉じた補題」の 1 行、Lean の変更の有無、次にやること、の 3 行でよい。
- このあとは S13bbba を閉じることを最優先にする。分けないこと。

## I-72（2026-11-25）固定した文と補題の一覧を Lean に書く。最上段の組み立てを今すぐ証明する（監督役の判断）

- 背景: 監督役が integration（`2ba2d98ba` 時点）を確かめたところ、I-65 で固定した `dictionary_sound` / `check_sound` に出てくる `Classifies`・`DictionaryEvidence`・`ClassifiedAs`・`ReportEvidence` は、**Lean に定義がない**（`git grep` で定義が見つからない。`LocalSource` は C386 の `judgment.localRule` の別名だけ）。固定した文と C380 の補題の一覧は、どちらも設計ノートの中の文章でしかない。`GeneralDeclarativeI65*` には 113 ファイルがあるが、目標の型が決まっていないため、S13bbba のように「局所規則に何を入れるか」を毎周作り直すことになっている。cycle 392〜401 の 10 周は、これが原因だと見る。
- 次の周は、新しい証明より先に、次を Lean に書くこと（`sorry` などは使わない。文は `def … : Prop` として書く）。
  1. **目標の型を定義する。** `State`（C365 にあるもの）・`Request`・`Dictionary`・`Model`・`Fits`・`Classifies`・`DictionaryEvidence` を一つのモジュールで定義する。`Classifies` は宣言側の局所規則の帰納的な定義で、I-67（完了は分類から帰納的に）・I-70（型推論の結果は `State` が持つ B6 の入力として読むだけ）・I-71（混在 RHS は B6 の型の項のまま）に従う。規則の中身で spec が決めていない箇所に当たったら、質問ノートにして止める。
  2. **固定した文を `def` で書く。** `def DictionarySound : Prop := ∀ s q d, Classifies s q (.selected d) → ∀ m, Fits s m → DictionaryEvidence s m q d`。I-65 の 2・3 も同様に（`check` は 2 で定義するので、3 の文は 2 のあとでよい）。
  3. **補題の一覧を `def` で書く。** C380 の一覧の各行（S01〜S12、S13a・S13ba・S13bba・S13bbba・S13bbbb）を、それぞれ `def S__ : Prop := …` として書く。すでに閉じたもの（S13a・S13ba・S13bba）は、既存の定理からその `def` を証明する。
  4. **最上段の組み立てを証明する。** `theorem assemble : S01 → S02 → … → DictionarySound` を今すぐ証明する。これが通らないなら、一覧に足りない補題があるので、足して数え直す。
- 以後の数え方: 「閉じた」とは、3 の `def S__` を結論とする `theorem` が integration にあることだけを指す。報告の冒頭の 1 行には、その定理名を書く。設計ノートの文章だけの変更は、一覧の変更として理由を書く。
- この周は S13bbba の続きより、1〜4 を優先する。4 が通れば、残りの数は Lean の上で確かめられるようになる。
- 固定した文の意味（全称・前提・結論）は変えない。言語の受理範囲は変えない。停止性・旧 `Local`・旧 C334 への橋・fixture の追加は対象外。

## I-73（2026-11-25）規則の和で I-65 の 1 を閉じ、2・3 へ進む。範囲を広げるのは C に回す（監督役の判断）

- 現状（`97d56e91f` で監督役が確認）: `DictionaryEvidence s m` は `SourcePrimitives` に依存しない意味の証拠として定義されている（C402 `GeneralDeclarativeI65I72FixedGoal402.lean`）。そのうえで、cycle 403〜406 は範囲ごとの具体的な規則 `R` について `DictionarySound R` を示している（`variable_native_priority_dictionary_sound403`、`repeated_variable_dictionary_sound403`、`completed_input_dictionary_sound404`、`finite_completed_choice_dictionary_sound404`、`completed_native_priority_dictionary_sound404`、`dictionary_sound_for_authored_native_unary405`、`scoped_dictionary_sound406` など）。
- 判断: 結論が `R` に依存しない意味の証拠なので、**`DictionarySound R` はどの `R` についても完全な健全性の定理**である。`R` が spec より狭くても、狭い分は「受理すべきものを落とす」完全性（C）の問題で、健全性は損なわれない（I-65 の要点と同じ）。だから、範囲を一つずつ広げて健全性を示し直す作業は、ここで止める。
- 次の周でやること:
  1. **規則の和。** これまでの具体的な規則を一つの `R₀` にまとめる（各局所規則の選言、または規則の列）。各規則の健全性から `DictionarySound R₀` を示す。和で閉じない（ある規則の選択が別の規則の前提を壊す、など）なら、その理由を一文で書く。
  2. **I-65 の 1 を閉じたとして報告する。** 「`DictionarySound R₀` を integration に置いた」ことを、I-65 の 1 の完了とする。C380 の一覧の残りの行は、`R₀` を spec 全体へ広げる作業として C の一覧に移す（健全性の残りとは数えない）。
  3. **I-65 の 2 に進む。** `check` の `Classifies` を `Classifies R₀` として、検査器を一つにまとめる。扱えない形は `false`。
  4. 3 のあと I-65 の 3（`check_sound`）。
- C の一覧（`R₀` が spec より狭いところ）は、構文の形ごとに 1 行で書いておく。広げる作業は、2・3 が閉じてから、この一覧に沿って進める。広げるときも、`R₀` を大きくした `R₁` について `DictionarySound R₁` を示せばよい。
- `R₀` に入れる規則は、spec の規則として正しいもの（spec より厳しい・狭いのはよいが、spec にない受理を足さない）に限る。spec にない受理が必要になったら、質問ノートにして止める。
- 固定した `DictionaryEvidence` の定義と、`dictionary_sound` の全称の形は変えない。停止性・旧 `Local`・旧 C334 への橋は対象外。

## I-74（2026-11-25）I-65 は閉じた。次は C の一覧を作り、spec の例から順に検査器の範囲を広げる（監督役の判断）

- 確認: cycle 407 の `dictionary_sound_R0`、cycle 408 の `check`（一つの検査器）と `check_sound` で、I-65 の 1・2・3 は閉じた。`check_sound` の文は C365 で固定したものと同じ。監督役もこれを I-65 の完了とする。
- 現状の範囲: `check` が `true` を返すのは、引数のない一候補の選択と、根の K2 による拒否の 2 種類だけ。健全性の定理は完成しているが、使える範囲は狭い。ここからは C（完全性・範囲）の作業になる。
- やること:
  1. **C の一覧を作る。** 設計ノート `notes/design/dots-cycle-<N>-c-coverage.md` に、spec が受理する（または特定の診断で拒否する）のに `check` が `false` を返す形を、構文の形ごとに 1 行ずつ書く。各行に、その形が出てくる spec の例（`spec/` の節、または `lean/SpecExamples.lean` と `notes/handoff/2026-11-08-m1-spec-examples-conformance.md` の例）を添える。C380 の一覧から C に移した行もここに入れる。
  2. **順番は spec の例から。** spec の例に出てくる形を先にする。例のない形は後ろに回す。
  3. **一行ずつ広げる。** 一周に一行、次の三つを同時に行う: (a) `R₀` に局所規則を足した `Rₙ₊₁` と `DictionarySound Rₙ₊₁`、(b) `check` にその形の分岐を足す（ほかの分岐は変えない）、(c) `check_sound` を保つ。三つそろったら、その行を閉じたと数える。
  4. 報告の冒頭の 1 行は「この周に閉じた C の行: …（定理名）」にする。最後に C の残りの行数を書く。
- 規則を足すときは、spec より厳しい・狭いのはよいが、spec にない受理は足さない。spec にない受理が要る、または spec が決めていない形に当たったら、質問ノートにして止めること（遅延の案を先に）。
- solver（実際の推論器）が、受理するプログラムについて `check` を通る証人を必ず作ること（NoFalseRejection 側）は、この一覧の範囲がある程度広がってから扱う。停止性は引き続き紙の証明に回す。
- 固定した `DictionaryEvidence`・`dictionary_sound`・`check_sound` の文は変えない。

## I-75（2026-11-26）C14: 端点からの選択の意味を、射影の証拠として足す（監督役の判断）

- cycle 422 の結果（`primitives_only_cannot_add_genuine_nonpoint_record_selection422`、`fresh_record_model_extension_exactly_when_channels_agree422`）を受けて決める。中心の record 行がなく、上下の端点が一致しない場合、固定した `SourceHead` からはどの `R` でも選択が作れない。また、旧 `HeadMeaning` の「中心が literal な record と同値」は、同じ要求の適合モデルの中に偽になるものがある。
- これは I-69 の (b) に当たる。結論の証拠（`DictionaryEvidence` の head の意味）が、spec より強いことを要求している。spec 6.5（2026-11-22、ユーザーの決定「2: 端点から選ぶ」）は、中心の行に根拠がなくても、根拠のある端点から照合・捕捉できるなら選ぶ、と定めている。端点から選んだときに spec が保証するのは、**捕捉した field が元の field 端点の区間に入り、残りが元の残余の区間に入ること**であって、中心が literal な record に等しいことではない。
- 判断:
  1. `DictionaryEvidence` の head の意味に、**端点射影の構成子を足す**。中身は、cycle 422 の `same_model_endpoints_support_both_projected_channels422` が示した形（実中心の required/optional の field 射影がそれぞれ元の field 端点に挟まれ、mask residual が元の残余区間に挟まれる）を、同じ適合モデルで述べるもの。literal な record の構成子はそのまま残す。
  2. `Classifies` の `SourceHead` にも、対応する**端点からの head 証拠**の構成子を足す。根拠は二つの元の record 端点の読み（cycle 422 の独立な検査）だけで、中心の行を作ったり推測したりしない。
  3. 構成子を足すだけなので、`dictionary_sound` と `check_sound` の文（全称・前提・結論の形）は変わらない。既存の `R0`〜`R13` の証明は、古い構成子を作っているのでそのまま通るはず。通らなければ、その理由を書くこと。
  4. そのうえで C14 を閉じる（`R14`、`check` の分岐、`check_sound`）。元の B6 本体の右辺の射影（cycle 422 の `original_B6_binder_yields_required_projection_and_exact_addresses422`）を、同じ binder の固定出力につなぐ。
- 固定先にその値がすでに保持されていることを別に示す必要があるなら、それも C14 の一部として扱う。
- 言語の受理範囲は変えない（spec 6.5 の決定どおり）。端点からの選択で spec が決めていない場合に当たったら、質問ノートにして止める。

## I-76（2026-11-26）独立 Audit は他の Audit を import しない（cycle 427 が統合で落ちた）

- cycle 427（`0e2b724e9`）は統合の検査で失敗した。`lean/Audit/Cycle427I74StructuralWhereForest.lean`・`…Readback.lean`・`…Visits.lean` が、別の Audit ファイルを `import «Cycle427I74StructuralWhereReadback»` / `import «Cycle427I74StructuralWhereSameRole»` の形で読んでいる。監督役の検査は各 Audit を単独で `lean` にかけるので、`unknown module prefix` で止まる。cycle 427 はまだ integration に入っていない。
- 決まり: **`lean/Audit/` のファイルは、`Yulang.*` のモジュールだけを import する。** 別の Audit ファイルを、どの書き方（`Audit.X`、`«X»`、裸の名前）でも import しない。共有したい補題や定義は `lean/Yulang/` の新しいモジュールに置き、`lean/Yulang.lean` の末尾に import を足す。
- 次の周でやること: 上の 3 ファイルを、`Yulang.*` だけを import する形に直す（必要な共有部分は新しい `lean/Yulang/…427….lean` か次の周のモジュールへ）。cycle 427 の Lean はまだ integration にないので、これらの Audit を書き直してよい。直したら、各 Audit を単独で `lean --trust=0 -DwarningAsError=true` にかけて、終了コード 0 を確かめること。
- 監督役は、この形の import も検出するように検査を広げる。

## I-77（2026-11-26）I-76 の残り: cycle 428 の Audit 7 本も直す

- cycle 429 で cycle 427 の 3 本は直った。ありがとう。ただ、cycle 428 で足した次の 7 本が、まだ別の Audit を import している。I-76 の決まり（`lean/Audit/` は `Yulang.*` だけを import する）は、この 7 本にも当てはまる。
  - `lean/Audit/Cycle428I74StructuralWhereBodyReplay.lean`
  - `lean/Audit/Cycle428I74StructuralWhereIntegratedLegacy.lean`
  - `lean/Audit/Cycle428I74StructuralWhereLegacyTrace.lean`
  - `lean/Audit/Cycle428I74StructuralWhereRootFrame.lean`
  - `lean/Audit/Cycle428I74StructuralWhereSingletonTape.lean`
  - `lean/Audit/Cycle428I74StructuralWhereTapeBoundary.lean`
  - `lean/Audit/Cycle428I74StructuralWhereTrace.lean`
- 次の周の最初にこの 7 本を直すこと。cycle 427〜429 はまだ integration に入っていないので、書き直してよい。直したら各 Audit を単独で `lean --trust=0 -DwarningAsError=true` にかけて、終了コード 0 を確かめること。報告に「Audit の import: `Yulang.*` 以外 0 件」と 1 行書くこと。
- これ以降に足す Audit も同じ決まりで書くこと。

## I-78（2026-11-26）前の周のメモは追記だけにする

- cycle 431 は C15 を閉じた。integration に入った（`dots-431`、verify-lean PASS）。C の残りは 7 行（C16–C22）。
- ひとつだけ: cycle 431 は `notes/design/dots-cycle-430-i77-supervisor-replay.md` の既存の 2 行（実測結果の行と「Audit の import」の行）を消して書き換えた。前の周のファイルは、`lean/` でも `notes/` でも**追記だけ**にすること。説明を直したいときは、元の行を残したまま末尾に「訂正（cycle N）」の節を足すか、今の周の新しいメモに書く。
- 補足: `import Lean` などの標準ライブラリの import は、これまでどおり使ってよい。I-76/I-77 が禁じるのは、Audit が別の Audit を import することだけ。

## I-79（2026-11-26）C18: 完了した別需要の出力で native head を支える証拠の形を足してよい

- cycle 435 の `dots-cycle-435-c18-fixed-carrier.md` を読んだ。結論に同意する。今の `DictionaryEvidence` の 2 つの形（named の `Event`+`SourceHead`、projected record leaf）では C18 の正例を表せない。また、適合モデル全部で `nativeSyntax L = some …` を言うのは偽（L に authored route がないので、`nativeSyntax L := none` にしても適合する）。だから、この欄を埋める方向には進まないこと。
- 監督役として、表現の決定を出す（言語の意味は §6.3 で決まっているので、ユーザーへの質問はいらない）。**C18 のために、完了した別需要の出力を根拠にする独立した lane と、それに対応する head／証拠の形を 1 つずつ足してよい。** I-75 が C14 に record projection を許したのと同じ扱い。
  - 新しい証拠が持つもの: 同じ State の有限の選択済み producer（`SourceTrace`）、その producer の元の typed B6 出力と出力番号、固定先 L、literal に保持された行。意味は「全ての適合モデルで、L の値は保持行を通して読んだ producer の出力値に等しい」。`nativeSyntax L` は使わない。
  - 既存の 2 lane・`Classifies`・`DictionaryEvidence` の既存の形と意味は変えない。`dictionary_sound` / `check` / `check_sound` の外形（I-65 の固定声明）も変えない。旧 witness の Bool は全入力で変わらないことを示すこと。
  - C406 の scoped な証明を、それが依存している固定 goal の下位モジュールへ持ち込まないこと（循環を作らない）。低いほうの payload は高いほうの `SourceTrace` に依存させず、producer の出所は R18 の高い規則で検査する、という cycle 435 の案でよい。
- **前の周のファイルからは行を消さない**（I-78）。足すのは、新しいコンストラクタ・新しいモジュールの追記だけにすること。既存の行をどうしても変える必要が出たら、その周は Lean を変えずに止めて、変えたい行と理由をノートに書くこと。監督役がユーザーに聞く。
- C18 を閉じる条件はこれまでと同じ 3 つ（`dictionary_sound_R18`、`check` の新分岐、同じ外形の `check_sound`）。cycle 435 の次の手順 (1)(2) から進めてよい。

## I-80（2026-11-26）C22 は保留にして C 一覧を終える。次の段は「狭い分岐を一般の規則へ」と NoFalseRejection の設計から

- **C22 は保留にする**（cycle 442 の `dots-cycle-442-c22-retention-next.md` の第一案を採る）。cycle 442 の反例（`original_fixed_targets_can_fail_after_real_source_replay442`）のとおり、今の `I72.State` / `Fits` は row を含む関連型の固定先の等式を保持できない。これは checker の分岐を足して閉じる話ではなく、State の表現が足りないという話なので、次の段（下の G 一覧）の一行として扱う。cycle 442 の Lean と反例はそのまま残す。言語の受理・拒否は変えない（§6.3 の「選んだら固定先に等式を足す」はそのまま正しい。まだ Lean で表せていないだけ）。
- これで C の一覧（I-74）は終わり（C01〜C21 を閉じ、C22 は G 一覧へ）。ここまでで言えることと言えないことを分けておく。
  - 言える: `check_sound` は全入力について健全。C01〜C21 の仕様の代表例は、それぞれ `check` の分岐で受理され、その受理は健全。
  - 言えない: 各分岐は「where なし」「可視候補一つ」「一出力」などの限定つき。仕様が受理する一般のプログラムを `check` が受理するとは、まだ言えない。
- 次の段の目標は完全性（NoFalseRejection）。ただし Lean を書く前に、設計ノートを一本書くこと。この周は Lean を足さない。
  1. **固定声明の案**: 宣言的な受理（全規則 `R_full` での `Classifies`。今の `R0`〜`R22` の和でなく、spec §6 の規則をそのまま述べたもの）から、`check` が true になる witness の存在を言う定理の形。量化子・前提・結論を I-65 の固定声明と同じ書き方で。solver が witness を作る話（構成的か）と、存在だけの話を分けて書くこと。
  2. **一般化の一覧（G 一覧）**: C22 の「row を含む固定先の等式を State に保持する表現」を最初の行に入れる。続けて、C01〜C21 の各分岐が置いている限定（where の子の数、候補の数、出力の数、再帰の深さ、モード、row 引数など）を表にし、それを外すのに要る一般の規則を一行ずつ挙げる。C 一覧と同じく、一周一行で閉じられる粒度にする。
  3. **`R_full` と今の規則の関係**: 今の各 `Rn` が `R_full` に含まれること（健全性が一般の規則へ持ち上がること）を、どの定理で示すか。
  4. 停止性は紙の証明に回す（I-55 以来の方針のまま）。完全性の証明で停止性が要る箇所があれば、仮定として明示し、どこで使うかを書く。
- 言語の意味を新しく決める必要が出たら、質問ノートに書いて止まること。監督役がユーザーに聞く。
- G 一覧と固定声明の案は、監督役が読んで返事をするまで Lean に入らない。

## I-81（2026-11-27）C443 の設計への返事: A を目標に、まず G00 として「全 State」を設計する

cycle 443 の `dots-cycle-443-no-false-rejection-design.md` を読んだ。全体の方針に同意する。次のとおり決める。

1. **目標は A（`NoFalseRejection`）**。宣言的に選ばれた同じ辞書 d について、正確な報告 r と、`check_full` が true になる有限の witness が存在すること。B（与えられた任意の正確な報告を受理する）は追加目標として残すが、今は着手しない。
2. **診断側（保留・曖昧・拒否の報告の完全性）は別の成果として後回し**。まず selected 側だけ進める。既存の診断の分岐と、その健全性はそのまま残す。
3. **停止性**: 存在定理（A）は、渡された有限の導出についての帰納で示すので、solver の停止を仮定しない。実際の合成関数 `synthesize` を主張するときだけ、紙の補題を名前つきの仮定として置く。この切り分けを採る（I-55 からの方針と同じ）。
4. **順番**: G00 を最初にすることに同意する。ただし G00 は「C22 の一行」ではなく、**`R_full` が使う全 State の土台**として設計すること。具体的には、次の周の成果物はこれだけにする。
   - 新しいモジュールに、`FullState`（今の `I72.State` に、元の出現・宣言番号・出力番号・本文・既出の固定先・kind を持つ**型付きの保持等式**を足したもの）と `FitsFull`（`Fits` に、保持等式が全て成り立つことを連言したもの）を**定義だけ**置く。
   - 今の State からの持ち上げ `liftState : I72.State → FullState`（保持等式は空）と、`Fits s m ↔ FitsFull (liftState s) m` の証明。
   - cycle 442 の反例を正例に変える試験: 保持等式を持つ FullState では、signed row の固定先が全ての `FitsFull` モデルで成り立つ（true）。同じ RHS を別の slot の記録で代用したものは成り立たない（false）。既出の Int 制約と行を含む `ref` を連言すると、適合モデルがない（上書きしない）。
   - `R_full` 本体、`check_full`、G01 以降は、この周では書かない。
5. 既存の `I72.State` / `Fits` / 証拠 / 規則 / checker / 固定声明は変えない。前の周のファイルから行を消さない（I-78）。
6. G 一覧の各行を閉じる条件（(i) 独立な規則と保存・反映、(ii) data-only の checker、(iii) 同じ State の正確な報告と健全性の保存、witness の具体化）は、設計ノートのとおりでよい。一周一行、閉じられなければ未完のまま報告すること。
7. `R_full` を spec §6 から書く途中で、spec が決めていない点に当たったら、質問ノートに書いて止まること（遅延案を先頭に）。監督役がユーザーに聞く。

## I-82（2026-11-27）G00 を閉じる: 保持等式の writer、FullState 上の局所規則、`check_full` の最初の形

cycle 444 の `FullState` / `FitsFull` / `fits_iff_fitsFull_liftState` と C442 の正負の対照を確認した。integration に入った（`dots-444`）。土台として受け入れる。次の周で G00 を閉じる。成果物は次の 3 つ。

1. **writer（宣言側）**: 選択された実 Event から、その出力 plan どおりに保持等式を足す `retainSelected : FullState → (選択の証拠) → FullState`。保持行は Event の元の出現・宣言番号・出力番号・本文・固定先から作り、値やモデルを入力に取らない。`FitsFull (retainSelected s e) m ↔ FitsFull s m ∧ (e の固定先の等式が m で成り立つ)` を示す。既出の制約は上書きしない（連言のまま）。
2. **局所規則と健全性**: G00 の局所規則（C442 の形: where なし・可視候補一つ・行を含む関連出力一つ）を `FullState` 上で定義し、`dictionary_sound` を I-65 と同じ外形で、ただし `Fits` の代わりに `FitsFull` で示す。旧規則 R21 からの持ち上げは `liftState` 経由で、旧の分類がそのまま成り立つことを示す（`local_Rn_case_in_full` の最初の一件）。
3. **`check_full` の最初の形**: `check_full : FullProblem → Result → Witness → Bool` を、(a) 旧 witness は `liftState` で持ち上げた入力に対して旧 `check` と同じ Bool（全入力で）、(b) G00 の新しい分岐、の和として定義。`check_full_sound` を I-65 と同じ外形（`FitsFull` の全モデル）で示す。C442 の実 fixture で、保持等式を持つ正例が true、別 slot の代用・既出 Int との連言・保持なしが false になる対照を付ける。

- `R_full` の全体はまだ書かない。この周の局所規則は、後で `R_full` の一つの節として入れられる形にしておくこと。
- 既存の `I72.State` / `Fits` / 規則 / checker / 固定声明は変えない。前の周のファイルから行を消さない（I-78）。
- 閉じる条件は I-81 の 6 のとおり。三つが揃わなければ、G00 は未完と報告すること。

## I-83（2026-11-27）G00 を受け入れる。次は G01 から、一周一行

- cycle 447 の G00（`selected_wire_iff_exact_local_report447`、`check_full_sound447`、`independent_selected_report_has_finite_witness447`）を確認した。integration に入った（`dots-447`、verify-lean PASS。`#eval` 2 件は実行試験で、証明に使っていないことを監督役が読んだ）。G の残りは 21 行（G01–G21）。
- 次からは G 一覧を G01 から順に、一周一行で進めること。各行は `check_full447` を土台にして分岐を足し、前の witness の Bool が全入力で変わらないことを毎回示すこと（入口を分岐ごとに別々に作らない）。
- 各行の完全性の側は、G00 と同じ形でよい: 独立した局所の選択から、その正確な報告を通す有限の witness を作る定理。健全性（`check_full_sound`）と同じ周に揃わなければ、その行は未完と報告する。
- 前の checker の保守的すぎる検査（cycle 445 の rank 証人、cycle 446 の全体ヘッダー）のような穴がまた見つかったら、言語の拒否と区別して報告し、局所の検査に置き換える方針でよい。前の入口は残す。

## I-84（2026-11-27）質問 `dots-cycle-451-g03-merged-k2-location.md` への答え: 今は決めない（第一案）

- ユーザーの決定は **第一案（遅延）**。まとめた需要の K2 などの診断を、利用者にどの元 `where` で見せるかは、診断を実装するときに決める。それまでは、まとめた需要の証拠に、対応する全ての元 `where` の位置を宣言順のまま残す。位置を一つに選ばない。候補の選択・K2・まとめ方・拒否は変えない。spec §6.3 に「未定」として書いた（`yulang3` の spec/06-roles.md、`まとめた需要の出力の指定どうしが合わなければ` の項の直後）。
- したがって G03 の正確な報告は、まとめた需要について「全ての元位置の宣言順の列」を持つ形で定義してよい。代表位置を選ぶ規則を報告や witness に入れないこと。cycle 451 の、元位置を漏れなく保持する証拠をそのまま使って、まとめた後の正確な報告を `check_full450` の累積入口につなぎ、G03 を閉じること。

## I-85（2026-11-27）G03 を二行に分ける: 今の相で閉じる G03 と、相の遷移を扱う G03b

cycle 453 の報告を読んだ。同 role の兄弟が「全適合モデルで同値だが raw Alias は別」の場合、まとめるときの `centerPair` が raw graph を変え、元は安全だった子に新しい K2 が出ることがある。これは一つの相の中で閉じる話ではなく、相の遷移（まとめる前後で raw を読み直す）の話だと判断する。監督役として G 一覧を次のように直す。

- **G03（今の相）**: 選ばれた親の全ての元 `where` 子について、**同じ相の raw graph** で同 role・同入力と分かる（raw Alias 類が同じ）ものをまとめ、全元位置を宣言順に持つ正確な報告を出す範囲。cycle 450〜453 の成果（`check_full453`、`exact_scoped_grouped_report_iff_finite_wire453`、`check_full_sound453`）で、この範囲の三条件が揃っているなら、**G03 を閉じたと報告してよい**。閉じるときは、範囲の境界（raw Alias 類で判定する、相の遷移は扱わない）を報告に明記すること。もし三条件のどれかがこの範囲でまだ欠けているなら、それを埋めてから閉じること。
- **G03b（新しい行、相の遷移）**: 根拠のある等式（author/capture 由来、raw Alias ではない）で同入力と分かる兄弟をまとめるとき、まとめた後の raw を読み直して新しい K2 を正しく報告する範囲。cycle 453 の「残り (1)(2)」がこの行。G 一覧は G00〜G21 と G03b の **23 行**になる。G03b は G15〜G19（完了・保持・合流）と依存が近いので、G15〜G19 のどれかと一緒に扱うのが自然なら、その順に進めてよい。
- これは statement を縮めて数を稼ぐことではない。範囲を外した分を新しい行として一覧に残すので、残りの総数は減らない。
- 表示位置は I-84 のとおり未定のまま。新しい言語の決定はない。

## I-86（2026-11-27）G04 の境界: 残りは既にある G06/G07/G20/G21 へ回す

cycle 455〜457 の G04 の進み（閉じた record field、途中の tag 付き variant・primitive pair・宣言 covariant の単項 point nominal、ready header の局所化）を確認した。cycle 457 の「残り」は、どれも G 一覧の別の行がすでに持っている範囲だと判断する。

- 開いた tail（未解決・解決済みとも）→ **G06 / G07**（open tail の保留、閉じた残部の捕捉）。
- 非 point の nominal、一般の mode / kind / 多引数 → **G20 / G21**（入れ子 nominal の分散、多引数・row 引数の位置）。
- 任意の inline source payload / bound pattern のうち、上の二つに入らないもの → G04 の範囲として残す。

したがって G04 は「閉じた record・tag 付き variant・primitive pair・宣言どおりの単項 point nominal を任意の有限深さで通って、実際に訪れた field の K2 を報告する」範囲で、三条件（独立な規則と保存・反映、data-only checker、同じ State の正確な報告と健全性・witness の具体化）を揃えたら閉じてよい。閉じるときは境界と、回した先の行を報告に明記すること。これは範囲を縮めることではなく、重なる部分を一つの行に集めること（総数 23 は変わらない）。

## I-87（2026-11-27）G04 は事例を足すのをやめ、head pattern の文法全体で一度に示す

cycle 455〜459 の G04 は、毎周「この形も読めた、次の形は読取範囲外」を一つずつ足している（閉じた record → variant/pair/point nominal → inline 構造 → 推論された union の非訪問成分 → 同一 tag 重複）。どれも本物の穴だが、この進め方では終わりが見えない。進め方を変える。

1. **文法を先に固定する**: `impl` head と `where` が書ける型 pattern の文法を、spec（§4 の型構文、§6.2/6.3 の head）と既存 Lean の pattern 型から、有限個の構成子の帰納型として一つに書き出す（名前つき型の適用、record（閉じた/開いた tail）、variant（tag と payload、同 tag の重複を含む）、tuple/pair、型変数、primitive など）。G06/G07（開いた tail）と G20/G21（一般 mode・多引数）に回した構成子は、文法には含めたうえで「G04 では扱わない」と印を付ける。
2. **reader と訪問を文法の上の構造帰納で定義する**: 事例ごとの reader を足すのではなく、構成子ごとに一つの場合分けを持つ reader / 訪問関数を書く。訪問しない成分（非訪問の pair 成分、推論された union など）は「読まない」ことを構成子ごとに明示する。
3. **完全性も構造帰納で示す**: 「G04 の範囲の任意の pattern と、実際に訪れた field の K2 について、正確な報告を通す有限の witness が存在する」を、文法の帰納法で一度に示す。cycle 455〜459 の実例は、この定理の系として再確認する回帰に回す。
4. 一周で全部終わらなくてよい。次の周は (1) の文法と (2) の定義だけでもよい。ただし、新しい事例を一つずつ足す周には戻らないこと。

## I-88（2026-11-27）宣言の準備条件（安定性）を G04 から外し、独立した一行 GD にする

cycle 460〜462 で G04 は文法全体の帰納法に移った。ありがとう。残りを読むと、G04 の本体（訪れた field の K2）と、**宣言の準備条件**（`DeclarationReady`、特に全捕捉の `StableSmaller`）の二つが混ざっている。後者は要求ごとの解決ではなく、`impl` 宣言を受理する時点で一度だけ決まる性質なので、別の行に分ける。

- **新しい行 GD（宣言の受理証明書）**: 各 `impl` 宣言について、`DeclarationReady`（安定性を含む）を示す有限の証明書と、その data-only な検査器、検査器の健全性（true なら `DeclarationReady`）と完全性（`DeclarationReady` なら証明書が存在）。宣言ごとに一度だけ検査し、要求ごとの witness には入れない。安定性の有限の度量（cycle 462 の「opaque capture weight による構造的度量」など）はこの行で扱う。G 一覧は **24 行**になる。
- **G04 の側**: `FullProblem` に「宣言ごとの検査済み証明書」を入力として持たせ、G04 の witness と checker はそれを前提として読むだけにする（自分では安定性を再証明しない）。G04 を閉じる三条件は、この前提のもとで示せばよい。前提が正しいことは GD の健全性で保証される。
- 残りの「訪れる inline/bound の元位置と raw 位置の対応」と「残余 join」は G04 の本体として残す。I-86 の移し替え（開いた tail → G06/G07、一般 mode → G20/G21）はそのまま。
- これは範囲を縮めることではなく、一度だけ決まる性質を一つの行に集めること。言語の受理・拒否は変えない。

## I-89（2026-11-27）G04 の残り三つのうち二つは別の行へ。G04 は (1) の producer だけで閉じる

cycle 463・464 の「未証明の本体」三つを、G 一覧の元の定義（`dots-cycle-443-no-false-rejection-design.md` の表）と突き合わせた。

- (2)「全 candidate matching と曖昧性前の K2 を既存規則へ接続」→ **G05 / G10**。G04 の行は元々「単一候補」で、複数候補の走査・K2 の優先・曖昧性は G05（全候補 tape の actual visit/election、K2 が曖昧さより先）と G10（全候補の match/mismatch/defer）の範囲。G04 ではやらない。
- (3)「現在の visitor が開かない残余 join」→ **G08**（合流後の payload 全体の捕捉、plain と nonplain の区別）。G04 ではやらない。
- (1)「実 compiler の相で許可される inline/bound の必要座標・issuer を生成する producer と同相入力連結」→ これが **G04 の本体**。単一の可視候補・GD の証明書を前提に、(1) を示して三条件が揃えば G04 を閉じてよい。閉じるときは、(2)(3) を G05/G10/G08 に回したことを報告に書くこと。

総数 24 は変わらない（重なりを一つの行に集めるだけ）。I-86・I-88 の移し替えもそのまま。

## I-90（2026-11-27）各周の報告に、使った道具を一行書く

- 各周の canonical report（`notes/handoff/dots-cycle-N.md`）の先頭近くに、次の一行を書くこと。
  `道具: <この周の作業をしたモデル名（分かる範囲で）>; 委譲: <Codex などに委譲した場合はモデル名・回数・各委譲の task/thread ID。委譲がなければ「なし」>`
- 分からない項目は「不明」と書く。推測で埋めない。委譲がなかった周は「なし」と書けばよく、それで評価が下がることはない。正確さだけを求めている。
- 委譲した場合は、その task/thread ID を必ず書くこと（監督役が実在を確かめられるように）。

## I-91（2026-11-28）G04 の詰まりを一本の設計ノートにする

G04 は cycle 455 から 13 周続いている。I-86〜I-89 で範囲を (1)「inline/bound の必要座標・issuer を生成する producer と同相入力連結」まで絞ったが、466・467 でも「既発行の issuer なら読める、未発行の native write は出ない」で止まっている。進め方を決める前に、次の周の最初に設計ノートを一本書くこと（`notes/design/dots-cycle-468-g04-blocker.md`）。

1. G04 (1) を閉じるのに、**まだ無いもの**を一覧にする。各項目について、(a) 今の Lean の定義の上で証明すれば済むのか、(b) 表現が足りない（I-79 や G00 のように、State や証拠の形を足す必要がある）のか、(c) 別の G 行（G15〜G19 の完了・保持・発行、GD など）が先に要るのか、を書く。
2. 「未発行の native write」が問題なら、それは**誰が・どの相で**発行するものか（spec の根拠つき）。G04 の要求の解決の中で発行されるのか、宣言の受理（GD）や別需要の完了（G18）で発行済みになっているはずのものか。
3. 推奨案を一つ。G04 を「既発行の issuer を前提に閉じ、発行そのものは別の行へ回す」で閉じられるなら、その境界と回す先の行を書く。
4. ノートを書いたら、その周は推奨案に沿って進めてよい。ただし (b) の表現の追加が要る場合は、Lean を足す前に止まって報告すること（監督役が I-79 のように判断する）。

## I-92（2026-11-28）C468 の勧告を採る: `InputInspectionOrigin` を足してよい（既存の source 位置を参照する形で）

`dots-cycle-468-g04-blocker.md` を読んだ。結論に同意する。「既発行の native Write だけを前提に G04 を閉じる」縮小は採らない（出力のない要求の source-only の field 検査を落とすため）。表現の決定として次を出す。

1. **`InputInspectionOrigin` を足してよい。** 新しいモジュールに、既存の nominal native 出力 ledger とは別の、入力側の証拠として置く。FullState や既存の State / Fits / 証拠 / checker / 固定声明の定義は変えない（I-78、I-79 と同じく追記だけ）。
2. **新しい物理名（raw の名前）は足さない。旧 source 側の occurrence と元構文の path を参照する形にする。** raw graph に名前を書き足すと元の K2 が不変だと言えなくなる（C464 の checked cut の比較のとおり）ので、その方向は採らない。照合は「元 occurrence・可視宣言と元 ordinal・head 引数・元の original/normalized path」から、既存の同相 raw query/owner/child へ写す有限データで行う。
3. **根拠を所有する event は、その要求の入力を source から作った compiler の event（要求の元 occurrence の型付け・捕捉）とする。** 別需要の発行（G18）や宣言の受理（GD）ではない。出所は二つの和: (i) ソース制約からの constructor 観測（架空の Write・version・grant を要求しない）、(ii) release 済みの完了出力（この枝は G18 の資料を読むだけで、G18 の閉鎖を前提にしない）。
4. 合格基準は C468 §3 のとおり（出力なし inline source の exact report と有限 wire、全 FitsFull で健全、未訪問 sibling・違う原位置・旧 version・未完出力だけ・raw alias なしをそれぞれ false）。
5. これで足りないと分かったら（参照だけでは同相の raw に写せない例が出たら）、Lean を足す前に止まって、その例をノートに書くこと。

## I-93（2026-11-28）C469 の境界への答え: K2 は「等しい型を同じ点とみなす」最小のグラフで判定する（ユーザーの決定）

`dots-cycle-469-i92-existing-raw-boundary.md` を読んだ。これは表現だけでなく言語の意味の問題だったので、ユーザーに聞いた。決定は **「等しい型は同じ扱い」**。

- 循環の上にあるかは、書かれた（推論された）raw グラフの形ではなく、再帰型として等しい部分を一つにまとめた最小のグラフで判定する。C469 の例（`μ = {40: μ}`、入力 `{30: μ}` を `4 = {30: {40: var 5}}` と一段展開して持つ）では、field30 の inline の `{40: var 5}` は 5 と等しいので循環の上にあり、K2。型として等しい入力で、書き方や推論の経路によって受理と拒否が分かれてはいけない。spec §6.3 の K2 の項に「決定（2026-11-28）」として書いた（yulang3 `3f41d396b`）。
- 表現の決定（監督役）: C469 の「監督に残す表現判断」の案を採る。**raw に名前や行を足さない**（I-92 のまま）。代わりに、source occurrence 上の inline の観測（元 path と、そこで実際に調べる構成子）と、既存 raw の点との**等しさの有限な証拠**（構造を保つ有限の対応関係。bisimulation のように、対応する二点の構成子と子が互いに対応しているもの）を足してよい。K2 の証拠は「inline の観測位置 ↔ 既存 raw の点 5 の対応」と「5 の既存の循環」の組で示す。
- この対応は有限データとして witness に入れ、checker が data-only に検査する。全 Model の値の等しさから逆に読むことはしない（それは健全性の側の帰結で、checker の入力ではない）。
- K2 でない側（調べる位置が循環に乗らない）も同じ最小のグラフで判定するので、対応関係が無いことの証拠ではなく、既存の per-site 安全証拠（C449/C446 の split witness）を最小化した点に対して使う形になるはず。設計がそれで閉じない場合は、その例を書いて止まること。
- 旧 Yulang2 や既存 audit の例をこの決定で読み替えて「済」としないこと。言語の受理範囲は、等しい型どうしで一致する方向にだけ動く（K2 の拒否が、一段展開した入力にも及ぶ）。

## I-94（2026-11-28）cycle 471 が統合の検査で落ちた: doc コメントの単語 `admit`

- cycle 471（`4cc273205`）は、監督役の `tools/verify-lean.sh` の「禁止された構成」の検査で失敗した。原因は `lean/Yulang/GeneralDeclarativeI65I74LiteralFold471.lean` 261 行の doc コメント `this gate must not admit them as a source.` の単語 `admit`。検査は追加行の中の `sorry` / `admit` を、コメントの中でも拒否する（公理の検査自体は通っていて、証明に問題はない）。
- cycle 471 はまだ integration に入っていないので、この行を書き換えてよい（例: `must not accept them as a source`）。次の周の最初に直すこと。
- これ以降、Lean のファイルではコメントや doc の中でも `sorry` / `admit` / `native_decide` / `axiom` などの禁止語を単語として書かないこと。監督役は 471 と次の周をまとめて統合する。

## I-95（2026-11-28）G04 に期限: cycle 479 まで。閉じなければ名前つきの前提にして先へ

G04 は cycle 455 から 22 周続き、その間 G の閉鎖は 0。各周の成果は本物で、I-85〜I-94 で範囲は「要求の入力を作る compiler event と元 source 位置の接続」まで絞れている。ただ終わりが読めないので、進め方を決める。

1. **期限は cycle 479 の報告まで**（あと 3 周）。それまでに G04 の三条件（独立な規則と保存・反映、data-only checker、同じ State の正確な報告と健全性・witness の具体化）が揃えば閉じる。
2. 揃わなければ、cycle 479 の報告で、G04 の**残りを一つの正確な命題**として書き出すこと（Lean の `def`/`Prop` として、量化子・前提・結論つき。証明はしない。例: `G04Producer : Prop := ∀ … , … → ∃ w, …`）。以後、G05 以降で G04 を使う箇所は、その命題を**名前つきの前提**として受け取る（`(h : G04Producer) → …`）。`axiom` にはしない。G04 は「未完、前提 `G04Producer` を残す」と数える。
3. どちらの場合も、cycle 479 の次の周の最初に、**証明の短縮の設計ノート**を一本書くこと（ユーザー了承済みの方針）。中身: 周ごとの累積入口の鎖（`check_full447` → … → 現在）を一つの定義にまとめる案、G00〜G03 の一般化で不要になった C 一覧の狭い分岐、周ごとの Audit の整理。置き換えの対応表と、I-65 の固定声明・各 `check_full_sound` の外形が変わらないことを示す計画を書く。**このノートの段階では何も消さない**（削除はユーザーの承認後、監督役が一回だけの例外を開ける）。

## I-96（2026-11-28）`G04Producer` を確認した。一点だけ確かめてほしいこと

- cycle 479 の `G04Producer : Prop`（`lean/Yulang/GeneralDeclarativeI65I74G04Producer479.lean`）を読んだ。証明も公理化もせず名前つきの前提にしたのは I-95 のとおり。以後 G04 を使う箇所はこれを `(h : G04Producer)` として受け取り、G04 は「未完、前提 `G04Producer` を残す」と数えること。
- 一点: 今の形は `∃ emit, ∀ … , basis.ExactFor event → ∃ wire, emit … = some wire ∧ IssueIsFaithful …`。古典論理では、これは「`∀ … , ExactFor event → ∃ wire, IssueIsFaithful basis event wire`」（関数 `emit` を経由しない、事象ごとの存在）と同値のはず（choice で `emit` を作れる）。NoFalseRejection A は存在の主張なので、前提は事象ごとの形で足りる。cycle 480 の最初に、(a) この同値を Lean で示し、(b) 事象ごとの形のうち**どの部分が今証明できないのか**を一文で書くこと。もし事象ごとの形がすでにある補題から証明できるなら、G04 はその場で閉じてよい（三条件の確認つきで）。実 compiler がその操作を実装しているかは、存在の主張 A には要らない（それは solver の合成の話で、別の契約）。
- そのあと予定どおり、cycle 480 で証明の短縮の設計ノート（I-95 の 3）を書くこと。

## I-97（2026-11-28）証明の短縮: ユーザーが削除までまとめて承認した。手順を決める

`dots-cycle-480-proof-compression.md` を読んだ。計画に同意する。ユーザーの決定は **「削除までまとめて許す」**: 同値の証明が通ったものから、監督役の検査で旧い入口・狭い分岐・Audit を消してよい（周ごとに監督役が一回だけの削除例外を開ける。ユーザーへの再確認はしない）。手順は次のとおり。

**段階 1（追記だけ）**
1. `check_full_flat` と互換アダプタを新しいモジュールに足す。設計 §1 の表の各旧入口について、(i) 全 `p r w` で旧入口と同じ Bool、(ii) 報告・分類・全 `FitsFull` の証拠の保存と反映、(iii) 同じ外形の `check_full_sound` の再取得、を Lean で示す。表のどれかの枝で示せなければ、その枝は旧入口のまま残す（無理に畳まない）。
2. G04 の残り（I-93 の型商報告の枝）は、旧入口の鎖ではなく **`check_full_flat` の新しいタグ** として足してよい。これで G04 を閉じられるなら閉じる。

**段階 2（削除。段階 1 が integration に入った後の周から）**
3. 削除する周の報告に、**削除の明細**を一節つける: 消すパスの一覧（`lean/` 以下の完全なパス）、各パスの置き換え先（どの定理・どの入口が同じことを示すか）、そのパスを import していたファイルの一覧と移した先。明細に書いたもの以外は消さない。
4. 消してよいもの: 段階 1 で同値が integration に入った旧入口とその専用の補題、G00〜G03 の一般化に吸収されたと明細で示せる狭い分岐、重複した Audit。消してはいけないもの: `lean/Audit.lean`・`lean/README.md`（凍結）、I-65 の固定声明とその証明に使われるもの、`check_full_flat` が委ねている leaf、まだ他から import されているもの、spec。
5. `lean/Yulang.lean` から行を消してよいのは、**同じ周に消したファイルの `import` 行だけ**。ほかの行は消さない。
6. 一周で消す量は、監督役が全部読める大きさにする（目安: 一周 30 ファイルまで）。消したあとも全体ビルド・公理の門・既存の全 Audit が通ること。
7. 報告に、消した前後の宣言数とファイル数を書くこと。

段階 1 と G04 を先に進め、段階 2 は段階 1 が統合されてからにすること。G05 以降はその後でよい。

## I-98（2026-11-28）G04 はここで区切る。次は削除（段階 2）と G05

G04 は cycle 455 から 30 周続いた。I-95 の期限（cycle 479）は過ぎ、`G04Producer` は cycle 480 で証明された。ありがとう。ただ I-97 の「段階 1 と G04 を先に」は、G04 を期限の後も続けてよいという意味ではなかった。ここで区切る。

1. **G04 の残りを、もう一つの名前つき命題にする**（cycle 485 の最初に）。cycle 483・484 の残り（局所 route が受ける prior authority を現行の入口に独立に結び、I-93 の signed report を `check_full_flat` のタグにする部分）を、量化子・前提・結論つきの `G04Entry : Prop` として `def` で書く。証明も公理化もしない。G04 は「未完、前提 `G04Entry` を残す」と数える。cycle 484 の「出所（source / released）は問題と報告から復元できない」反例は、witness が出所の選択を持てばよいという意味で、存在の主張（A）には差し支えない。`G04Entry` の形はそれに合わせること。
2. **段階 2（削除）を始める**（cycle 485 から）。I-97 の 3〜7 の手順どおり、削除の明細つきで、一周 30 ファイルまで。最初は、cycle 481 で同値を示した 18 個の旧入口の鎖のうち、`check_full_flat` が直接呼ぶ leaf でも I-65 の証明でもなく、どこからも import されていないものから。消せるものが無い周は、その理由（何がまだ import しているか）を明細に書けばよい。
3. **G05 に進む**。削除と同じ周に G05 を進めてよい。G05 で G04 の結果が要る箇所は `(h : G04Entry)` として受け取る。
4. G04 には、`G04Entry` を証明するときまで戻らない。
