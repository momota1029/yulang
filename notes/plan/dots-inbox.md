# dots への現在の指示 (監督役が書く)

更新: 2026-11-08 21:35（監督役、サイクル 3 の検証後）。dots は編集しない。変わったら、更新時刻と「指示の ID」が変わる。

- 指示の ID: I-4
- 状態: ACTIVE（`STOP` と書き換えたら、dots は次のサイクルで止まる）
- 最大サイクル数: 12（これを超えたら、dots は作業を止めて待機の報告を書く）

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

- **忠実性の確認 F1（優先して取ってよい）**: spec 5.5c（2026-11-08、ユーザー）の規則 `'a -> ['e] 'b` を `'a ['f] -> ['e, 'f] 'b` に cast できる（引数の行は空でなく全能。効果は関数の起動時に放出される）が、現在の Lean の核に入っているかを調べる。調べること: `Common.common_arrow_iff`（矢印の部分型は標準の反変・共変）、application の型付け規則、`Core.infer` の lambda・application が、この規則と整合するか。入っていなければ、反例の式（Yulang の例つき）と、定義を直す案（遅延する案を先頭に、2〜3 個）を `notes/handoff/` に報告する。Lean の既存の定理は変更せず、報告と質問ノートだけ。これは B4/B5/B6 の定義に響くので、結果を監督役が確認する。

- **T7b 到達可能性の解析（読み取りのみ・削除しない）**: `notes/plan/m1-plan.md` の T7b。Lean のメタプログラム（新規の `tools/Reach.lean` など、`lean/Yulang/` の外に置く）で、残したい定理から到達できない宣言とモジュールを列挙し、報告を `notes/handoff/` に出す。T7a の草稿（`lean/MainStatements.lean`）があれば、その Statement を根に加える。
- **T7a 主定理のファイル（文芸的 Lean）の草稿**: T7a。主定理を一つのファイル（`lean/Main.lean`）に再掲し、補題は別ファイルのまま。証明済みの定理は短い証明で、未完成は `def ... : Prop` で置き、日本語の docstring を付ける。主張の選択に迷う点は質問ノート。

- **T4 適合例の表を一本にする**: `lean/SpecExamples.lean` と `lean/SpecExamplesSettled.lean` の状態表を、一つの一覧（X1〜X24 の状態と、通っている入口の名前）にまとめる。既存の定理は削除しない。新しいモジュールとして作り、実在する定理と一致させる。
- **T3 の下調べ**: `notes/plan/m1-plan.md` の T3（variance 表と nominal carrier の接続）を読み、既存の `CommonDeclarationVariance*`、`CommonNominal*` の定理の一覧と、足りない橋を `notes/design/` に整理する（Lean は、橋が名指しできてから）。
- **適合例の追加**: spec 6.3〜6.5 の確定した例のうち、`notes/handoff/2026-11-08-m1-spec-examples-conformance.md` にないものを拾い、候補を `notes/handoff/` に提案する（spec は変更しない）。

## 参照

`notes/plan/m1-plan.md` の T1c、`notes/handoff/2026-11-08-dots-T1b-results.md`、`notes/design/2026-11-08-dots-T1b-producer-driver.md`、`notes/handoff/2026-11-08-dots-T1-results.md`、`notes/handoff/2026-11-08-m1-spec-examples-conformance.md`、`spec/06-roles.md` 6.2〜6.5（特に「where の子の解決は、兄弟の更新が安定するまで遅らせる」）。

## 回答済みの設計判断（監督役が転記）

- where の子は、兄弟の更新が安定するまで遅らせる。最終化はファイルの終わりの安定時。途中の曖昧・保留はエラーではない（`notes/questions/2026-11-08-T1b-sibling-recollection.md` の選択肢 1）。

## 監督役からの前回サイクルへのコメント

- サイクル 3（再起動後、約 51 分）: `verify-lean.sh` PASS（1157 jobs、Audit、公理ゲート 82,887 宣言）、`integration/m1-final` に統合。73 の公開定理、新規 9 モジュール。**T1c の本命（四方向の分類、一般 `resolve_exact`、X13〜X16）は 3 サイクル連続で未達**だが、報告は正確で、未達と書いている。
- 特に良かった点: (1) **兄弟の順序独立**（`CommonRolePathOrder.observable_order_independent`: 任意の有限 2 path で実 Parent 入口の observable が一致）と、`CommonRoleSiblingOrders` で forward / reverse の最終モデル集合が等しいことを証明した。確定した where の連言の性質（spec 6.3）に合う。(2) `Main.lean` に 11 定理を昇格した（従来の 8 定理は草稿と同じ型）。「全言語完成を宣言する Prop は追加していない」という線引きが正しい。(3) T7b の根を、全 Audit・Main・X の入口へ拡張して実測した（削除なし）。(4) ハートビートを 10 分ごとに出し、復旧ではなく再開を選んだ記録も明確。
- 次の 1〜3 補題候補は dot 自身が `notes/design/2026-11-08-restart-next-saturation.md` に記録した: (A) 実生成 child の source provenance と有限仕事領域、(B) 新情報のない再訪を除いた driver の停止と意味的閉包、など。**I-4 の最優先はこの (A)(B)**。部品の追加で終えず、四方向の分類へ向かうこと。
- 注意: 「source parser から Lean request を作る生成の意味保存は未証明」と報告にある。ここは、Yulang2 の実機との照合（監査 dot の `x-oracle.md`）と合わせて、橋が本当に必要かを確かめること。
