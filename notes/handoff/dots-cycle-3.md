# dots cycle 3 — 再開・I-3 部分達成

- 開始: 2026-11-08T11:31:16Z
- 報告作成: 2026-11-08T12:22:42Z（開始から 51.44 分）。最終終了時刻は末尾の公開確認欄。
- 取得した基点: `b6012d3874f893c37f4834f40d2320d927b68860` (`origin/integration/m1-final`)。
- 最終 Lean 検証対象: `514c65248`。その後は文書のみ変更し、Lean tree 不変を `git diff --quiet 514c65248 HEAD -- lean`（exit 0）で確認。
- 最終成果ローカル commit（報告追加前）: `708ad7ee6`。
- 結論: **verify-lean PASS。T1c/一般B4は未達。X13〜X16の外側PROVEDは増えていない。**

## 復旧ではなく再開

ユーザーの最新指示「今回はもう無視して再開してください」に従い、以前の未公開サイクル3救済を中止したうえで、新しいクローンで現在の基点から作業した。前回の未公開ファイルを成果に混ぜていない。開始時点の最新公開報告はcycle 2、以前の心拍は取得できず、今回をcycle 3とした。以前の中断原因や失われた証明を推測していない。今回は環境再作成・実行中断なし。

開始直後と約10/20/30/40/50分に `notes/heartbeat/dots-main.md` を更新した。20分時点には直前18.5分の追加心拍もある。心拍とは別に中間成果を複数回公開した。今回の実行中に次の定刻起動が来たが、親側が心拍を確認して同時writerを開始しなかった。

## 何を証明したか

新規9モジュール、73の公開定理。`Main`には11定理（従来草稿8件の同じ型での昇格と今回の3再掲）。全84項目の日本語の主張と**前提・量化子を省略しない宣言型**は [定理一覧](2026-11-08-dots-cycle-3-theorems.md)。73公開定理すべてにAudit登録があることも機械確認した。

1. `CommonRoleStatefulParentExample.outer_exact`: 固定された3slotの具体例について、**任意の**出力状態out、引数argument、辞書answerで、実seed→逆順Index依存辺2sweep→実ordinary solver→materialize→実Parent辞書の成功 iff 独立Final。既知receiver `Right str` の実 `type value = str` が流入し、最終Parent(box a)のLeft/Rightは**同じa**を要求する。ordinary atomsを入口へ手渡していない。seed RightとParentは同じregistryだが、途中Indexは別の既存checked registry。
2. `CommonRoleSourceDescent`: **任意の**source occurrence表・評価について、同名occurrenceの型coherence iff source名の型評価への因子化。実solverの受理とのiff、使用された名前上の一意性も証明。効果の同一視は主張しない。
3. `CommonRoleStatefulPathComplete.checked_exact` / `PathParent.outer_exact`: **任意の**n、有限output path、receiver、旧ordinary状態s、結果out/argument/answerについて、実宣言seed・状態を渡すpath・実solver・Parent辞書の成功 iff 明示した生成後状態のModelsと独立辞書。成功・Models・fuelを外部前提にしない。旧型/効果制約は保持する。pathは入力で、停止は有限リストの構造再帰。
4. `CommonRoleNamedPath.outer_exact` / `success_domain`: **任意の**seed識別名、有限名前列、計算したslot数の旧状態と結果について、slot割当と同一source制約を実際に計算して上の入口を実行する。成功領域は、旧制約を満たし全slot型がstrと同値となる評価の存在とiff。空状態からの成功と旧不整合の拒否も証明。seedの型が任意なのではなく、固定Index(box str)由来。
5. `CommonRoleSiblingOrders.orders_models` / `orders_observable`: 固定Index依存2辺をforward1回とreverse2回で解いたとき、**任意評価**で最終モデル集合が等しく、実入口の(argument,辞書answer)も等しい。内部atom列は重複があるため等号を主張しない。Parentのwhere自体の任意置換定理ではない。
6. `CommonRolePathOrder.observable_order_independent`: **任意の**有限2path、同じtarget membershipである証拠、receiver、旧状態について、実Parent入口のobservableが一致する。成功/Models前提なしでnoneの場合も含む。置換は系で、重複個数も変えられる。これは固定str seedの有限path断片で、一般動的where graphの順序独立ではない。
7. `lean/Main.lean`を許可された位置へ昇格。従来8定理の宣言型が草稿と完全一致することを比較確認。全言語完成を宣言するPropは追加していない。

## 受け入れ条件と未達

| I-3 | 状態 |
|---|---|
| 宣言から制約→外側の具体例 | 上記のchecked Leanデータ上で達成。source例も実parser確認。ただしsource parserからLean request生成への意味保存は未証明 |
| source identity | 型評価の降下、計算された有限名前pathのslot割当まで。一般動的childのallocator閉包は未達 |
| 飽和と停止 | 実状態更新、逆順再走査、任意有限path、path内順序独立まで。Paterson/K2由来の一般飽和停止は未達 |
| 四方向分類・一般resolve_exact・X13〜X16 | 未達。新しい成功iffを全言語のpending/selected/ambiguous/rejected分類と呼ばない |
| T7a | Main昇格と限定範囲の明記を達成 |
| T7b | 根を全Audit＋Main＋X入口へ拡張して実測。削除なし |

X22は以前の独立source entryの既存証明をMainに再掲しただけで、今回新たに全Core.inferへ統合したものではない。

次の1〜3補題候補は [次の飽和の橋](../design/2026-11-08-restart-next-saturation.md) に量化子・前提・結論付きで記録: (A) 実生成childのsource provenance/有限仕事領域、(B) 新情報のない再訪を除いたdriverの停止と意味的閉包、(C) 安定状態から独立四方向分類・有限辞書への無条件iff。これらは未証明の案であり、既存Lean宣言と偽っていない。今回、新しい意味論選択が必要な点は決めていない。質問ノートの新規追加なし。

## コマンドと検証

Lean: `leanprover/lean4:v4.35.0`、既存elan環境を再利用。fresh clone/fetch後、基点も検証した。

| 実行 | 結果 |
|---|---|
| 基点 `bash tools/verify-lean.sh . origin/integration/m1-final` | PASS, exit 0, 1147 jobs |
| SourceDescent/Main focused build | PASS, 391 jobs |
| Stateful各module focused build | PASS（worker側の281 jobsとtrust=0監査を含む） |
| PathComplete focused | PASS, 280 jobs |
| PathParent focused | PASS, 283 jobs（記録上約46秒） |
| NamedPath focused / Main | PASS, 285 / 400 jobs |
| SiblingOrders focused | 修正後PASS, 281 jobs |
| PathOrder focused | PASS, 284 jobs |
| 中間全体verify | PASS, 1149 / 1154 / 1155 / 1156 jobs（各exit 0） |
| 8新規module+Mainを `lake env lean --trust=0 <file>` で直接再検査 | 全exit 0、計10秒。最後のPathOrderも別途直接再検査exit 0 |
| `git diff --check origin/integration/m1-final..HEAD` | exit 0 |

最後の必須検証開始 `2026-11-08T12:18:05Z`、終了 `2026-11-08T12:18:53Z`、所要48秒。コマンド:

```sh
bash tools/verify-lean.sh . origin/integration/m1-final
```

出力全文:

```text
verify-lean: . @ 514c65248 (base origin/integration/m1-final)
ok: lake build --wfail (Build completed successfully (1157 jobs).)
ok: Audit.lean exit 0
ok: axioms only propext/Classical.choice/Quot.sound over 6299 printed declarations
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended
ok: AXIOM-GATE-PASS: 82887 declarations
verify-lean: PASS
```

終了コード: **0**。生成物はcommitしていない。既存Leanファイルの削除/変更はなく、許可された集約3ファイルへの追記、許可されたMain/library追加のみ。

### 途中の失敗を含む記録

- SourceDescent初稿のBool等式変換/末尾証明、PathCompleteのOption bind帰納法、PathParentの大きな簡約でのheartbeat timeoutを修正してからfocused/full検証を通した。失敗した初稿は完成扱いしない。
- SiblingOrders初稿は`explicit_pair_detected`を追加制約のある状態へそのまま使って型不一致、次の修正では展開順でsimp未解決/unused警告。実状態のdetect計算と明示した中間状態へ修正し、wfail込みでPASS。
- cargoは最初PATHに無かったが、既存`audit-cargo`/`audit-rustup`を発見。offline実行はuncached `anyhow`で失敗。通常cargoで既存parserをビルド（28.33秒）、独立`/tmp` targetを使用。
- source例初稿は必須Index method/box宣言不足をレビューで修正。実parserはstandalone Parent head/カンマwhereで6件recoveryを報告（exit 1）。spec既存のstruct-with implと反復whereへ修正してPASS。CST確認で式内colonが型注釈でなくapplicationだと分かり、binding注釈へ修正して再PASS。
- 最終source例: `syntax_guide_check ... --quiet` は1 block ok、recovery 0、exit 0。`cargo test --offline -p yu-syntax --lib where` は15 passed/0 failed、exit 0。Rust sourceは変更なし。型検査・source→Lean loweringは未検証。
- GitHub README追記が1回、自動reviewに別のauditブランチ制約と誤認され拒否された。standing ordersのwork/dots-main許可を再取得し、現在内容を完全に保つ2行追記と実証して同じAPIを再試行、成功。迂回経路は使っていない。

## 公開と照合の範囲

GitHubアプリから **work/dots-mainだけ**へ公開。他ブランチへ書いていない。成果24ファイルを公開済み（最後のcode/doc一括時のremote `b18765362e6ef80ed2580d11136d0ae915453127`、その後reachability文書の追加更新あり）。24対象の内容一致と、**lean/全体**の一致をfetch後のgit diff exit 0で確認した。本報告を含め成果25ファイル、心拍1ファイルの計26対象になる。

注意: 公開branch全体とintegration基点を同一だとは主張しない。work/dots-mainには以前の監督用spec/plan/toolsが残り、最新integration基点はそのGit履歴の祖先ではない（merge-base exit 1）。remoteの古いverify scriptにはMain許可前のgateも残る。指定どおり、最新integrationのローカルcloneへ成果を重ねて、その**最新gate**で検証した。監督所有のspec/plan/toolsを勝手に上書きしていない。取り込みは最新integrationへ列挙した成果ファイルを反映する形を前提とする。

成果ファイル（本報告以外）:

- `lean/Audit.lean`
- `lean/Main.lean`
- `lean/README.md`
- `lean/Yulang.lean`
- `lean/Yulang/CommonRoleNamedPath.lean`
- `lean/Yulang/CommonRolePathOrder.lean`
- `lean/Yulang/CommonRoleSiblingOrders.lean`
- `lean/Yulang/CommonRoleSourceDescent.lean`
- `lean/Yulang/CommonRoleStatefulIndexPath.lean`
- `lean/Yulang/CommonRoleStatefulIndexSweep.lean`
- `lean/Yulang/CommonRoleStatefulParentExample.lean`
- `lean/Yulang/CommonRoleStatefulPathComplete.lean`
- `lean/Yulang/CommonRoleStatefulPathParent.lean`
- `lean/lakefile.toml`
- `notes/design/2026-11-08-restart-main.md`
- `notes/design/2026-11-08-restart-named-path.md`
- `notes/design/2026-11-08-restart-next-saturation.md`
- `notes/design/2026-11-08-restart-path-completeness.md`
- `notes/design/2026-11-08-restart-path-order.md`
- `notes/design/2026-11-08-restart-sibling-orders.md`
- `notes/design/2026-11-08-restart-source-descent.md`
- `notes/design/2026-11-08-restart-stateful-example.md`
- `notes/handoff/2026-11-08-dots-cycle-3-reachability.md`
- `notes/handoff/2026-11-08-dots-cycle-3-theorems.md`

## 公開後の最終確認

2026-11-08T12:23:03Z に remote `27d6f778242f38856a6cc0653baee232092c0006` を取得し、本報告を含む25成果ファイルがローカルと完全一致（`git diff --exit-code ...` exit 0）、lean/全体も一致（exit 0）と確認した。開始からこの確認まで51分47秒。この確認欄の追記は同じブランチへ反映し、その後completed心拍を公開する。完了通知処理を含む終了時刻・経過分は最終心拍のupdated/elapsed_minに記録する。

公開数: 成果25ファイル＋心拍1ファイル＝26対象。全体PASS、未達は上記のとおり。これ以降、次サイクルまで作業を広げない。

## 使用量・実行制限

今回の実測継続時間は上記開始から最終確認まで。プラットフォームのジョブ上限・使用量枠への課金内訳は、この実行のツールからは不明。実測時間を最大許容時間と同一視しない。セッション再作成やタイムアウトによる作業中断は今回なし。
