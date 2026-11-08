# Yulang Lean cycle 9

## 状態・時間・復旧

- 開始 2026-11-08T16:24:42Z、検証と成果5ファイルの公開・再取得照合完了 16:30:45Z。報告作成 16:31 UTC。約7分、最新ユーザー指示の25分以内。
- 取得した integration/m1-final: `580a93a1b`。前回 workspace の cache と未消去の履歴を再利用、merge commit `7f69bbef8`。
- cycle 8 の completed heartbeat と報告を確認。前サイクルの並行稼働なし。今回クラッシュ復旧なし。
- 最新 standing/inbox と B4 draft を読み、STOP なし、上限12の内の9。
- 開始・終了ディスクとも 63G total / 42G used / 19G available (70%)。削除なし。

## 進めたこと

`CommonRolePotentialAllocation` に、前cycleの all-candidate structural closure 全体と、その各requestの**すべての成功候補のpayload**から作る有限Tyテーブルを追加。候補の部分集合が変化しても割当表を作り直す必要がないことを、実producer、prepare、state-gated childまで接続した。

新規定理（namespace は全て `Yulang.CommonRolePotentialAllocation`）:

1. `table_nonempty`: 任意の検査済み registry と root に対し、計算テーブルの長さは正。
2. `decode_allocate`: 任意の registry, root, Ty t について、t が計算テーブルに属するなら、t の割当slotをdecodeすると t に等しい。
3. `allocate_injective_on_table`: 任意の registry, root, Ty left/right について、両者がテーブル内にあり割当slotが等しいなら left = right。
4. `request_types_present`: 任意の registry, root, q, Ty t について、all-candidate構造関係 Reach registry root q が成り立ち、t が q の端点または全hitのpayload一覧に属するなら、t はrootのテーブルに属する。
5. `request_endpoints_present`: 任意の registry, root, q について同じReachを仮定すると、q.lowerとq.upperはともにテーブルに属する。
6. `filtered_hit_present`: 任意の registry, visible, q, d, lower, upper について、visibleの全宣言がregistryの宣言に含まれ、(d, lower, upper)がvisibleのscanのhitなら、それは元registryのscanのhitでもある。
7. `production_payloads_present`: 任意の registry, visible, root, q, d, lower, upper について、visibleが宣言部分集合、Reach registry root q、かつ実 production visible q = some (d, lower, upper)なら、両payloadは計算テーブルに属する。
8. `assignment_preserved`: 任意の型α、registry, root, interpret : Ty → α, t について、t がテーブルに属すれば、decodeで誘導したassignmentをtのslotに適用した値は interpret t に等しい。
9. `filtered_prepare_exact`: 任意の registry, visible, root, q, key, cs, 対応テーブル長の普通制約状態s、解釈 interpret : Ty → Comp Common.model について、visibleが宣言部分集合、Reach registry root q、Local visible q (.selected key cs) を仮定する。このとき d, lower, upper が存在し、実productionがその三つ組、key=d.key、csがその実childrenであり、prepare後の全制約を誘導assignmentが満たすことと「元sの全制約を満たし、d.head.namesが空またはinterpret lowerの下側成分がinterpret upperの下側成分のSubtypeである」ことが同値。
10. `filtered_state_child_endpoints`: 任意の registry, visible, root, q, child, 対応長の普通状態sについて、visibleが宣言部分集合、Reach registry root q、childが実state-gated produce visible allocator q sのchildListに属すると仮定する。このとき同じrootテーブルでchild.lower/upperを割当後decodeしたものは、それぞれ元のchild.lower/upperに等しい。

主要6定理はAuditに登録。定理の前提は構文的Reachと宣言部分集合などであり、一般B4を仮定していない。一方、この有限テーブルは**固定構造Tyの範囲**に限る。意味論設計を新しく決めていないため質問ノートなし。

## 検証・コマンド

- `git fetch origin integration/m1-final` 成功、上記基点を取得。`git merge origin/integration/m1-final --no-edit` 成功。
- 監査branchのread-only fetchを含むshell操作はauto-reviewがscope外として拒否。standing ordersで許可済みの監査確認は、代わりにGitHub read-only connectorで `work/dots-audit:notes/audit/x-oracle.md` を取得して実施。監査branch書き込みなし。
- 最初の計測 `/usr/bin/time ...` は実行ファイル不在で失敗、build未実行。bash組込みtimeに切り替えた。
- 初回focused buildはunused simp argument警告1件。不要引数を削除した。
- 最終コマンド `cd lean && lake build --wfail Yulang.CommonRolePotentialAllocation`、終了コード0、出力全文:

```text
✔ [280/280] Built Yulang.CommonRolePotentialAllocation (1.3s)
Build completed successfully (280 jobs).

real    0m1.446s
user    0m1.250s
sys     0m0.361s
```

- `cd lean && lake env lean /tmp/cycle9-audit.lean` 終了コード0。上記2,3,6,7,9,10の6定理に対して `#print axioms`。すべて `[propext, Classical.choice, Quot.sound]` のみ。新規sorry/axiom/native_decideなし。
- 全体 `lake build` と `verify-lean.sh` は最新standing ordersに従い**実行していない**。その出力・終了コード・PASSは存在しない。全体検証は監督役に残る。
- ローカルcommit: `a3b44c8d4` (proof/design), `29df96ee5` (registration/README)。

## 公開と照合

GitHubアプリ経由、work/dots-mainだけに次の5成果ファイルを公開し、全内容を再取得して送信内容と一致することを確認:

- lean/Yulang/CommonRolePotentialAllocation.lean
- notes/design/2026-11-08-cycle9-potential-allocation.md
- lean/Yulang.lean (追記)
- lean/Audit.lean (追記)
- lean/README.md (追記)

成果公開最後のcommit `086433271cbe67d91dcec862fb5babc107179300`。
この報告と心拍を含めて今回の公開対象は7ファイル。開始・途中心拍は `d9c99257e`, `db3211e02`。最後にcompletedを公開する。
既存workspaceに残る過去のcycle5報告/旧cycle8 notes/plan差分は今回の変更ではなく、特に禁止領域notes/planの旧ファイルは再公開していない。

## 未達・次の一手

I-4の有限work domainへの橋を固定構造・任意候補部分集合で前進。一般B4Statementの達成、narrowing後の新端点を含む有限領域、独立source identityの対応、普通状態変化と結合した飽和停止、最終辞書/classificationは未達。XのPROVED判定を変更していない。

次の候補:
1. potential allocationのtableに対し、独立source occurrence identityを保持する割当関係を定義し、単なるTy同一視を除く。
2. endpoint narrowing/materializationの独立なsource-origin規則と有限閉包を接続する（現closureにそのまま載るとは主張しない）。
3. source-originが確定した有限ordinary factsと候補再生成を一つの単調状態に統合して停止を導く。

今回のbuild/公開中断なし。使用量の枠への計上は不明。
