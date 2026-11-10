# dots cycle 75 — ordinary graph境界監査とcycle69〜75の公開復旧

## 結果

**六モジュールの入力台帳と境界検査を完了し、cycle69〜75の保全済み成果18pathを公開した。**
ソース公開commitは [`02702246a9d188acb6915b142589ed8d1b9b76c0`](https://github.com/momota1029/yulang/commit/02702246a9d188acb6915b142589ed8d1b9b76c0)。
公開treeは `fa35eab2e10bbbf1f65338d775dd04331d311d42` で、local検証済みHEAD
`352c10cf972d913b80bce0c3654a63b850916153` のtreeと完全一致する。

- 台帳L節で、`CommonRoleRegularGraph`、`CommonRoleGraphBisimulation`、
  `CommonRoleGraphInspection`、`CommonRoleDeferredBounds`、
  `CommonRoleGraphDemandSnapshots`、`CommonRoleCandidateConstraints` のcaller入力、
  依存定理、sourceから導く必要がある対応、spec6.2〜6.5との関係を整理した。
- production Lean変更0、新規production定理0、新規質問0。cycle69で追加した
  addressed captureのコードは変更せず、未公開分として今回まとめて公開した。
- inventoryは242モジュール、Main到達93、Audit到達242、台帳言及103。
  **言及数は入力監査完了数ではない。I-13は部分達成のままで、cycle72の公開期限は超過した。**
- B4主要5橋、M1全体の健全性・完全性・主型性は未完。

## 閉じた部分目標と確認した境界

部分目標は「ordinary graph読出しと候補制約への受渡しに残るcaller入力を区別し、
source接続時に誤って使える含意を境界検査で否定する」。次を確認した。

1. 異なるunresolved nodeは全深度の表示観測が等しくてもbisimilarではない。
   観測一致からbisimulationへ戻す定理のclosed前提を落とせない。
2. 低位inspectのvariable captureと、rootの再帰を先に記録するsnapshotは役割が違う。
   identityによるcycle検出とbisimulationによるregularityも同じ判定ではない。
3. lowerHeadsはunknownを除く一方、all-contributionsはunknownを保持する。
   重複seedとflow元のsource slotも保持し、upperだけではlower寄与を作らない。
4. headのmismatch観測とordinary solverの非空scheme族は共存できる。
   ordinary成功を候補成立やK2安全性にそのまま接続できない。
5. capture-only抽出は不成功兄弟の観測を落とす。同名capture二本からは
   四つの自己・交差atomを生成する。全観測を使う候補判定は別に必要である。

必要な接続は、ordinary stateとgraph/problemの意味対応、unknown identityと
slotBoundsのscope対応、上下界の合流と候補ごとのordinary整合、全観測を保持する
適用候補/K2判定、更新後の再読出しとwhere/associated feedbackの安定化である。
これは既存の主要橋の内訳で、新しい言語意味を選んだものではない。

## 検証

保存ログではfocused build、境界検査、diff-only gateが全てexit 0だった。
公開復旧後にも同じsource treeで次を実行した。

```text
cd lean
ELAN_HOME=../../elan timeout 120 ../../elan/bin/lake build --wfail Yulang.CommonRoleGraphDemandSnapshots Yulang.CommonRoleCandidateConstraints
Build completed successfully (275 jobs).
exit 0

ELAN_HOME=../../elan timeout 120 ../../elan/bin/lake env lean --trust=0 ../../cache/yulang75/boundary-check.lean
exit 0
```

scratch検査は20個のexample、2個の名前つき境界命題、1個の共有補助証明。
計22境界assertionと補助証明を通し、11対象定理の公理出力は
`propext` / `Classical.choice` / `Quot.sound` のみだった。
ログは `cache/yulang75/recovery-focused.log` と `recovery-boundary.log`。

`python tools/boundary-input-inventory.py --check` はexit 0:

```text
PASS: inventory matches source hashes, imports, and ledger mentions.
CommonRole import scope=242; Main=93; Audit=242; ledger mentioned=103. Mention counts are not audit completion counts.
```

`git diff --check origin/integration/m1-final HEAD` と
`git diff --quiet 4d40caffd HEAD -- lean` はexit 0。
保存済みdiff-only gateの全文:

```text
verify-lean: . @ 352c10cf9 (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)
```

dotの作業場では全体lake build、全Audit/AxiomGate、build付きverify-leanは実行していない。
source commit `02702246` のGitHub CIは両方successを確認した:

- [Core CI](https://github.com/momota1029/yulang/actions/runs/42788031206):
  core成功、2026-11-10T09:07:48Z終了。
- [Lean inference kernel](https://github.com/momota1029/yulang/actions/runs/42788031161):
  proof成功、2026-11-10T09:08:35Z終了。build、全宣言の監査、例の実行stepが成功。

この報告とcompleted心拍を載せる後続commitは記録のみで、Lean sourceは同じ。
ただし後続commit自体のCIを上記source commitの結果と取り違えない。
新しいYulang2実行やparser実行はしていない。

## 公開の中断・復旧と照合

cycle69のcommit作成拒否後、cycle70〜74は新承認がなく公開していなかった。
cycle75でユーザーが、work/dots-mainの更新に必要なGit object作成を明示承認した。
integrationその他のrefは引き続き更新対象外とした。

1. 最初の公開担当はpayload読込中に中断した。履歴と保存状態を確認し、
   承認後のcreate_tree/create_commit/update_refが全て未実行と確定した。
2. 引継ぎ後、18pathを含む大きなcreate_tree要求を1回呼んだが、410.6秒で中断。
   成功・拒否の応答はなく、直後は結果不明と扱った。期待treeと18blobを読み取りで
   確認し、全て404、work refも不変だった。明示拒否を別経路で回避していない。
3. 同じ承認済み内容を個別blobとして準備し、全18blobの応答SHAをlocal内容と照合。
   SHAだけの小さいtree要求が成功し、期待tree `fa35eab2e…` と一致した。
4. 最新integration `434d3ceefce3bc2dbd8d5cb5d84c6295a9c40cf8` を親とする
   commitを作り、expected old head `872066861d13cfa1784bffdaa7bfbb973998c00f`、
   `force=false` でwork/dots-mainだけ更新した。commit時刻は09:07:03Z。
5. live work ref、commitの親とtree、recursive tree全2281entryを再取得した。
   18path全blobが一致し、tree全体もlocal検証treeと一致。対象外pathを保持した。
   integration/m1-finalのrefは `434d3ceef…` のままと確認した。

source公開は18path。本報告の新規追加と心拍更新を含めると、保全・公開した対象は
合計19個の異なるpathになる。過去のcycle報告の「未公開」は当時の履歴として残した。
この報告が現在の公開状態を更新する。失われたsource成果は見つからなかった。

## 時間・資源・再開

- cycle75開始心拍: 2026-11-10T08:27:36Z。
- source準備完了のlocal心拍: 08:32:57Z。remote心拍ではなかった。
- source公開commit: 09:07:03Z。開始から39.5分。
- この完了記録の準備: 09:09:45Z。開始から42.2分。
- **公開中断と復旧を含むwall-clockで25分上限を超過した。期限内完了とは報告しない。**
  開始・10分間隔のremote心拍も満たせなかった。研究を延長したのではなく、
  公開・検証・記録の復旧に要した時間である。
- 確認時空き48G/全63G、使用13G。同じ作業場とcacheを再利用し、追加worktreeなし。
  使用量枠は不明。

今回の作業はここで閉じる。次サイクルは再開可能。最初にlive workと最新integration、
standing orders/inboxを読み、completed心拍と本報告を確認する。公開済みsourceを
再度作ったり、古いtracking refだけを根拠に上書きしたりしない。
ローカル履歴とAPI公開commitのIDは違うが、source treeの一致を確認済みである。

残るB4主要橋は5本:
`source_boundary_adequate`、`generated_work_closed`、`saturate_terminates_and_closes`、
`saturated_frontier_exact`、`resolve_dictionary_order_sound`。

次の候補は、Mainのassociated/where exactness全入力と台帳の対応、
sourceからordinary graph/readoutへのadequacy設計、残る未列挙moduleの監査。
Q1/Q2とcycle23/24の未決事項は維持し、意味論を勝手に選ばない。
