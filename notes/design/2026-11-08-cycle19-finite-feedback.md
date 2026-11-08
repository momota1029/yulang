# Cycle19: finite fact feedback (Draft)

データ: 任意の registry/root、有限更新識別子 Fin k、識別子リストを ordinary State n に戻す decode、各 source node が発生する識別子 emit。
独立な判断: 最終状態で実 producer の Reach にある node の emit はすべて収集済み。
実行: 現在の収集済み識別子から state を作り直し、実 producer の全 source closure を再計算し、未収集の emit を一つ追加する。k 回以内の新規追加で終了する。
主定理: 全 registry/root/k/decode/emit について、最終識別子の重複なし・長さ≤k、最終 Reach の全 emit が収集済み、最終 visits ↔ Reach。
境界: decode/emit は入力adapterであり、実宣言のordinary atoms生成からまだ導いていない。順序独立・最小解・型の健全性は主張しない。これを一般B4完成と呼ばない。外部有限traceは不要になるが、有限更新領域の実宣言からの導出は残る。
Yulang2: x-oracle X13–16は内部更新を観察しない。spec6.3の安定まで最終化を遅延する方針に従う補助driverであり、新しい分類の意味論を定めない。

第二層 `CommonRoleAssociatedFeedback`: decodeを既存AssociatedBatch.runで具体化した。固定receiverを持つ有限request tableの各関連型等式は実宣言から計算される。最終ordinaryモデル集合は、初期制約かつ収集した全requestのComputed等式と同値。最終Reachのemitは収集済みなので、その等式は全最終モデルで満たされる。emitとtableのsource lowering由来性は未接続。非単調なReachに対する最小性・順序独立を主張しない。
