# dots への現在の指示 (監督役が書く)

更新: 2026-11-08 17:30（監督役）。dots は編集しない。変わったら、更新時刻と「指示の ID」が変わる。

- 指示の ID: I-1
- 状態: ACTIVE（`STOP` と書き換えたら、dots は次のサイクルで止まる）
- 最大サイクル数: 12（これを超えたら、dots は作業を止めて待機の報告を書く）

## 現在の指示

計画表 `notes/plan/m1-plan.md` の **T1c** を担当する（開いた区間の断片で、飽和の driver と停止性、実 allocator、最終 `resolve_exact`、X13〜X16 の外側入口での証明）。T1b の続きで、`work/dots-T1b` は統合済み（`integration/m1-final` に含まれる）。

優先順位（上から。1 サイクルでは終わらない）:
1. **narrowing を扱う候補ごとの state 更新と、その後に集計する source frontier**。関連型の等式を通して別の子が決めた型が流れ込む具体例（`impl Parent (box 'a) where Left 'a, Right 'a` で、`Right` の関連型が `'a` を絞る形）を、外側の入口で通す。impl が一つしかないことから絞り込みが起きる、とはしない（spec 6.3）。
2. **実 allocator**: `Allocation n := Ty → Fin n` を外部入力にせず、Ty 端点・nominal 意味・slot/source identity を保存することを証明する。
3. **飽和の driver と停止性**: 再生成で現れた child をさらに解き、状態が安定するまで繰り返す。進捗の尺度は宣言時の Paterson 検査と K2 から導く。兄弟の順序独立は未回答なので仮定しない（成り立つなら証明の対象にしてよいが、成り立たなくても止まらない）。
4. 最終結果と独立な source Classify の iff、外側の無条件 `resolve_exact`、X13〜X16 の少なくとも一つを外側の入口で PROVED（`lean/SpecExamplesSettled.lean` か、新しい表に反映）。

## 参照

`notes/plan/m1-plan.md` の T1c、`notes/handoff/2026-11-08-dots-T1b-results.md`、`notes/design/2026-11-08-dots-T1b-producer-driver.md`、`notes/handoff/2026-11-08-dots-T1-results.md`、`notes/handoff/2026-11-08-m1-spec-examples-conformance.md`、`spec/06-roles.md` 6.2〜6.5（特に「where の子の解決は、兄弟の更新が安定するまで遅らせる」）。

## 回答済みの設計判断（監督役が転記）

- where の子は、兄弟の更新が安定するまで遅らせる。最終化はファイルの終わりの安定時。途中の曖昧・保留はエラーではない（`notes/questions/2026-11-08-T1b-sibling-recollection.md` の選択肢 1）。

## 監督役からの前回サイクルへのコメント

（サイクル報告を読んだあとに、監督役がここに書く。）
