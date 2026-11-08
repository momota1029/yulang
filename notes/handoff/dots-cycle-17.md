# dots cycle 17: actual-producer cache invalidation

- 開始: 2026-11-08T22:40:04Z。成果復旧・公開準備完了: 22:53 UTC（約13分、承認待ちを含む）。
- integration 基点: 2ec533cd1。公開前 work/dots-main: e3b128236c8e90be2e34c8ae2e77cd3b42c0ef36。
- ローカル commit: 26ac7f00b, 0edd01ce0。
- 中断: 初回公開は Guardian の連続拒否で中断。ユーザーの明示承認後、最新先頭と5ファイルを再確認し、正規GitHub APIの非force・expected-head一括公開で復旧。拒否の具体的理由は不明。拒否を迂回したものではない。
- 変更成果5ファイル、報告と心拍を合わせ7ファイル。同一commitで公開する。読み戻し結果は会話で別途報告する。
- 焦点ビルド: `cd lean && lake build --wfail Yulang.CommonRoleCacheInvalidation`。元ログ: 285 jobs PASS, real 1.249秒。復旧時再実行も285 jobs PASS、終了コード0。
- 12宣言の `#print axioms` は propext / Classical.choice / Quot.sound のみ。sorry、新しいaxiom、native_decideは追加していない。
- 全体 `verify-lean.sh` は inbox I-6 に従い未実行。全体PASSとは主張しない。
- 復旧時空き容量19GB。元サイクル開始時の容量はこの復旧作業では未確認。

## 定理（namespace Yulang.CommonRoleCacheInvalidation）

以下 n は任意の有限source slot数。対象は既存の int-only materialization/unary-template 断片であり、一般区間全体ではない。

1. dirty_exact: 任意の前後状態、source request q、slot i について、i が dirty に属することと、i が q の端点依存slotに属し known bit が変わることは同値。
2. endpoint_unchanged: 任意の前後状態と端点 e について、e の全依存slotの known bit が等しければ、e の評価結果は等しい。
3. request_unchanged: 任意の前後状態と q について、q の全依存slotの known bit が等しければ、q の評価結果は等しい。
4. clean_iff: 任意の前後状態と q について、dirty が空であることと、全依存slotの known bit が等しいことは同値。
5. actual_next_cache_valid: 任意の registry、前後状態、q について、dirty が空なら actualNext の子リストは等しい。十分条件であり必要条件ではない。
6. changed_producer_has_dirty_dependency: 任意の registry、前後状態、q について、actualNext が異なれば、known bit が異なる依存slotが存在する。
7. dirty_is_new_evidence: 任意の前後状態、q、i について、前のatom集合が後に含まれ、後の全atomを満たすassignmentがあり、i がdirtyに属するなら、known before i=false かつ known after i=true。
8. changed_producer_has_new_evidence: 任意の registry、前後状態、q について、atom包含と後の全atomを満たすassignmentを仮定し、actualNext が異なるなら、false→trueになった依存slotが存在する。
9. dirty_cannot_repeat: 任意の状態 a,b,c,d、request first,last、slot i について、atom包含 a⊆b⊆c⊆d と b,c,d のモデル存在を仮定する。i が a→b の first のdirtyなら c→d の last のdirtyには属さない。
10. reach_cache_valid: 任意の registry、root、前後状態について、計算された領域の全Nodeでdirtyが空なら、任意の同領域Node q の Reach は前後で同値。
11. saturated_membership_cache_valid: 同じ全Node clean仮定のもと、任意のNode q の saturate への所属は前後で同値。
12. producer_change_events_bounded: 任意の registry、状態列 states:Nat→State n、queries:Fin k→SourceRequest n について、全 a≤b のatom包含、全t≤kのモデル存在、各t:Fin kでqueryのactualNextがt→t+1で変化することを仮定すると k≤n。

## B4 の残り

B4主定理は未完成。従来の5橋のうち一般化を要する残りは引き続き5本で、本サイクルは飽和の停止・閉包の橋の部品を追加した。実producer変更イベント数だけの上界であり、ordinary更新全体の停止、動的な兄弟再生成/親再計算driver、その意味的閉包、独立な最終分類・辞書同値、一般区間への接続を完成したとは主張しない。次はこの有限無効化をstate-changing driverの更新処理と結ぶ。
