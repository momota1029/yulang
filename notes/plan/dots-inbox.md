# dots への現在の指示 (監督役が書く)

更新: 2026-11-08 17:45（監督役、サイクル 1 の検証後）。dots は編集しない。変わったら、更新時刻と「指示の ID」が変わる。

- 指示の ID: I-2
- 状態: ACTIVE（`STOP` と書き換えたら、dots は次のサイクルで止まる）
- 最大サイクル数: 12（これを超えたら、dots は作業を止めて待機の報告を書く）

## 現在の指示

計画表の **T1c** の続き（サイクル 1 は部分達成）。サイクル 1 で、候補ごとの局所の伝播（候補ごとに lower ≤ head ≤ upper の ordinary atoms を、直前の状態へ足して、実 ordinary solver を回し、そのあと実行可能な候補を集める）と、有限な source occurrence の allocator（`2 * row + side`）まで来た。残りは、上位の橋。優先順位（上から。今回は **50 分近く使う**こと）:
1. **宣言から制約を導く**: `impl Parent (box 'a) where Left 'a, Right 'a` で、`Right` の関連型が `'a` を絞る、という具体例を、ordinary 制約を手で渡さずに、宣言から導いて外側の入口で通す。絞り込みは impl の一意性ではなく、関連型の等式を通した型の流入（spec 6.3）。
2. **source identity**: 別々の occurrence の endpoint を、共通の source 変数へ統合する橋（graph/source identity）と、動的に生成される child への allocator の閉包。
3. **飽和の driver と停止性**: 再生成で現れた child をさらに解き、状態が安定するまで繰り返す。進捗の尺度は宣言時の Paterson 検査と K2 から導く。兄弟の順序独立は未回答（仮定しない）。
4. K2 / knownness と、language-visible な pending / selected / ambiguous / rejected の最終分類。外側の無条件 `resolve_exact`、X13〜X16 の少なくとも一つを外側の入口で PROVED。

## 余り時間の仕事（現在の優先事項が止まったときに、順に取る。独立で、競合しない）

- **T7b 到達可能性の解析（読み取りのみ・削除しない）**: `notes/plan/m1-plan.md` の T7b。Lean のメタプログラム（新規の `tools/Reach.lean` など、`lean/Yulang/` の外に置く）で、残したい定理から到達できない宣言とモジュールを列挙し、報告を `notes/handoff/` に出す。T7a の草稿（`lean/MainStatements.lean`）があれば、その Statement を根に加える。
- **T7a 主定理の主張だけのファイルの草稿**: T7a。`def ... : Prop` で主張を並べ、日本語の docstring を付ける。主張の選択に迷う点は質問ノート。

- **T4 適合例の表を一本にする**: `lean/SpecExamples.lean` と `lean/SpecExamplesSettled.lean` の状態表を、一つの一覧（X1〜X24 の状態と、通っている入口の名前）にまとめる。既存の定理は削除しない。新しいモジュールとして作り、実在する定理と一致させる。
- **T3 の下調べ**: `notes/plan/m1-plan.md` の T3（variance 表と nominal carrier の接続）を読み、既存の `CommonDeclarationVariance*`、`CommonNominal*` の定理の一覧と、足りない橋を `notes/design/` に整理する（Lean は、橋が名指しできてから）。
- **適合例の追加**: spec 6.3〜6.5 の確定した例のうち、`notes/handoff/2026-11-08-m1-spec-examples-conformance.md` にないものを拾い、候補を `notes/handoff/` に提案する（spec は変更しない）。

## 参照

`notes/plan/m1-plan.md` の T1c、`notes/handoff/2026-11-08-dots-T1b-results.md`、`notes/design/2026-11-08-dots-T1b-producer-driver.md`、`notes/handoff/2026-11-08-dots-T1-results.md`、`notes/handoff/2026-11-08-m1-spec-examples-conformance.md`、`spec/06-roles.md` 6.2〜6.5（特に「where の子の解決は、兄弟の更新が安定するまで遅らせる」）。

## 回答済みの設計判断（監督役が転記）

- where の子は、兄弟の更新が安定するまで遅らせる。最終化はファイルの終わりの安定時。途中の曖昧・保留はエラーではない（`notes/questions/2026-11-08-T1b-sibling-recollection.md` の選択肢 1）。

## 監督役からの前回サイクルへのコメント

- サイクル 1（`work/dots-main`）: `verify-lean.sh` PASS（1134 jobs、Audit、公理ゲート 82,152 宣言）、`integration/m1-final` に統合。部分達成の自己評価は正確で、「ordinary 制約を手で渡した例は、要求された完全な source 例ではない」と区別して書いた点がよい。
- サイクルの早期終了（約 12 分で待機）をやめること。標準の指示に手順 8 を足した。
