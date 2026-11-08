# dots cycle 7: finite-graph declaration exactness and capacity recovery

開始: 2026-11-08T15:24:58Z。成果の公開・照合: 15:32:04Z。
対象 integration/m1-final: `db39e19572a5571ffc0082cbc4f12310ad6d1733`。
最新の standing orders / inbox I-4, I-5, I-6 を再読。STOP ではない。
25分以内の上限を優先し、全体ビルド・全体 Audit・verify-lean は実行しない。

## 復旧と容量

前回心拍は cycle 6 completed、報告も存在。クラッシュと再判定せず、
前回報告の容量不足を I-6 に従い解消した。
保持した作業場は `/workspace/scratch/1d0b4aaa3394/yulang-cycle6`。
最初に integration を取り込み、質問ノートの競合は監督役の回答を優先した。

未公開 local commit の検査は `git log --oneline HEAD --not --remotes`。
旧 worktree には API 公開と異なるローカル commit が複数残るため、
ソース worktree と commit は削除しなかった。稼働ビルド作業場は一つに限定し、
それ以外の24個の `lean/.lake` 生成キャッシュだけを削除した。
削除量 14,886,979,722 bytes。`df -h` 空きは 4.3GB → 19GB。
記録: `/workspace/scratch/1d0b4aaa3394/cycle7-cache-cleanup.tsv`。
I-6 の容量確保とキャッシュ一本化は達成したが、全ソース worktree の一本化は未達。
旧ログも削除していない。未公開履歴を失わないことを優先した。

## 新しい一般定理

新モジュール: `lean/Yulang/CommonRoleFiniteAssociatedDeclaration.lean`。
固定サイズ・固定例でなく、任意の自然数 n、n 個の slot を持つ有限 source graph、
任意の旧 State、任意の fact を対象にする。新しい判断 `DeclarativeDerives`
は初期 Evidence、同一 source identity の伝播、独立な関連宣言導出による伝播の
帰納的閉包。実行版 Computed / assocOf / resolve / saturation を判断の定義に使わない。

以下で env は任意の AssocEnv、roles は任意の RoleDecls、
wf は WellFormed env.cores、awf は AssocWellFormed env roles、
p,q は任意の Source n、s は任意の State n、f は任意の Fact n とする。

1. `derives_exact` (健全性・完全性の橋): wf, awf の下で、
   旧グラフ導出 Derives env roles wf p s f と DeclarativeDerives env roles p s f が同値。
2. `saturate_declaration_exact` (健全性・完全性): wf, awf の下で、
   f が実際の saturate env roles wf p s に含まれることと独立宣言導出が同値。
   successful-run、十分な fuel、閉包済み universe を仮定しない。
3. `run_declaration_exact` (健全性・完全性): wf, awf の下で、任意の slot と head について、
   実行後の ordinary state に Evidence があることと、旧状態から (slot,head) が
   独立宣言導出されることが同値。
4. `declaration_congr` (補助・順序独立): wf, awf は不要。
   全 a,b で p.identity a=p.identity b iff q.identity a=q.identity b、かつ
   全 occurrence r で r∈p.occurrences iff r∈q.occurrences を仮定すると、
   全 f について両グラフの独立宣言導出が同値。順序や重複に依存しない。
5. `saturate_membership_congr` (補助・実行の順序独立): wf, awf と4の2前提の下で、
   全 f について p と q の実行キャッシュへの所属が同値。
   リスト順や辞書の同一性を主張していない。
6. `declaration_stable` (補助・閉包): wf, awf の下で、全 f について、
   実際の run 後の状態からの独立宣言導出と、旧 s からの独立宣言導出が同値。

主張はいずれも principality の証明ではない。
実行を含んでいた関連ステップを独立宣言判断につなぐ、有限 scalar 断片の一般結果である。

## 検証

実行した焦点コマンド:

```sh
cd lean && lake build --wfail Yulang.CommonRoleFiniteAssociatedDeclaration
```

初回出力全文 (exit 0):

```text
✔ [282/282] Built Yulang.CommonRoleFiniteAssociatedDeclaration (2.2s)
Build completed successfully (282 jobs).
```

stability 追加後の出力全文 (exit 0):

```text
✔ [282/282] Built Yulang.CommonRoleFiniteAssociatedDeclaration (911ms)
Build completed successfully (282 jobs).
```

新モジュールだけを import する `/tmp/cycle7-axioms.lean` に6個の
`#print axioms` を置き、`lake env lean /tmp/cycle7-axioms.lean` を実行 (exit 0)。
出力全文:

```text
'Yulang.CommonRoleFiniteAssociatedDeclaration.derives_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleFiniteAssociatedDeclaration.saturate_declaration_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleFiniteAssociatedDeclaration.run_declaration_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleFiniteAssociatedDeclaration.declaration_congr' depends on axioms: [propext]
'Yulang.CommonRoleFiniteAssociatedDeclaration.saturate_membership_congr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleFiniteAssociatedDeclaration.declaration_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

sorry、新公理、native_decide なし。全体の verify-lean.sh 出力は存在しない。
監督役の全体検証を待つ。上記 focused PASS を全体 PASS と呼ばない。

## B4 の未達と次の橋

Main.B4Statement は依然、未証明の目標 schema。
前回整理した5個の大きな橋は依然すべて残る:
source_boundary_adequate / generated_work_closed /
saturate_terminates_and_closes / saturated_frontier_exact /
resolve_dictionary_order_sound。
これは5個の短い補題という見積もりではなく、構成が必要な5課題である。
今回の結果は3番目の有限 scalar 関連宣言断片を独立意味論につないだもので、
動的 where/capture の生成域、一般区間 knownness、K2付き外側分類、辞書を完成していない。
X13–X16 の一般外側入口を PROVED に変更していない。

次の候補:
1. generated_work_closed: 実 producer が生成する全 where/capture request の source provenance。
2. saturate_terminates_and_closes: その生成域の有限性を実 sibling/parent 再生成へ結ぶ。
3. saturated_frontier_exact: 回答済みの「子結果を保持する未完成診断 tree」を接続。

Y2 の公開監査 x-oracle を参照した。古い実装の有限の例は一般区間・動的生成を
検証しないため、実装を一般仕様の根拠にはしていない。Y2 の新規実行なし。
分類境界の回答を読み、最終分類写像や辞書同値の新しい意味論は選ばなかった。
新しい質問ノートは不要だった。

## 公開と制限

書き込みは work/dots-main のみ。
新規モジュール、Yulang.lean の import、Audit.lean の6宣言、README の説明を
1ファイルずつ GitHub アプリで公開。取り戻した全 lean tree と検証済みローカル木は
`git diff --exit-code origin/work/dots-main -- lean` が0で完全一致。

公開 commit: 9d653d4f / 46fe9e68 / af2606df / 0b22428f。
local proof commits: 5a3d45ead / 5ff4a9c6b / 49b6b79dc。
integration 取り込み commit: 976758c2642aa3bc51b10569b0e5a160b4e56ab7。
この merge の28ファイルは既存 integration と全 blob 同一で、spec/plan を新たに
編集したわけではない。integration が公開ブランチの祖先である検査も exit 0。
以前の cycle5 未完 draft/type appendix は完了報告として再公開していない。

今回新規・追記した公開対象は6ファイル (Lean等4、報告1、心拍1)。
キャッシュ清掃以外の破壊的変更、実行中断、承認待ちはなかった。
使用量の枠の計上は取得できず不明。

報告準備終了: 2026-11-08T15:33:05Z。開始から8分7秒。最終公開確認の時刻は completed 心拍に記録する。
