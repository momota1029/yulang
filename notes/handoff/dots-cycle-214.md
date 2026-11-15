# dots cycle214 — corrected all-shape head replay and retained overlaps

開始: 2026-11-15T14:33:27Z。予定14:30UTCの回。検証・公開・報告の締切は15:25UTC。
開始時に integration/m1-final を再取得し、standing orders と inbox I40 を読み直した。
開始時integration: `3c7ba73facef43f4e94e5cb9f79db22bbec4661f`。最終再取得で`92a801be7642ed7ffcdafbcab0a99c5b0ff034e5`へ更新（既存213の統合）。plan/standingに変更なし。重複した213履歴をmergeし、競合したumbrella/indexは監督版が完全なprefixであることを照合して214追記だけを保持した。213は完了済み、前のwriterなし。
STOPなし。制限時間はユーザーの最新55分上限を文書の長時間指示より優先した。

## 結果と前提

I40の最終目標 `B4SkeletonV7.EvidenceNode (DefaultBoundary208.boundary roles)` は未完成。
Step/Stable/Local/Models、選択範囲、全体の目標は変更していない。FreshCompletionは撤回されたまま。
以下はその計画で必要な補題であり、全体のEvidenceNode証明とは区別する。

- `Choice214.choice_iff_prepared`: Checked・Reachable・現在selectedの全域で、ChoiceCompatibleと、同じaliasクラスの全履歴宣言が現在Preparedであることは同値。宣言の可視性とrole一致は実際の208遷移から導いた。Preparedの持ち越し自体は未証明。
- `Overlap214.solution_iff` / `journal_extension`: 任意の有限total等式について、右辺の読みを保持できる条件下で、同じtargetの右辺どうしの意味的同値と、保持対象との意味的一致を正確な拡張条件にした。targetの相異・一律freshness・構文的一致は要求しない。重複target・保持された自己参照・構文的には異なる同値値の閉じた回帰例も通した。
- `ActualFullSources214.full_support_binder`: InitialSource・InstalledDepthBound・実際の208 Stepsの下で、元の213 journalSourcesに現れる任意のpurpose8名は、保存済みplanのbinderに由来する。total emitted/child schema、明示/default snapshot/live effectsも含む。shadowedな生構文変数を宣言済み入力と誤認せず、任意のbinder由来として扱う。
- `FullFreshness214.support_historical` / `fresh_support_separate`: 同じ前提で、purpose8の全journal supportとの交差からHistoricalInvocationを導く。その否定から完全なfresh分離を得る。都合のよい小さいsupportへの置換はしていない。
- `IdentityCenters214.registered_identity_centers_same`: Checkedと実際の208 Steps・journal Modelsの下で、同じ数値identityの任意の登録siteのcenterは意味的に一致する。旧Stepへのモデルのcastやreportの構文的一致は使わない。
- `CandidateActual214.candidate_actual`: 同じinvocation/declarationの保存planと現在Frameを持つ候補について、現在の各actual head useは保存binderと意味的に一致する。候補のhead等式を結論の前提にはしていない。
- `Conservative214.conservative_extension_iff`: InitialSource・depth bound・実際のtrace・Checked・現在Frame・journal modelの下で、有限actual head useの保存的拡張は、観測値の存在・capture BoundsFit・binder衝突時の意味的一致と同値。履歴とのoverlap一致は導出した。全旧journalモデルと現在capture端点を保持する。
- `HeadEquationExtension214.head_equations_extension_iff`: 全head変数・tests・登録input射影をまとめたHeadEquationsの保存的拡張の正確な同値条件。任意の一変数だけの主張ではない。
- `Revisit214.revisit_extension_iff_bounds`: 同じ数値invocation/declarationの登録済みplanがあるとき、現在Frame・元journal modelについて、HeadEquationsの保存的拡張は現在BoundsFitと同値。tests、観測値存在、衝突整合、Finishedは導出される。変数・named・structural・scalarを一様に扱い、point入力や同じreportには限定しない。
- `RawBranch214.head_and_branch_extension_iff`: 同じjournal modelに現在のraw HeadModelsも成立している場合、上記head拡張中にそのraw branchを保持できる。別々の存在証人を勝手に結合してはいない。現在private/report supportの予約名も明示的に保持し、purpose8との分離を証明した。
- `StaleChoiceFilter214.raw_obstruction_not_reachable`: 旧raw stale-choice反例は、不可視な保存宣言を含むため訂正208の初期状態から到達できない。この特定例を除外しただけで、一般のChoiceCompatibleを証明したとは言わない。

22の新規ソースモジュール、251定数（補助定義・private定理を含む）を監査。
モジュール一覧と全コマンド出力は [verification](../verification/dots-cycle-214.md)。
全域の依存関係と次の穴は [design](../design/2026-11-15-cycle214-overlap-plan.md)。

## 未解決点 / 次の順番

1. `Choice214.choice_iff_prepared` の現在Prepared持ち越し、またはAが使えない場合の一般証明書replay。
2. `Revisit214.BoundsFit`: 既存のshape一般 `HeadProjectionBounds187.projection_bounds` が必要とする、現在centered ProjectionModelsとallocation merge等式を、同じjournal modelで導く/共同構成する。Frame.preparedの「あるモデル」と「現在の任意journal model」は異なる量化子。
3. raw HeadModelsを含む同じ代入で、明示/default・merged出力・child schemaまで共同に満たすBを閉じる。今回のraw branch保存は存在証明ではない。213のrawHeadを落とせない回帰はそのまま有効。

課題のEvidenceNodeへの閉じた反例は見つかっていない。意味論を新たに決める必要も確認されなかったため質問ノートは追加していない。

## 検証 / 制限

- 明示的な22モジュールへの `lake build --wfail`: exit0。1283は依存キャッシュを含むジョブ番号で、全umbrella buildを実行したのではない。
- `lake env lean -j1 --trust=0 -DwarningAsError=true Audit/Cycle214Complete.lean`: exit0、251 constants /22 modules。許可公理はpropext/Classical.choice/Quot.soundのみ。
- `tools/verify-lean.sh . origin/integration/m1-final --no-build`: exit0、diff checks only、2 REVIEW。追加run_cmdは公理を列挙して不許可依存があれば失敗する監査器として読んだ。証明の穴を埋めるメタプログラムではない。
- 全体build/全体検証/実機Yulang2は未実行。監督役による統合検証は別。言語仕様やruntimeを変更していない。
- 初期補題のimport/名前解決、単体leanへの不適切な`--wfail`指定を修正後、厳密な全対象再検証を行った。途中のdiff gateはexit1。最終integration再取得直後のancestor gateもexit2となったため、統合履歴をmergeし直した。最終gateはexit0。途中失敗を最終PASSと混同しない。
- 使用量の枠は不明。

## 公開

checkpoint `917e9aec2f879fa4107475779564f51611657be0` はwork/dots-mainへ公開し、取得後のソース差分は0（heartbeatだけ異なる）と確認した。
ソースローカルcommit `3d38e5d4b`、最新integration取り込みcommit `41f92a60e`。最終公開はこれらの追加分を最新work/dots-main treeへ重ね、expected headを指定して非force更新する。
既存のAudit.lean/README.md/仕様/planは変更なし。Yulang.leanとdesign indexは追記のみ。
新規22source+2audit+design+handoff+verification、追記umbrella/index、heartbeatを合わせ30pathsが本回の対象。
最終公開のcommitとreadback結果・終了時刻はcompleted heartbeatおよび会話報告に記録する。
