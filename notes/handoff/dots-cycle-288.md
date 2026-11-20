# dots-main cycle 288: source 由来の葉、ledger、局所読取りの分離

## 結果と範囲

cycle 287 の実 mixed-kernel 例を使った。親 `F(a)` は実際の据付で
where 子を一つ生成し、座標 2 に関連出力 `F(F(a))` を課す。座標 0 は
`R(row0)`、座標 1 は `F(R(row0))`。型全体を受け取る子と、行を
分解するため保留になる子を比較した。既存の実 Step、spec、Rust、
構文、言語の受理／拒否は変えていない。

1. **source 由来の証拠と旧台帳は別（健全性・補助）**。
   `InertLeaf288.source_evidence/existing_selection` は任意の state/registry
   について、正確な現行 Frame・V8 安全条件・唯一の選択・子も出力要求も
   ないこと・非空の元 source slice・その全割当てでの packet を前提に、
   既存の葉辞書を構成する。実子にこの条件が成立するのは全型を受け取る
   枝だけで、据付で生成される前はどちらにも Frame がない
   (`RowLeafWindow288.actual_activation_window`)。
   `RowLeafSlice288.extension_iff/slice_exact` は既存の trusted input を
   残したうえで出力 fact を一つ足す補助証明が正の枝に限り成り立つこと、
   その slice の割当ての条件は元の source 条件と出力等式に必要十分
   であることを示す。全 Models の一致だけではこの信頼を得られない。

2. **静的な台帳追記と合法な実遷移を分けた（補助）**。
   `RowLedger288.models_eq/old_refresh`：正の実端点の台帳へ独立証明の
   ある葉 plan を追加した**仮の状態**は、core・effects・全 Models を変えず
   旧 `Discharged`、`Trusted.output`、旧 Refresh 証明を持つ。
   `RowLedgerStep288.no_raw_path_to_supplement`：この追記自体には
   元の実 Step の経路がない。台帳追記を仮定した後だけ、旧 Step の
   具体的な refresh が本当に存在する。元の生端点は従来どおり停止。

3. **無スコープ追記は誤り（閉じた反例）**。
   `ForeignLeaf288.semantic_shortcut_counterexample/no_raw_path`：
   行を分解する枝の同一子 ID に、別 registry の正の葉 plan を静的に
   移植しても全 Models は一致する。旧台帳の構文的 `Discharged` と
   `Trusted.output` まで作れるが、本来の checked registry の Frame も
   辞書も成立しない。これらは到達不能な台帳を用いた反例で、旧実行の
   健全性への反例ではない。モデル充足や ID 一致だけで追記する案は
   ここで止めた。さらに `RowDeferredDecisionGuard288.not_a_settlement_criterion`
   により、**元の実負例も**既存 DecisionGuard を満たす。既知の根を
   持ち、deferred 検査の nested read が空だからだが、保留で、辞書はない。
   DecisionGuard を V8 の実検査完了の代わりにする案も止めた。

4. **仮の正の台帳から出る、すべての旧 refresh を特定（健全性・完全性・補助）**。
   `RowLedgerFirst288.only_output_refresh`：任意の次状態について、旧 Step
   である必要十分条件は、証明つき refresh で型 ID 2 を新たに Known と
   すること。`RowRefreshShape288.actually_nominal`：任意の許可された
   refinement の出力 mark は、型 ID 1 を両端とする一点の `F(1)`、
   スロット名の埋め替えまで一意。私的集約名は現に生の一覧にあるが、
   その型を Top にできるモデルがあるので新たに Known にはできない
   (`RowLedgerNames288.listed_not_recognizable`)。
   `RowRefreshHalt288.maximal_iff`：仮の台帳からの極大な生経路は必ず
   この一手で止まる。これは元のソースで追記が起きる意味でも、一般の
   停止性でもない。三相 observer の両向き対応
   (`RowPhaseSimulation288.exact_observer`) は定義した正の Family に限る。
   全相で出力だけの二 fact 射影と全 Models は同一。foreign 状態は
   同じ ready 表示でも Family ではない。

5. **一手後の辞書と局所検査（健全性・完全性）**。
   任意の上記 refresh、任意の完全割当てと payload について、
   `RowRefreshEvidence288.exact_payload` は、全 Models と根 Evidence の
   同時成立が元の source/出力条件と payload `.node 0 [.node 1 []]` に
   必要十分と示す。`RowRefreshDiagnostics288.exact_tree` は V8 の実診断木
   も `.selected 0 [.selected 1 []]` に限ると示す。生の割当てに必要な
   支持は型 0,1,2 と行 0、正準補完した割当てでは型 0,1 と行 0 だけ
   (`RowRefreshProjection288.exact_support`)。補完は型 2 を計算するだけで
   全行と他の型を保ち、既存 Step ではない。
   型 2 を Top にする元 source の割当ては mark 後の **全 snapshot** を
   満たさない。したがってその全 snapshot に対する新しい source-only
   葉証拠は存在しない。それでも同じ割当てで子の局所入出力・class 条件、
   実根 head は成立し、nested read は空。これが
   `RowLeafReceipt288.strong_and_weak_separate` の局所 receipt との違い。
   実根 head の最小支持は型 0 と行 0、親 mark の最小支持は型 1 と
   型 2（独立な行・私的な型の読取りなし）。前者は元 source が既に
   課しているので、行 pattern が新しい独立な行条件を足したわけではない。

## 検証、公開、制限

- Lean 4.35.0。新規 33 モジュールを警告をエラーにして個別確認、
  10 個の独立監査で 144 宣言を確認。出力に現れた公理は
  `propext`、`Classical.choice`、`Quot.sound` のみ。旧回帰 24 個は
  再実行で全て exit 0。199/202 の初回だけキャッシュ不足で、
  不足した 7 依存のみ個別に作って再試行した。さらに新規モジュールを
  一切含まない別キャッシュから 33 モジュールと 10 監査を再検証し全て
  exit 0。生成結果のハッシュも 33 個すべて一致。全体 build や CI は未実施。
- 静的検査は前周と統合基点の両方から exit 0。統合基点比の REVIEW 2 件は
  既存 cycle 287 にある二行の評価。新規の評価コマンドは追加していない。
  barrel は末尾への追記のみ、各新規 import を同じ公開に含めた。
  追加一覧は [lean-manifest.txt](../verification/cycle288/lean-manifest.txt)。
  [検証の一覧](../verification/cycle288/coverage.md)、
  [コマンド](../verification/cycle288/commands.md)、
  [focused](../verification/cycle288/focused.txt)、
  [static](../verification/cycle288/static.txt)、
  [既存回帰](../verification/cycle288/legacy.txt)、
  [別キャッシュ](../verification/cycle288/isolated.txt)。
- 開始時に統合 `b9bb2a19d271447d6f03f8b99e8ec97c9ee50363` の
  standing orders、続いて inbox (ACTIVE、I-53) を読み、前周 287 の
  完了した心拍と報告、ローカルとの差分、唯一の writer を確認した。
  開始時刻: 2026-11-20 03:35:05Z（03:30 枠、実際の開始は約 5 分後）。
  GitHub アプリで `work/dots-main` の期待する親 SHA を検査し、非 force
  で公開。途中の検証済み pin:
  `c9fff0f2b5101bd375fedcd6f2791a7144edf30c`、
  `487cd5fe60e8af7d45e712024e2c83d83f258188`、
  `7aa99a5b4cf15c1830d0cf15c43497794fc503dc`、
  `b76da9249b07e1819937998dcc9a3e8cf6c6e88e`、
  `a41b17188606d45ea0904b3046f05a77998973bb`。
  公開先はこのブランチのみ。使用量上限の具体値は不明。
- Yulang2 の audit `55574b6052ef1534fd0fc36d6d3617ebede59a0e` の X1、
  C3-ROLE-01/02（associated producer と実 where、成功／欠けた子の診断）
  の根拠と raw log を再確認。今回の行・receipt・mixed ledger を
  Yulang2 で測定したとは主張しない。

## 残り

B4/T1c の外側 `Initial/GroundRoots`、一般 EvidenceNode・主型性、
I-49/I-50 の一般測度、alias・出力効果を持つ子の receipt、行を直接分解
する typed observer と閉じた行付き source 文法は未証明。設計の候補を
[次の設計ノート](../design/2026-11-20-cycle288-dependency-local-receipt-followup.md)
へ置いた。意味論の決定を必要とする質問ノートは追加しなかった。

- 最終報告書の時刻: 2026-11-20T04:25:07Z、経過 50.03 分。前周からの変更 62 ファイル
  （この報告と完了心拍を含む）。完了書き込み後に再読出しで照合する。
