# Yulang2 再現監査 cycle 2（A-1）

## 状態と基点

- 状態: completed（この監査サイクルの終了。Yulang全体やLean統合のPASSを意味しない）。A-1はACTIVE、最大12サイクルのうち2回目。
- 開始: 2026-11-08T12:30:51Z。監査終了: 2026-11-08T13:21:21Z。経過: 50分30秒（監査作業。公開完了の時刻はcompleted心拍）。
- 新spec/Lean読取基点: `integration/m1-final@3fdd6c3acac223b0920730979b3fd01b94366509`。
- 旧実機: `main@d4c8bc8fc8a49173180932cd25921a2c41057354`、前回のrelease binaryを再利用。
- 作業tree: `/workspace/scratch/1d0b4aaa3394/yulang-audit-cycle2`。旧実機treeは別の `yulang-audit-y2`。source/spec/Leanの変更なし。
- 書込公開は `work/dots-audit` のnotesのみ。証明用 `work/dots-main` とは別。Git pushは行わずGitHubアプリのblob/tree/commit/ref APIを使用。

## 復旧と心拍

前回cycle-1報告と公開成果を読み直した。開始時の心拍は無かったため「心拍なし」と記録し、cycle-1公開済み成果を独立treeに復元した。今回クラッシュ復旧対象を捏造せず、crash報告は作っていない。

開始、約10分、20分、30分、40分、50分と完了の心拍を `notes/heartbeat/dots-audit.md` へ公開した。各時刻・経過は同ファイルのcommit履歴に残る。長い標準prelude試験はセッション継続＋ログ保存で実行した。

中間公開:
- `cddc1f79e74d0add2ecada01735ce50278f1ee59`：X oracle等12ファイル、12:47 UTC、fetch照合。
- `75dced5cf6a7ebb6eb4133b987e6037c3193ef53`：注釈/SCC追補、12:51 UTC、fetch照合。
- `c746f7bb204718227748fa81b4e05d7e4962af63`：cast/hygieneと標準対照まで、13:08 UTC、fetch照合。
- `2581be61aa7e8671a3f404b42db5b2d0ed3a8492`：試験上限とpattern順序追補まで22成果ファイル、13:20 UTC、fetch照合。

最終公開はこの報告とcompleted心拍を含む。公開treeを取得して対象ファイルを照合した結果は最終心拍に記す。

## 調べた文書・主張

主な文書15件（関連節を読取。前回ノートとRust/Leanソースを別途参照）:
1. `notes/plan/dots-audit-standing-orders.md`
2. `notes/plan/dots-inbox-audit.md`
3. `notes/handoff/2026-11-08-m1-spec-examples-conformance.md`
4. `spec/03b-patterns.md`
5. `spec/04-types.md`
6. `spec/05-effects.md`
7. `spec/06-roles.md`
8. 旧 `web/docs/ja/reference/types.md`
9. 旧 `web/docs/ja/reference/type-theory.md`
10. 旧 `web/docs/ja/reference/effects.md`
11. 旧 `web/docs/ja/reference/casts.md`
12. 旧 `spec/2026-06-02-role-system.md`
13. 旧 `spec/2026-06-04-method-selection.md`
14. 旧 `spec/2026-05-31-effect-variable-subtractable.md`（June22改訂をMay31初版と区別）
15. 旧 `notes/design/handler-row-subtraction.md`（May13の旧設計メモ）

- `x-oracle.md`：X1〜X25の25行。一致4、違う5、実機で表せない16。各行に実入力、結果、spec上の受理/拒否理由、近似の限界を記載。これはLeanのPROVED分類ではない。
- `y2-claims-*-cycle-2.md`：追加の詳細46行。一致20、違う14、未確認12、確定した仕様欠落0。X oracleと主張の重複があるため、独立な71規則の発見とは数えない。
- 各「一致」は具体例/局所定理の範囲だけ。「違う」には意図した新仕様変更、表現代数の違い、source境界未接続を区別して含める。

## 実機・検証

記録済みCLI試験688呼出: exit0 497、非零175、外部timeout16。exit0にはエラー回復するdumpを含み、497個の正しいプログラムを意味しない。初期の誤構文・翻訳失敗も原ログに残した。補助のhelp、試験一覧、手動再確認、追加raw scheme dumpはこのJSON台帳の試験回数に含めない。

|群|台帳呼出数|exit0|非零|外部timeout|
|---|---:|---:|---:|---:|
|role/X1–12|108|81|23|4|
|type/X13–21|141|104|37|0|
|注釈/SCC|61|36|13|12|
|cast追補|120|84|36|0|
|hygiene追補|38|33|5|0|
|X22–25/標準対照等|202|150|52|0|
|pattern順序追補|18|9|9|0|

個別呼出時間の合計1940.959秒（32分20.959秒、並行分を含む。サイクル壁時計とは別）。標準preludeの第一群9呼出は1260.852秒、F1/default対照5呼出は156.006秒、cast/callback対照4呼出は159.415秒。標準preludeでも主要な差を再現した。

典型コマンド:
```sh
<y2>/target/release/yulang --std-root <y2>/lib --no-prelude check <case>.yu
<y2>/target/release/yulang --std-root <y2>/lib --no-prelude dump --poly <case>.yu
<y2>/target/release/yulang --std-root <y2>/lib --no-prelude run --print-roots <case>.yu
# --poly-raw / --mono / --runtime-ir、interpreter/evidence-vm対照も実施
# 標準prelude対照では --no-prelude を外した
```

Rust既存unitは個別8件PASS（区間3、advertised where1、filter2、directed weight2）。追加のordinary cast characterization 25件suiteは15件のok出力後、標準registry試験中に240.207秒で外部中断（suiteの終了コードなし）。当該1件を他の重い試験と並行させず単独で再試験したが、420.183秒で外部中断した。25件全体のPASSとはしていない。全出力と警告は原ログ。JSON台帳の全source/code/output/stdout/stderr文字列が保存済みMarkdown内にあることも機械的に照合した。新規Rust/Leanコードを書かず、既存期待値も変更していない。

Leanは定理のstatement/前提とsource橋渡し範囲の読取のみ。`lake build --wfail` / `verify-lean.sh` はこの監査で実行していない。Lean全体検証を済ませたとは報告しない。

## 核に響く差・未接続

- **B4/role**: 増大whereの宣言を旧Y2は受理。advertised whereとbody由来prerequisiteは別経路。bodyで実需要を作るとcheck/runが5秒上限に達する例があり、定数body成功から停止性を結論しない。未知receiverで同名roleが2つ見えると旧実機はfield fallback、新§6.4/Leanは曖昧。
- **B5/cast**: 有限boxの後変換を具体的に利用すると、旧Y2はcheck0でもnon-int primitive argumentになる例、固定producer経由でrunのcompile段階に拒否する例がある。直接scalar変換/明示back再構築は成功。宣言variance metadataを観測したこととは区別し、一般の型安全性反定理とはしない。
- **B6/F1**: 直接適用・pipe・推論高階は7。明示両rowの高階はpolyまで通るがmono/runtime-irでconflict。wildargは直接/etaで差がある。Common標準arrow関係とstrictApp合流だけで全F1接続を完成扱いしない。
- **B2**: X22の正確なoptional注釈は旧未対応。推論caseはmissing portをrunで拒否する一方default付きは80/443。default由来effectが型表示に現れず、外側の明示action境界経由ではunhandledになる例がある。直接catch対照は7。
- **B3/注釈・hygiene**: 外側一般化後のeffect具体化とSCC peer順序の正負対照は確認。effectfulな両方向実呼出SCCは上限で中断、inner完了時刻は未確認。無注釈callbackの許可外armを旧が受理する差を観測。旧word take/popとLean signed countは同じ演算と仮定できないが、source意味の非同値は未証明。
- **X21**: holder例の旧外側scheme量化と新field-local forall/rigidを分けた。元ref/sub例は完全再現していない。

## 通るべき候補

X1の子Display実使用、X12名前付き再帰、phantom retag、pure record default、到達不能arm、明示handler pipe、直接F1、一般化後のeffect具体化、直接入れ子shallow handlerの `(1,7)`、scalar castと明示box再構築を受理候補として原ログへ積んだ。拒否例だけでなく、これらを今後の完全性側の回帰試験候補にする。完全性定理を証明したという意味ではない。

## 質問・設計判断

既存の `notes/questions/2026-11-08-audit-F1-arrow-passthrough.md` に追加観測を追記した。遅延案を先頭に残し、carrier/cast/subtypeの方式は選んでいない。`spec-proposals.md` にも追記したが、確定した新規欠落条文は0。新specの明示的な決定を旧実機に合わせて戻す提案はしていない。

## 中断・制限・未確認

- サイクル本体の環境消失・クラッシュは観測なし。試験の外部timeoutは16件: 増大型role4件（5秒）、effectful SCC12件（40秒/5秒）。CLI自身の終了値でないrunner124/nullを区別して保存。別途Rust suiteを240秒、単独再試験を420秒の自主上限で中断。最後の実行中test名は repository_std_infer_and_poly_classification_are_unique。これはプラットフォーム時間切れでなく監査runnerの制限で、原因未特定。
- 構造record/variantのimpl head、source区間注釈、無名再帰μの生成、元X21、pipe catch省略構文等は旧実機の表現/観測に届かず。構文拒否を新specどおりの意味論的拒否と数えない。
- record patternの先行missはfallback20を確認したが、match側のabortive handler経路がruntime未対応で順序対照を完了できず。
- 型推論器/adapterの根本原因、全表面言語のsource-to-core対応、全SCCの停止、一般型安全性/完全性/主型性は未検証。
- 旧Y2の実行結果は素材。新specおよびユーザーの意味論決定を上書きしない。
- このジョブのプラットフォーム上限/使用量枠は確認していない。個別timeoutは自分で設定した試験上限。

## 公開範囲と次サイクル

今回の追加/変更成果は23ファイル（監査報告を含むauditノート22件＋既存質問1件）、加えて必須心拍1ファイル。計24パスを `work/dots-audit` のみへ公開。生成物/Lean/source/specを公開していない。最終公開treeとの比較結果はcompleted心拍に記す。

次回は最新integrationとstanding orders/inboxを再取得しSTOP/上限を確認。今回のcompleted心拍とこの報告から再開する。未確認のsource境界を優先し、すでに明示した新spec決定を聞き直さず、X oracleの表現不足と一般定理の不足を区別して進める。
