# Yulang2 再現監査 cycle 1（A-1）

## 基点・時刻

- 開始: 2026-11-08T11:25:57Z。
- 終了: 2026-11-08T12:16:15+00:00。総所要時間: 50分18秒。
- integration/m1-final: `3b34c9e94b255ecde581e92cac787604e8313cad`。開始時にclone/fetchしstanding orders/inboxを読み、ACTIVE（上限12）を確認。
- Yulang2 main: `d4c8bc8fc8a49173180932cd25921a2c41057354`。別worktreeで実行、既存ソース変更なし。
- work/dots-auditは開始時baseから作成した。公開済みcycleはなかった。
- 書いた成果物はnotes/audit/および質問1本のみ。spec/、lean/、notes/plan/、他のremote branchには書込なし。

## 今回の成果

旧文書20本（全主張を網羅したという意味ではない）から48主張を3表へ整理。分類は22一致、19違う、0確定欠落、7未確認。「一致」は文書とLeanの対応範囲を含み、全surface実行を保証しない。「違う」は意図した新仕様、旧文書が古い場合、Leanのモデル境界を区別する。

旧文書: effects / types / type-theory / functions / application / casts / control-flow / patterns / structs / operators / idioms / syntax-style / errors の13 reference文書、および旧spec effect-variable-subtractable / role-system / invariant-type-sandwich / method-selection / syntax-design / act-copy、handler-row-subtraction設計メモの7本。

- **F1・X25は部分的、PROVEDではない。** Y2のpure-argument passthroughは実装と既存unit、ordinary/pipe/inferred-higher例で確認。新Commonのcommon_arrow_iffには同じ特例がない。ただしstrictAppの伝播・推論接続はある。矢印subtypeとstrict applicationを混同しない。詳細と紙上反例はf1-effect-passthrough.md。
- 明示高階引数型のF1例はcheck成功、runで`conflicting type candidates: [ping] vs []`。標準prelude付きでも再現した。旧Y2の動作を完全成功としない。
- nominal source→targetのcast二候補例はcheck/runとも成功し先頭の値を返す。旧文書の曖昧拒否と違う。generalizeのinstantiate-all、compactの非空検査、specializationのiter().findを確認。builtin int→boolの0/1/2候補はmissing/成功/ambiguousで、経路差が実在する。nominal2候補は宣言順を逆転すると結果も反転。nominal0候補はcheck0/run1だった。
- branch合流例は推論表示がunionでもrun結果は両枝int。後段変換の完全な追跡は残した。
- OR同名binding左枝でunbound local、型注釈pattern無視、refutable my受理、as結合力、pipe先頭引数、else無しifのunitを再現。いずれも旧挙動を新specに戻す提案ではない。
- error record payloadは旧文書のunsupportedに反してconstructor成功。新specとは一致する。さらにnarrower errorをbig::wrapへ直接渡す例はunhandledで失敗し、big::upを挟んだ例はresult::err(big::nested(small::bad))で成功。旧文書の自動narrower捕捉を無条件の実機保証にはできない。enumのfrom自動cast例は308.048秒後にno implicit cast from small to bigで失敗。Throw/Display等の全生成は未検証。
- handler hygieneの文書そのままのsub/return例は0。shallow、再handle、multishot、record default/spread等も記録。effectful defaultの欠落field例はcheck成功/run unhandledであり、成功としない。

## 検証と所要時間

記録付きbatchは236 CLI呼出・76入力例。exit0が190、exit1が44、SIGKILL(-9)が2、runner timeout(124)が0。exit1は期待した拒否・環境依存・runtime失敗を含み、236全てPASSという意味ではない。batchのコマンド経過時間の合計は2020.527秒（並行実行を含みwall timeではない）。初期の手動探索実行は別記で厳密なCLI全総数には合算していない。再現可能な各入力、command、開始時刻、経過秒、終了値、出力全文はruntime-cycle-1.md。大きい初回prelude dumpはlogs/f1-direct-standard-dump.txt。既存Rust unitの全文はunit-tests-cycle-1.md。

- 初期cargo不在: exit127。公式Rust toolchainを隔離workspaceへ導入。
- 指定offline build: 依存chasa不在でexit101。通常release buildはexit0、91秒、既存warningあり。
- 初回標準prelude dump: exit0、179秒。初期home cacheがread-onlyだったためwarning。公式YULANG_CACHE_DIRをworkspaceへ指定し、権限を変更せず継続。
- 標準prelude付きdirect run: exit0、308秒。
- 狭い既存unitコマンド11回成功、29 test completions（1再実行を含みunique28）。F1の初回debug build込み86秒、他の小さいfilterは各1秒未満。Leanビルドは実行せず、定義・定理・制限の読取のみ。
- broad ordinary_cast_characterizationは複数PASS後にtest process SIGKILL。2つのrepository_std testが60秒超を表示。原因は出力されていない。shellの末尾tailは0だったが、cargoの数値exitを保存し損ねた。全PASSと扱わない。
- 標準check2件も子プロセスreturncode -9（SIGKILL）。runは成功。順次check再試験は両方exit0（149.007秒、150.092秒）。初回SIGKILLの原因は確定していない。
- runner生成の誤りでsource文字列の各文字をfilenameとした642呼出を誤実行、全てexit1。言語の試験結果には数えず、直ちに修正して所定7モジュールを再実行。誤実行metadata/rawはローカルに保存。

## B4/B5/B6に響く点

1. B6/F1: 既存Common arrow比較とspec5.5cの関数型変換の位置付け。明示coercionかrelation変更かは監査で決めない。
2. B5: strict applicationと歴史的appの入口、callback注釈、patternのsource bridgeを分ける。OR名前検査/並び替えの核はあるが、型注釈pattern、my静的refutability、asのparser結合力を覆った証明は今回未同定。
3. B6 cast: 旧docの曖昧拒否は実機全経路のoracleにできない。新仕様の曖昧拒否に合わせるべき部分と、旧動作の素材としての観測を区別。
4. B4: role宣言varianceの導出とwhere residualへの反転・共起簡約は旧unitで確認。新nominal varianceの定理だけをrole残余schemeの接続完了として扱わない。一般飽和driverの監査は未実施。
5. effect solver: 旧take/popの非可換正規形は既存unit6件PASS。新Effectsはoccurrence visibilityモデルだと明記している。旧wordと新counter/visibilityの同値を仮定しない。

## 公開の失敗（未解決）

GitHubアプリでwork/dots-auditの作成は成功。その後の最初のfile create:

- destination: momota1029/yulang、branch work/dots-audit
- path: notes/audit/y2-claims-effects-types.md
- operation: github_create_file

は次のエラーで実行されなかった。

```text
Automatic approval review failed: authorization changed before approval could be applied
The action was not executed because automatic approval review could not be completed. This is a review failure, not a determination that the action is unsafe. Do not bypass the approval check; resolve the error or ask the user for guidance.
```

承認を迂回せず停止し、親へ報告してローカル作業を継続した。20分ごとの中間公開と最終公開は未達。2026-11-08T12:11:40Zのread-only fetchでwork/dots-auditがbase3b34c9e94のまま、notes/audit/が空と確認。**公開ファイル0件**。Git pushへの代替も実施していない。

ローカルでは専用cloneのwork/dots-auditに小分けcommitし、公開予定11ファイルと原出力を保存した。入力例・個別ログはruntime本文へ集約してあり、notes/audit/examples等の未追跡一時ファイルは公開予定に含めない。次サイクルがrepoだけから復元するには、公開承認の問題が解決される必要がある。未公開分をremoteにあると誤認しない。

## 質問・提案・残件

- notes/questions/2026-11-08-audit-F1-arrow-passthrough.mdを1本ローカル作成。遅延案を先頭に置き、F1の確定した意味論を変更していない。未公開。
- spec-proposals.md: 確定追記案なし。既知の仕様変更と旧文書の陳腐化を「欠落」と数えていない。
- 次（優先順）: 公開問題解決後に今回の11成果物を照合付きで公開。F1の高階矢印変換とstrictAppの接続をB6担当へ引継ぎ。監査の続きは、role residual variance/knownness・共起簡約をsource最小例へ落とす。次にnominal/builtin castの0/1/2候補経路差、parameterized effect residual、source annotation/coverage、直接narrower-wrapやeffectful defaultの生成境界を追う。
- 次回に同じ試験を無闇に重複しないため、Y2 binaryはyulang-audit-y2/target/release/yulang、cacheはaudit-y2-cache、toolchainはaudit-cargo/audit-rustupに残した。同一workspaceが残れば再利用できるが、残ることの保証はしない。
- 新specの処理系を走らせたわけではない。Lean theorem bodyの読取はしたが、Lean再ビルドや新しい信頼性監査はしていない。任意プログラムについてY2や新モデルの正しさを証明していない。内部規則の一部はsource最小例まで落としておらず、unit/文書だけの行と区別した。

## 最終追加実行

`enum-from-cast` の標準prelude付きrunは終了値1、308.048秒。出力はruntime-cycle-1.md。
