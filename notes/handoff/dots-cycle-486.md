# cycle 486: G05 の有限候補 tape と I-99 の最初の削除

道具: モデル不明、Lean 4.35.0; 委譲: モデル不明、1 回、task `/root/yulang302_resume`（追加委譲なし）
使用量: 不明。

## I-99: 一件だけ削除した明細

対象の権威は `d12fff985c2aef3ef298b181251462f8f03c4e37`、Lean tree `9731ca088dbe50869458d94cd80f135be9771c16`。以下の明細以外の既存ファイルや行は消さない。

| 削除するパス | 削除前の blob | 置き換え先 | import の修正 |
|---|---|---|---|
| `lean/Audit/Cycle410I74RootEscape.lean` | `3b4f67388ad054b917321df3adaa99174a39bf62` | 既存の `lean/Audit/Cycle410I74ListEntry.lean`、blob `39253c2e7b9f5da3e93ef1b1cfcfd08fa65b0110`、5 行の同一の検査 | この Audit を import するファイルは 0。集約 import の編集なし |

削除側は import と `open` のほかに検査 5 件のみで、宣言や実行例を含まない。保持側の同じ名前は厳格ビルド前後で同じ完全修飾名 `Yulang.GeneralDeclarativeI65.I72.List410` 下の同じ宣言に解決された: `escape_rows_checked410`、`EscapeRows.sameAlias`、`EscapeRows.escapes`、`EscapeRows.follows`、`checked_escape_refutes_exact_raw_root_K2410`。`sameAlias` に公理依存なし。他の 4 件は propext / Quot.sound のみ。保持する監査全体も標準集合のみ。実装 `lean/Yulang/GeneralDeclarativeI65I74RootEscape410.lean` と既存証明は変更しない。C481 の 18 旧入口と I-65 固定声明も変更しない。

権威 tree の Lean ソース 10,732 パスを blob hash 照合して逆参照を検索、加えて tools の 53 ソース・設定 blob を確認。いずれも `Audit.Cycle410I74RootEscape` への参照なし。既存 umbrella も同参照なし。該当 Audit の直接輸入先が 0 なので、影響確認はその旧監査と代替監査に絞った。代替監査と旧監査の推移的なソース閉包（3,990 パス）の hash は、依存を準備した既存の Lean 4.35.0 の対象と一致。Audit だけを対象にする隔離した Lake 設定で、`--trust=0 -DwarningAsError=true` を使用した。削除前 `lake --no-cache build +Audit.Cycle410I74RootEscape +Audit.Cycle410I74ListEntry` は 3 jobs・終了 0。削除後は旧 Audit のソース・olean の両方がない別ディレクトリで、同じ依存を参照して `lake --no-cache build +Audit.Cycle410I74ListEntry` が 2 jobs・終了 0。全体ビルドではない。標準出力 sha256 は前 `8f6706fc27fd9f41f27873cc5463326533544e6f307289583961a33ee146fc04`、後 `5822cdab994177376fb927172982e289895eef4618a96cc5d400446a5022137e`。

削除だけを比較すると、影響のある監査ファイルは 2→1、Lean ソース全体では 10,732→10,731。削除される宣言は 0、同監査 2 ファイル中の実装宣言数は 0→0。出力される監査件数は重複込み 37→32、実際に検査される異なる宣言は 32→32。G05 追記のファイル・宣言はこの差分に含まない。監督役が統合時の `VERIFY_REVIEWED_REMOVALS` で開けるパスは表の一件だけ。

## G05: 旧 State の実際の全候補と全引数を使う生成・再検査

- `OriginalNodeBudget486` と `ExactSuccessorHop486`: 元 Pattern の実行可能な node budget が、空でない元 AST 位置への実際の descent で減る。候補 action・pose と旧 graph の即時 successor を有限に並べる。既存 `readHop` を通るものと独立な既存 Hop が一致する。一つの exact key が提案で重複することはあるが、別の元 pose は混同しない。
- `BoundedCandidateGeometry486` / `AuthorizedCandidatePlan486`: 同じ有限旧 graph の元位置について、完全な palette のもとで旧 signed Trail を有限に列挙し、保存と反映を証明した。途中で K2 の符号が true なら、その経路の下は読まない。別に与えられた許可が独立の出所判断に対して正確なら、列挙された proper visit のキーだけがその出所に合う。置換・循環・型等価から author permission を推測しない。
- `GeneratedPlanWitness486` / `CandidateWiresFromGeometry486` / `ExactComputedCandidateReplay486` / `CompiledCandidateFootprint486`: 同じ元 head と原位置で、旧 checked palette からキーと path packet を実際に組む。ペアを独立な `ExactCandidateFootprint485` に反映し、今作った wire そのものを既存 reader に戻して、元操作・全旧位置・終点の符号が一致する。等しい曲路から別の packet を選び直さない。`FiniteCandidatePalette486` は guarded positions を覆う有限ベクトルが古典的に存在するだけの別定理。
- `AllDemandedRootsBeforeElection486`、`OriginalArgumentStart486`、`AllOriginalArgumentFootprints486`、`ComputedWholeRoster486`: 実際の demand の root を順にすべて確認してから、可視一覧を元順のまま全部使う。各可視候補で実際の登録 ordinal と元 head の arity、GD 済みの各引数位置、同じ旧 capture 下端の raw 状態を読む。全引数の footprint を順にまとめる。許可を固定すれば、key の membership はある実引数の独立 proper visit と同値。C485 の既存 tape checker に戻して候補順と優先結果を検査する。空 arity は proper visit 無しのみを表し、候補が一致したとは言わない。
- `ReachablePalettePreflight486`、`RosterPalettePreflight486`、`ReadyAuthorizedRoster486`: palette に到達可能な旧位置の checked sign が無ければ局所入口は none。ここで必要なのは候補の実引数から辿れる構造的な範囲で、独立な未訪関係を全て否定するものではない。preflight 成功時、同じ元 head・旧 graph の全独立 Trail を取りこぼさない。別に許可が exact なら、それらから許可された訪問全体と同値。既存 geometry が開けるが許可されない枝の証拠を先に要求し得る、保守的な入口。none を言語の拒否や不一致には読み替えない。
- `ReadComputedRosterCompleteness486` / `ReadyOriginalRosterCompleteness486`: 元全引数の権威つき checked root・実際の全可視候補の同じ arity と独立な各 `OriginalArgumentStart486`、別に供給した許可の健全性の下、順序を保つ全候補 tape の生成と再検査が成功する。完全な旧 palette からの存在を証明した範囲であって、一般の source feasibility や candidate 照合をこれで作ったわけではない。
- `ComputedOldPalette486` / `AutomaticPaletteEntry486`: 既存 raw table と与えられた関係で旧 cone と最小型商を**実行可能なデータ**として構成し、従来の `readCheck` に照合する。既存の guarded な位置と読める旧符号が正確に対応する。自動入口には palette・key list・candidate path wire の手入力が不要。実際の `FullProblem`、GD、raw 位置・対応関係、元要求根の証明書と候補局所 permission は引き続き別途与える。これは全体 compiler/solver の実装ではない。

独立 `Cycle486I74G05TwoOriginalArgumentsActual` で、同じ fitting State の**実際の二つの元引数**が同じ raw logical 0 にある場合を kernel 検査した。登録元候補 1 は arg 0、候補 3 は arg 1 を本当に訪れ、間の binder-only 候補を開かない。元引数の区別と両元候補を保って `.recursive [1,3]`、旧 root false と元 field 終点 true。元 root packet の欠落・余分・別 terminal は decline。到達 terminal の palette を消すと、以前の plan に相対的な入口は `.allSafe [1,2,3]` を返すが、新しい preflight は none。これは安全の言語的証拠でない。自動 palette がある側は同じ再帰結果、偽の旧対応 `[(0,1)]` は checkpoint を作れない。

## できていないことと次の課題

G04 は `G04Entry` を証明せず未完。G05 も未完なので残り 20 / 24。全実候補について実際の permitted matching/typing visit と独立な prior の照合を一般に被覆すること、他の要求の分類・選択との固定入口への接続が残る。G10 の一般 match/mismatch/defer や最終選択を新たに決めていない。次は `accepted_ready_roster_preserves_and_reflects_every_prior_authorized_proper_visit_of_each_head486` の permission exactness を実際の局所型付けから供給する範囲を明示し、検証済みの authority で各符号付き候補を接続すること。発生する全候補の本当の一致を幾何・K2 の符号だけから含意しない。

旧 Yulang2 実機は再実行していない。既存 `work/dots-audit` `55574b6052ef1534fd0fc36d6d3617ebede59a0e` / `notes/audit/x-oracle.md` `0d75bdb801151589d5aeef453fd6b7dfa414baec` を照合: X8/X9 は目的の再帰 μ を実際には出しておらず、X10/X11 も旧 syntax・型解決上の限界で今回の選択前 K2 を確認した例ではない。

## 検証と公開

- Lean 4.35.0、対象だけを `lean --trust=0 -DwarningAsError=true` で厳格確認。新規 production import の同時読み込みも独立検証。production 20、独立 Audit 21、名前付き検査 39（許容標準集合のみ）、kernel 判定で具体例を確認。集約は対応する import 20 行の追記のみ。権威相対 Lean 43 パス（追加ソース 41、集約、上記重複 Audit の削除 1）、全 47 パス（設計2本・報告・HB を含む）。I-94 の追加行違反なし。上記の一件以外、既存 C485 の旧 production・Audit を変更していない。全体 `verify-lean.sh`・Lake build、Yulang2 実機は dot では実行していない。
- 実開始 `2026-11-28T09:33:50.000Z`。+10 `32b95b54cd34e9c2a4caedd1c69fdcc89e53fa74`、+20 `3ad2ca6d8a6f12a31a810501f76fbdd5e4d9d94c`、+30 `ed4253de4da9202cb8a482164d8a3a598eb24937` で Lean 凍結、+40 `a786f277660ee4469784e3e6520e2ffe22e8e4eb`。凍結 tree `bc9b82481f7cafb328824bcc7f69dc963c425141`、正確な権威祖先 `d12fff985c2aef3ef298b181251462f8f03c4e37` と I-99 inbox を確認。次回は最新の inbox と統合の先頭を最初に読む。
