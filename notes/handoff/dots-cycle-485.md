# cycle 485: G04Entry を残し、G05 の前段に着手

道具: モデル不明、Lean 4.35.0; 委譲: モデル不明、1 回、task `/root/yulang302_resume`（追加委譲なし）
使用量: 不明。

## I-98: G04 の区切り

`Producer479.G04Entry : Prop` を新しい定義として置いた。証明も公理化もせず、既存入口・状態・spec は変更していない。命題は各元の `FullProblem` と宣言検査済み表に対して、旧平坦入口の組と signed 入力検査の組を分ける Bool インターフェースを求める。旧タグ同士は全入力で既存 `check_full_flat` と同値で、混ざったタグは false。signed 側は外から得た同じ `PriorPhase` に対し、独立な `TypedInput`、`ExactFor`、選んだ source / completed release と元の位置を保つ `IssueIsFaithful` を反映する。実際の全要求引数が同じ有限観測で安全と確認される local diagnostic の範囲において、逆向きに有限 wire を求める。端点の K2 の符号、旧 graph 上の実際の edge と安全な接頭部、同じ State の全 `FitsFull` で元の Walk を保つ。C480 の `G04Producer` 証明とは別の未証明の入口契約。命題に Bool の型を置くこと自体は実行可能な判定器の構成・設置ではない。G05 は可視一覧を単一に縮めてこの前提を使わなかった。

## I-98 / I-97 段階 2: 削除 0

`notes/design/dots-cycle-485-deletion-inventory.md` に、C481 で同値になった18の旧入口の完全パス、対応定理、実際に残る直接 import を記録した。各入口は既存 Audit と umbrella に参照され、ものによっては平坦側 leaf または互換・証明の依存そのもの。権威側 `tools/verify-lean.sh` が既存 Lean の削除を拒む状態で、C485 専用の許可パスと全体検証の依頼・成功を確認できなかった。削除前後の削減数はファイル 0・宣言 0・既存 import 移動 0。新しい成果物は追記だけで、ユーザーに再承認は求めない。置き換え可能性の証明と、実際の依存の切り離し・監督役の限定検証の両方が必要。

## G05: 全候補の tape、既存の実訪問、選択より先の K2

- `OriginalRoster485` / `ExactCandidateTape485`: 元の demand の可視順を全部使い、登録元 ordinal と literal 宣言を両方照合する。与えた局所判定が独立な意味に対して正確なら、その意味と全 wire の読取りを保存・反映する。欠落・余分な行、別の位置を同じ位置とする試み、局所読取り失敗は完全な tape にならない。
- `PreElectionTape485` / `ElectionAfterTape485`: 完全な tape に true が一つでもあれば、真であった元 ordinal をすべてその順に残し、後段の選択 callback は結果に影響しない。callback から値を返せるのは、順・長さとも完全で全候補の対象局所ビットが false の場合だけ。複数の true のうち表示する一つをここでは決めない。判定できなかった候補を false や不一致に読み替えない。
- `LegacyRosterPriority485` は旧 C413 の real one-nested fragment について、非 opening 候補は実際の binder match で payload を調べず、opening の旧 `PatternK2` が実際の元 ordinal にあることを保つ。旧 raw K2 と I-93 の型商判定を一般に同一視しない。
- `CandidateSignedPath485`: 実際の可視一覧の任意の位置で、GD 済みの元宣言・元 argument・元操作と AST 位置・同じ既存 raw の各点を保つ独立 `Trail` を読み、逆向きに同じ head/始点/端点/符号を持つ有限 wire を具体化する。肯定は実際に訪れた endpoint 自身の型商での循環。局所の経路検査自体が別途の source 権限、候補全体の一致、他の経路の安全を作るわけではない。
- `CandidateVisitFootprint485` / `PlannedPreElection485` / `PlannedReturnMeaning485`: 外から与えられた許可と exact plan の全選択を、元の head 引数、action と AST pose、同じ旧位置列まで検査する。各 proper visit を独立な path に反映し、独立 path 群からも同じキーと符号の有限データを具体化する。選ばれた各終点の符号は同じ型商の循環判定と同値。
- `CoveredCandidatePriority485` / `CoveredCandidateReification485`: 各元可視候補の実際の合法な局所循環の判断が正確に被覆されるという独立前提と許可の健全性の下、全 tape の各候補ビットはその判断と同値。真の候補があれば、その実際の登録 ordinal を残して選択より先になる。全て安全ならその範囲の実際の候補に循環なし。全候補の独立な有限経路資料が与えられれば一つの full tape を有限 wire にできる。

`Cycle485I74G05RosterActual` の独立監査では、一つの元の fitting snapshot にある、異なる二つの nested 候補について元 registry ordinal 1 と 3 の実訪問を確認した。同じ旧 raw の endpoint に達し、元要求根は I-93 型商で安全で、訪問終点自身の判定は true。旧 C413 の一つだけ nested の検査はこの複数ケースを扱わない。binder 候補を調べず、間にある role 外候補は元の registry 位置だけ残して可視 tape には入らない。元の登録順が変われば位置が実際に変わるため、古い wire を再利用しない。欠落、重複、未検査の行が加わるケースは完全 tape として通さない。

## できていないこと

G04 は `G04Entry` を残して未完、G05 も未完。残り 20 / 24。G05 の局所検査に与える候補の actual typed/matching visit の網羅性・許可の独立な生成を一般に示していない。空の plan を与えて得た局所的な all-safe を全候補の安全と見なさない。他の要求根との優先、全候補の match/mismatch/defer（G10）、既存の固定声明へ新しい入口を実装した結果はこの周の主張ではない。次は `IndependentCoverage485` を実際の元の候補ごとの局所判断から正確に供給できる部分を切り分ける。削除候補は Audit・leaf・既存互換の逆依存を解いた後でパス限定検証を行う。Yulang2 は再実行しておらず、今回の型商経路を旧 runtime の結果に読み替えない。

## 検証と公開

- Lean 4.35.0、対象だけを `lean --trust=0 -DwarningAsError=true` で厳格確認。新規 production import の同時読み込みも独立検証。production 12、独立 Audit 13、名前付き検査 44（許容標準集合のみ）、kernel 判定で具体例を確認。集約は対応する import 12 行の追記のみ。権威相対 Lean 26 パス、全 30 パス（設計2本・報告・HB を含む）。I-94 の追加行違反なし。既存 C484 の旧 production・Audit を変更していない。全体 `verify-lean.sh`・Lake build、Yulang2 実機は dot では実行していない。
- 実開始 `2026-11-28T08:35:18.000Z`。+10 `d5084da5a0a2bbcc7a6f73e34cce3995ddc25416`、+20 `6876788a81535424744e3081585cfc49e02c1cd0`、+30 `ef25dd1ff0b609f7f68e36107acfc25b3d8507e3` で Lean 凍結、+40 `2c1b7e2bf845d979af0bea627e4f568704ff96a2`。凍結 tree `9731ca088dbe50869458d94cd80f135be9771c16`、正確な権威祖先 `eaef0baeaafc45b3e35c983dfbcd7c1137c1b5e5` と I-98 inbox を確認。次回は最新の inbox と統合の先頭を最初に読む。
