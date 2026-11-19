# dots-main cycle 280 — 裸変数の固定ポートと、再現できる辞書グラフ

- 開始 2026-11-19 19:30:00 UTC。終了 2026-11-19T20:20:00Z（50.00 分）。開始時の integration/m1-final は 6ffaba4a。standing orders と inbox を開始時および途中に読み直した。ACTIVE、I-51〜53、凍結ファイルを保持。279 の heartbeat と報告は 058a8659 で完了済みだった。復旧対象なし。書き込み先は private work/dots-main のみ。
- 実際の名目型 `Display (list 'a)` と `where 'a: Display` を維持し、構文や受理規則は変えていない。

## 1. 裸変数を含む固定グラフと、型・出力の読み戻し

- **補助 / 構築と健全性:** 任意の実 emitted child の ID・role・named output target・実 center をそのまま保ち、引数の上下を親 ID・宣言・節・位置で固定した purpose 3/4 のポートに置く。任意のモデルで、裸変数にだけ出力する型不等式は、固定端点が旧端点と上下両方向の部分型関係にあることと同値。よって任意の実型への interval fit、center origin と SiteHolds は同値。row を触らない同時コピーで、書く先が意味の支持・参照と衝突しなければ、全モデルから公開値を変えずに拡張できる。private な旧表・新表を（保護条件下で）置き換えても公開射影は同じだが、二表を恒久的に両方足すと、異なる旧・新端点を同一視して公開モデルを実際に落とし得る。
- **健全性／完全性（到達グラフ）:** 任意の checked source とすべての実到達列に対して、通常の裸変数も含む canonical full-edge basis が有限。同じ ID は一つの固定 occurrence を決めるが raw descriptor の等号は主張しない。実 Generated があることは、重複を除いた ID グラフにその ID が到達することと同値。実辺の親 ID、checked 宣言・節を使う実行版 catalog は、各実辺の両端を漏らさず、固定候補以外を返さない。
- **読み戻しの境界:** 位置ごとの有限表で、固定 child から元の raw occurrence、center を含む Site、同じ順序の実 where 子を正確に復元。Display の子は raw point (1,1) で既知だが、固定ポートの名前は構造グラフに未登録なので、普通の atom を足すだけでは旧 Known が pending のまま。元の構造検査に渡す前に表で復号すると、実の子 .node 3 [] と親 .node 1 [.node 3 []] を失わない。全 packet の表も、宣言の一意な節 ID と割り当てキーの単射性で衝突せず、各子の個別表と同じ読み戻しになる。実行テストは上下とも 1 に復号し、未割当は none、catalog と重複圧縮の両方が true。

## 2. 保存した effect snapshot まで圧縮する全経路対応

- **健全性／完全性（実 operational path）:** 任意の mixed journal の current raw 辺と、保存した各 versioned effect snapshot の raw 辺を、full occurrence の membership を保ってそれぞれ置き換えられる（固定 ID グラフへの変換とは別）。全割当モデル、履歴の ClassEffects、出力の生きた要求、legacy/版付きの信頼された cache slice を保存。output fact だけを新旧 effect の対応で運び、class readback の元の snapshot も確認する。legacy の archived effects 自体は書き換えない。
- **全 Step と停止性の保存:** 任意の対応した状態上で、実 install・merge・enqueue・equate・両入口の refresh・reobserve の一歩を反対側でも行え、次も同じ関係に入る。よって任意の有限経路を双方向に運べる。毎回 current と全版付き snapshot を重複なしにする圧縮機械では、Stable、Acc、V8 の Local 判定（K2、共有・出力衝突を含む）と構造的な EvidenceAt を保存。正規化は冪等。実 Display の非葉は圧縮後も一歩で終わり、同じ payload を持つ。保存 snapshot に重複を入れた表現だけの試験（実到達だとは主張しない）でも一つに縮む。
- **旧反例は消えない:** raw 辺を消しても版付き捕捉による新しい全割当の切り捨ては残る。旧239と I-45 の旧240は圧縮機械でも Acc を持たないと閉じた定理で確認。従って一般停止性を「履歴の重複を取ったから」とは言えない。

## 3. raw 辺リストは保存しなくても、到達状態で正確に復元できる

- **健全性／完全性（到達状態の表現）:** 初期 root と、実 install の plan を古い順に並べた ticket 台帳から、現在の raw sites・centered sites・raw edges を順序・重複込みで再現できる。保存済み versioned effect 各々の snapshot は、その effect より古い prefix の辺を正確に持つ。
- **実装と復元則:** current と全 versioned snapshot の raw 辺をいったん空にした保存表現から、任意の actual checked source 到達状態を構造体ごと復元できる。二つの到達状態が同じ保存表現になることと、元の状態が等しいことの同値。復元して一歩動かしまた空にする遷移は、前後の実状態に対して正確な iff、有限経路・Stable・Acc も同値。Display の実到達例で辺と payload を復元し、旧239/240 の全段階でも round trip。これは graph を落とす保存則であり、残る plan/effect の個数を有限にする主張ではない。

## 主な公開宣言

| Lean モジュールと宣言 | 前提と結論 |
| --- | --- |
| `GeneralRebasePortMeaning280.clause_atoms`, `observed_holds` | 任意の plan、妥当な節、割当に対し、全 alias atom と端点の同値が iff。その同値の下で両方の observed site のモデルが iff。 |
| `GeneralRebasePortProjection280.projected_replace`, `append_loses_public` | 元の述語の New/Old 両表の target が支持・公開値・参照元から分離し、表が一意なら公開射影は iff。逆に二表を追加し、異なる公開値を同じ target にするなら、その公開割当は失われる。 |
| `GeneralRebasePortBatch280.batch_unique`, `decode_batch`, `all_alias_atoms` | 任意の checked packet で同一 key への書き込みは一意。任意の登録節で復号は元の occurrence。copy 側は source/target の分離の仮定の下ですべての節の alias atoms を充足。 |
| `GeneralRebaseFixedGraph280.finite_canonical_edges`, `GeneralRebaseFixedGraphExec280.edges_exact` | 任意の checked initial source に対し、全到達の固定辺と同値な有限リストが存在。任意の到達先で、実行版 code の membership と実辺の正確な固定化が iff。 |
| `GeneralRebaseProjectedReach280.source_reach_exact`, `GeneralRebasePortGate280.Display.raw_gate_fails` | 任意の source 到達状態で ID グラフの到達と実 Generated の存在が iff。実 Display では atom の追加だけで固定ポートの旧 Known は改善しない。 |
| `GeneralRebaseArchiveTrust280.trusted_forward`, `cache_iff` | 旧履歴 effect と新履歴 effect が両方向に対応するなら、任意の trusted fact list に整合する新 trusted list があり、各 cache snapshot に対し CacheSound は iff。 |
| `GeneralRebaseGraphBisim280.step`, `GeneralRebaseCompactMachine280.lift_path`, `lower_path`, `acc_exact` | 対応した任意の状態から実一歩と次状態の対応を得る。圧縮機械の有限経路は双方向、開始点で Acc iff。 |
| `GeneralRebaseArchiveLocal280.adapter_local`, `GeneralRebaseCompactSource280.evidenceAt_iff` | 対応した状態の全 frontier と EvidenceAt を双方向に保存。 |
| `GeneralRebaseTicketLedger280.source_exact`, `GeneralRebaseArchiveReplay280.source_roundtrip` | 任意の初期 source と実経路について、台帳の展開が元の sites/centers/edges と厳密に等しく、消去時点の全 versioned effect snapshot を含む journal は復元で元に戻る。 |
| `GeneralRebaseStoredStep280.match_state`, `acc_exact` | 同じ初期 source から到達する任意の二状態について保存遷移 iff 実遷移。任意の到達状態で Acc iff。 |
| `GeneralRebaseCompactRegression280.old239_remains_nonaccessible`, `old240_remains_nonaccessible` | 前回の旧反例の初期状態は、新しい exact edge 圧縮でもアクセシブルでない。 |

## 残りと検証

- I-52 の後継に向け、raw の参照を扱う位置表、グラフ圧縮、保存と復元の橋を閉じた。一般 Acc、正規化・置換した新しい operational boundary 全体、すべての裸変数再訪で読み出し先と旧支持が衝突しないこと、12 の法律と full language EvidenceNode は未証明。
- 次の候補: (1) 各 fixed port の live 読み出しと immutable 過去表を分け、再観測で write set が私有・有限支持に閉じることを実 source compiler から出す。(2) 辞書グラフを増やさない install に、公開意味を真に変えることまたは有限な phase の消費を要求する新しい規則を、旧全割当の切り捨てと区別して定義・検証。(3) 新規規則の下で実頻出の bare child 再訪が安定し、旧239/240を再現しないことを示す。
- Yulang2 は監査 branch の `notes/audit/x-oracle.md` の X1（名目ラッパーを通す）と X3/X5（構造型の検査限界）を参照した。今回の内部表現が旧実機にもあるとは主張しない。実機再試験なし、意味の選択を要する質問ノートなし。利用枠不明。
- 30新規Libraryモジュール、8独立監査、386宣言。すべてPASS、標準3公理のみ。型付き使用例6本と実行テストもPASS。
- 新規 Lean 原本は trust=0・警告エラー化で再検査、すべての監査は単独 import (Yulang.* のみ)。両基準の diff と verify-lean --no-build を再確認。全 Lake build、全統合検証、CI は実行しなかった。
- [固定ポート設計](../design/2026-11-19-cycle280-fixed-child-ports.md) / [snapshot 圧縮](../design/2026-11-19-cycle280-effect-snapshot-compression.md) / [ticket 台帳](../design/2026-11-19-cycle280-child-ticket-ledger.md) / [packet 一括表](../design/2026-11-19-cycle280-packet-port-batch.md) / [再検査](../verification/cycle280/independent-recheck.txt) / [検証コマンド](../verification/cycle280/commands.txt)
- 追加の既存検査: 206・218 の監査は欠けていた個別依存の再構築後に PASS、230 の2本・279の2本も PASS。239 の個別監査も依存再構築後に PASS。240 の全旧監査は依存不足のため未再構築という内訳を、[補足検査](../verification/cycle280/legacy-compat.txt)に記録。今回の監査では239/240両方の非停止と復元の閉じた定理を再検査した。
- [新規モジュール](../verification/cycle280/module-list.txt) / [監査宣言一覧](../verification/cycle280/audited-declarations.txt) / [次の意味的進捗](../design/2026-11-19-cycle280-next-strict-port-progress.md)
- 今回の公開対象は 58 パス。最終公開後、プッシュ前の検証済み全 tree と受け取り直した tree を照合する。
