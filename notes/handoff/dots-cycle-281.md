# dots-main cycle 281: 有限の進捗判定と、固定集約への正確な読み戻し

- 開始 2026-11-19 20:30:00 UTC。終了 2026-11-19T21:20:00Z（50.00 分）。integration/m1-final は開始時 `6ffaba4a`、終了前再読時 `707497ab`。両方とも作業 tree の祖先。standing orders と inbox を開始時に新しく読み、途中にも照合した。ACTIVE、I-51〜53、凍結ファイルを保持。280 の heartbeat と報告は `e62f33b58` で完了済み。作業者は一人、書き込み先は private `work/dots-main` のみ。
- 20 分・30 分のチェックポイント付近で実行環境が短く切れた。公開前の head を確認し、未反映の分だけ再開した。30 分時点は `351cf498`、40 分時点は `cf7b75c5`。いずれも検査済み tree と受け取った tree が一致した。

## 1. 履歴の別名ではなく、実際の新情報で一歩を数える

`GeneralRebaseChartStep281.Step` は旧 mixed kernel の実際の一歩のうち、(a) plan を増やさない管理更新、(b) 新しい固定グラフ辺、(c) 有限リスト上で新しく含意される公開命題、のいずれかを許す。公開命題が該当の状態を完全に記述する局所条件の下では、公開割当の集合が真に縮むことと新しい命題の獲得が同値。どの chart も完全だとは仮定しないし、単なる版付けで全 raw 割当が減ることを公開進捗と呼ばない。

`GeneralRebasePhaseMachine281.Step` はさらに、履歴にまだない owner × phase を消費する実 install を許す。実 owner 候補は checked source の Paterson 有限リストから、phase は codec の有限値から取り、履歴で増やせない。任意の chart・有限 codec・初期 source 到達状態について、この定義した Step の全有限列の長さの上限と `Acc` を証明した。実行版 ledger は plan の有限キーを重複なく保存し、新しい phase を検出する iff を持つ。これは後継の部分関係の停止性で、すべての必要な処理がその関係に入るという一般の完全性ではない。

- 実 `Display (list 'a)` の `where 'a: Display` では全割当が同じでも新しい辞書 edge を数えられる。
- compound238 の実 install は旧公開モデルに存在した具体的な `.exactEmpty` の例を named output の本文で除く。公開像は旧の条件、次は旧の条件と出力本文の連言まで示した。
- I-45 の optional は、最初の公開出力、無増加の再観測、point 後の公開型・グラフが変わらない二回目 install を区別した。最後は実 `loose → point` phase で残る。point 時点で exact Evidence leaf を欠く割当があり、同じ公開値のまま私的条件を満たせることを構成した。これは任意の raw Evidence を保存する証明ではない。
- 旧 239・240 は、それぞれの旧公開射影上、どの chart を選んでも実反復 install が新しい公開命題も辺も増やさない。固定 owner 一回の codec で最初の実 round を残し、以後の全反復 install を除いた。旧 raw kernel の非停止には変更がない。

## 2. 一般の raw 集約から固定書き先への射影

同じ上下端点が複数捕捉された場合は、lower union と upper intersection を二つの単純なコピーに畳める。異なる捕捉も含む任意の packet に対し、各 binder の lower union / upper intersection をそのまま式にした固定版も構成した。singleton は新規行なし、0 個は既存 raw merge と同じ bottom/top。版付きコンパイルの atom 列は旧実装の merge atom 列と構文的に厳密に一致する。型のコピーは row 値を変えず、式の参照は capture report 由来の旧 raw source 支持にある。

固定 (seed・owner・宣言・binder・上下) アドレスは任意の旧 source 到達状態の **raw source 支持**から外れる。初期は seed 以下、証明済みの管理更新では支持は変わらず、install が追加できる予約は versioned keys と固定の異なる purpose に限られるため。任意の refresh が metadata `allocated` を更新できるため、そのリストにないとは主張しない。

実 replay を旧 raw source 上で読み戻すと、正確に「旧 raw Models ＋ cross ＋ self-check ＋ 旧支持に書き先が残っている版付き行の式」になる。fresh な行の値は共同でコピーできるので存在射影で消える。固定版は到達状態で最後の項を持たない。したがって両者の射影がすべての割当で同じ ⇔ 旧 Models・cross・self-check が保持版付き行をすべて含意する。版付き側の fresh を一般定理の前提から外した代わりに、正確な同値条件として残る場合を特定した。構造 slot と graph に変更がないため、任意の ID の raw `Known` は両 replay で同じ。

旧 239 と 240 の実列を全 n で検査した。下側・上側とも、現版の書き先は以前の予約・構造 slot・旧 atom の三つのどこにもない。実 replay と固定 replay の旧 raw source 上の射影と全 ID の `Known` は従って一致する。固定書き先は n によらないが、捕捉の読み元は動く。固定名への変更自体は古い反復を止める証明ではない。

最後に、cross/self-check と残る版付き等式を一つの有限 atom リストにした。任意の実 plan の**一回の raw replay**で、そのリストは旧支持から読め、旧 raw Models に相対的に厳密。その旧射影が真に縮むことと、リスト中の具体的な一つの atom が新しく含意されることが同値。さらに、当該 atom の参照先を全て観測に含めれば、他の raw source 名は観測から落としても、同じ連言分解と進捗判定が成り立つ。旧 state 全体をその小さい観測で復元できると仮定しない。各 packet の有限支持であって、全到達族に共通の固定有限 chart ではない。

## 主な Lean 宣言

| 宣言 | 前提・結論 |
| --- | --- |
| `GeneralRebaseSemanticChart281.relative_loss_iff` | 旧モデルが base に属し、新モデルの chart が base 上で完全なら、任意の旧・新状態でモデル喪失 iff 新規含意。 |
| `GeneralRebasePhaseMachine281.length_bound`, `accessible` | 任意の有限 chart/codec・checked source 到達の開始点で、定義された Step の列の一様上界と `Acc`。全 raw Step の結果ではない。 |
| `GeneralRebasePhaseFixture281.all_three`, `retained_service` | 実 optional で具体的二段階 codec により三歩すべてと point 後の private install を保持。 |
| `GeneralRebasePhaseLoop281.Version.no_repeat`, `Loose.no_repeat` | それぞれの実旧列で任意の n の最初の round 後、同じ owner の次の install は新 Step では起きない。 |
| `GeneralRebaseChartDelta281.delta_exact` | 旧支持を保つ同時コピー、公開条件の不変性、定義的分解が与えられた任意の local delta では、公開 chart 上の拡張 iff 旧公開像と新しい有限命題の連言。 |
| `GeneralRebaseAggregateCompile281.packet_exact`, `GeneralRebaseAggregateLift281.project` | 任意の packet で同一捕捉 compiler が成功すれば、全 raw merge 条件 iff コピー等式。書き先が source 支持の外なら旧支持上で射影を厳密に保つ。 |
| `GeneralRebaseFixedOrigin281.fixed_absent` | 任意の source 到達状態・owner・宣言・上下タグで安定したアドレスは raw source にない。 |
| `GeneralRebaseLoopReplay281.Version.projected_equal`, `Loose.projected_equal`, 各 `known_equal` | 旧239・旧240それぞれの任意の実段階で旧 raw source への射影と任意 ID の Known を固定 replay が厳密に保つ。 |
| `GeneralRebaseTermAggregate281.versioned_atoms`, `reads` | 任意の packet（同一 capture の前提なし）で、versioned merge atom は term compiler の atom 列に等しく、どちらの書き先方式でも式は旧 raw source のみを読む。 |
| `GeneralRebaseTermReplay281.actual_project`, `replacement_iff`, `same_known` | 任意の plan の versioned raw replay の旧支持への射影を厳密に分解。source 到達状態に packet の context が一致するなら、固定版と射影が同じことは保持版付き行がすべて含意されることと同値。Known は任意 plan と ID で一致。 |
| `GeneralRebasePacketChart281.supported`, `public_cut_iff` | 任意の plan で局所リストの各 atom は旧 raw source に支持され、一歩の旧支持への射影の真の縮小 iff 局所リストのいずれかが新しく含意される。 |
| `GeneralRebasePacketFootprint281.project_through`, `projected_exact`, `footprint_cut` | 旧支持の任意の部分リストでは共同リフトと正確に対応。リストが全新規 atom の支持を含めば存在量化の外に atom を出せ、atom の構文的参照だけの footprint 上でも進捗が iff。 |

## 境界と次の証明

I-52 の部分後継と有限の rank、実回帰および raw 射影の橋を得た。定義した filter と固定 replay を通した新しい operational compiler 全体の双方向対応、旧 snapshot や live consumer の固定表への移植、outputs/where・EvidenceNode の完全性は未証明。共通の公開支持と chart を得るためには、保持版付き式の右辺を source/owner basis に展開し、読む側（center・出力・子・証拠）も保ったことを確認する必要がある。次は (1) `TermReplay.replacement_iff` の保持条件を current + 旧 consumer から証明する、(2) `PacketChart.pool` を共通の有限 basis 上へ正規化・lift する、(3) 実 install の private evidence phase が有限であり必要な phase を失わないことを generalize する。

Yulang2 の監査 branch `notes/audit/x-oracle.md` の X1（名目ラッパー）、X2（構造引数に依存した where の結果・動作差）、X3/X5（構造型の検査限界）を参照した。今回の判定は内部表現の Lean 検証であり、新しい言語規則はなく旧実機の再実行はしていない。意味の選択を依頼する質問ノートなし。使用量の残りは不明。

## 検証・公開

- 29 原本モジュールと 12 独立監査（301 宣言。標準公理の範囲内）、barrel に各一回、型付き使用例 6 本、実行テスト 8 行がすべて PASS。実行例は両反復の固定 slot が同じ、版付き slot が異なる、optional の実捕捉に loose/point の異なる phase が付く、同 phase の再登録で台帳の長さが増えない、別 phase なら増えることを確認。
- scoped `lake env lean --trust=0 -M 3200 -DwarningAsError=true -R .` のみ。I-51 の監査ファイルは `Yulang.*` のみ import し、一つずつ単独で検査。統合基準と cycle 280 基準の `verify-lean.sh --no-build`、`git diff --check`、凍結対象と禁止構文を検査。全 Lake build、全統合検証、CI は実行していない。
- [検証コマンド](../verification/cycle281/commands.txt) / [再検査](../verification/cycle281/independent-recheck.txt) / [モジュール一覧](../verification/cycle281/module-list.txt) / [監査宣言一覧](../verification/cycle281/audited-declarations.txt) / [実行出力](../verification/cycle281/executable-probe.txt) / [統合基準の出力全文](../verification/cycle281/integration-diff-full.txt) / [前周基準の出力全文](../verification/cycle281/prior-diff-full.txt)。
- 最終公開の対象は 77 パス。expected-head の非 force 更新後、最終 tree と heartbeat・報告を受け取り直して照合する。
