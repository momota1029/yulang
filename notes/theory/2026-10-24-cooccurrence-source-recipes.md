# 共変位置から受領・解除対応表を構成する

Date: 2026-10-24
Revision: 1, primary construction; independent review pending
Post-freeze review: r1 は S1–S6 の明記された範囲で独立査読 ACCEPTED、BLOCKING/MAJOR 指摘なし。[査読記録](../../tasks/agent-loop/sprints/cooccurrence-source-20261024-outcome.md)を参照。この receipt のみ査読後に追加した。
Author: `/root`; no delegated authors of this file
Contract: `tasks/agent-loop/sprints/cooccurrence-source-20261024.md`, SHA-256 `f2c29073586fad9ac2ec260505f5b58ac83eab12290de664de51bf8a13073e60`
Baseline: `5fb43a1e61336153496f745e51d6782816561f88`

## 1. 元の義務と今回構成するもの

[前稿](2026-10-24-cooccurrence-release-preservation.md)は、同じ共変位置を持つ成分をまとめる商 q と、動的証拠を保持する表示の保存を示した。本稿はその一つ前の、位置集合と入力対応表を生成する部分を構成する。入力を「完成した正しい解除対応表」とはしない。

入力は、有限な型付き signature graph、source の実際の entry を識別する root、元の変数 binder、実行で得られた lexical receipt 環境である。出力は位置の判定手順、元の入力を列挙する有限 recipe、実際の受領を捕捉した表である。全 source からこの signature graph が生成されること、すべての型簡約がこの graph と対応することは別の義務として末尾に残す。有限 graph の定理を非正則な全 instance の有限性へ拡張しない。

動作原理から共有変数と解除を説明するという[直接訂正](../design/2026-10-24-cooccurrence-release-clarification.md)を適用する。入力選択の追加仕様を要求せず、`A_all` という旧候補の採用も前提にしない。recipe は保護の起点を対応付ける証明上の構成であり、全入力位置に新しい保護を作る規則ではない。

## 2. 極性を持つ有限 signature graph

有限 graph G の node は型の構成位置である。異なる entry root、field、tuple slot、Function port を識別する。辺は child label と符号 `+/-` を持つ。同じ node の child label は相異なる。binder 解決は完了しており、原子 a は表示名ではなく元の binder identity を含む座標である。局所な抽象 effect 成分の有限集合を `V(v)` とする。具体 effect atom、値型変数、grant、receipt はこの集合と混ぜない。

辺の符号は次の構造から定まる。

| 構造 | 子への符号 |
| --- | --- |
| Function の argument Value / argument Effect | 反転 |
| Function の result Value / result Effect | 維持 |
| tuple、record field、variant payload、row tail | 維持 |
| interval の lower / upper | 維持 / 反転 |
| 宣言から既に展開された nominal の引数 | 当該 bound 構造に従う |
| 型 binder の body、regular recursive reference | 維持。束縛 identity は解決済みの参照を使う |

opaque な nominal の variance を推測しない。有限 graph が与えられない instance はこの構成を適用済みとしない。再帰参照も一つの label を消費する辺として表すので、query は有限の経路語について実行できる。これは無限に深い経路を事前に展開する操作ではない。

root r の初期符号を `σ(r)` とする。位置は root と有限 child-label 語の対 `p=(r,w)` である。語が graph 上を辿れるとき、その終点と符号を `end(p),sign(p)` とする。表示名が同じだけの別 root は別位置である。

`I⁺(a) = {p | sign(p)=+, a∈V(end(p))}`。

**定理 S1（位置判定の構成と完全性）。** 位置 query は語の長さに比例する有限回の辺選択で終わり、成功することと、その root から対応する極性付き構造経路が存在することは同値である。有限 graph では `I⁺(a)=I⁺(b)` を有限に判定できる。

**証明。** 空語では root が終点で符号は初期値である。非空語 `ℓw` では一意の ℓ 辺を一つ辿り、その符号を掛けて残りの w を処理する。帰納仮説を適用すると traversal の成功と構造経路が一対一に対応する。辺がなければ両側とも不成立である。

集合 I は無限になりうるが、判定には有限の signed node graph `Nodes(G)×{+,-}` を用いる。全 root から到達可能な `(v,+)` を列挙し、各点で `a∈V(v) ⇔ b∈V(v)` を調べる。全点で一致すれば任意の有限経路の終点で一致する。異なる点があれば、その到達経路が I の差の証人になる。正の到達点に一度も現れない変数同士は併合対象から除く。□

これは全型の無限展開を必要とせず、有限の到達点集合から正確な共変位置の一致を判定する構成である。root/符号を落として単に同じ type node を共有しているかだけを調べる構成ではない。

## 3. 入力 recipe を表からではなく graph から作る

実際の formal/component entry の有限集合を K とする。各 k は source 導出の entry root `in(k)` と、その下で元の effect 座標を読むための構造経路を持つ。K は実行後に見つけた event の一覧ではない。通常 entry が受領する carrier の識別子であり、未使用の潜在値についても静的に存在する。

各 k,a について、graph を `in(k)` から辿り、終点が a を含む effect component である語の言語を `L(k,a)` とする。`L(k,a)` は小さなコピーを個別に作らず、同じ有限 graph と開始点・受理点の参照で表せる。空言語かどうかは到達可能性で判定できる。入力の場所には共変・反変の両方がありうるため、ここで全てを正極性とみなさない。保護の発生条件は既存の実際の entry/profile 規則が別に判断する。

`q(a)=[a]` を非空 I⁺ が等しい原子の class とする。正の出力位置 p とそこに現れる class c に対し、次を機械的に構成する。

`Recipe(p,c) = {(k,a,L(k,a)) | q(a)=c, p∈I⁺(a), L(k,a)≠∅}`。

K と原子集合が有限なので recipe の entry 数は有限である。潜在値の経路語の集合が無限でも、entry の内容は上記の有限 recognizer への参照である。

**定理 S2（集約 recipe の厳密性）。** `p∈I⁺(a)` が class c の一要素で成り立つなら、全 a∈c で成り立つ。従って Recipe(p,c) は、その class に属する各元成分の入力 recipe のタグ付き和集合に一致する。別の正位置だけに現れる成分を混入しない。

**証明。** class の定義により I⁺ は全要素で等しい。p の membership は従って全要素で一致する。Recipe の内包式を a ごとに分割すると、元の入力言語を持つ `(k,a,L(k,a))` の和集合になる。元の a と k は消去していない。I⁺ が異なる a は q(a)=c を満たさない。□

この結果は、同じ変数の表示を複数入力のために使える根拠を与える。型の解や effect family が偶然等しいという別の条件は使っていない。

## 4. 実際の受領と潜在経路を結ぶ

実行済みの entry が構成した lexical 環境を ρ とする。`ρ(k)=b` の b はその entry の実際の receipt であり、元 receiver `recv(b)` を持つ。まだ entry がない k は ρ の定義域にない。実際の output entry は fresh target t を作り、次の表を一度だけ捕捉する。

`B_t = {(k,a,b,recv(b),L(k,a)) | (k,a,L(k,a))∈Recipe(p,c), ρ(k)=b}`。

receipt の予約が既存の entry 規則で認められる場合でも、この表の作成自体では scope witness や event を発生させない。実際に生成された scope s の原点は `(b,r,a,j)` と書く。ここで j は元の input root k を含む完全経路 `(k,w)` である。a は元の原点を指す証明上の座標であり、商を取った表示変数だけではない。

`Match(t,s) ⇔ ∃(k,a,b,r,L)∈B_t. Origin(s)=(b,r,a,(k,w)) ∧ w∈L`。

**定理 S3（受領の正確性と新しい呼出しの分離）。** Match の成功は、元の入力位置・原子・実際の receipt・元 receiver・有限経路の全てが同じ tuple に一致することと同値である。別 receipt b' は、同じ class・family・型を持っていても、この表にある b と交換できない。

**証明。** Match を展開すれば五つの照合は同じ表の一行で行われる。S1 により経路判定にも余分な成功はない。逆に一致する一行と構造経路があれば、その行が存在量化の証人になる。新しい通常呼出しの b' が既存 support に対して fresh なら、捕捉済みの B_t に b' の行はない。ρ を後で拡張しても B_t を更新しないので、後から混入することもない。別 k が同じ b を正当に共有する場合は root を含む j が区別を維持する。□

**系（潜在使用）。** 表の捕捉後に元の b の潜在値を実際に使い、Origin が生成された場合にも S3 は適用できる。表は潜在 event の列挙を必要とせず、有限語 w の判定をその時点で行う。

**定理 S4（前稿への適用）。** この B_t を前稿の fiber 表示へ渡し、同じ actual target の元成分別の表を集約した場合、Match・actual crossing の更新・保護 query は集約前と一致する。

**証明。** S2 により class の選択は正しい元成分の和集合である。S3 の Match は同じ tuple で評価するので、和集合内の membership は元のどれか一行への membership と同値である。前稿補題 5–6 の集約表の前提をこれで構成した。実際の crossing は actual packet の Origin と経路だけを調べるので、未使用の別 receipt を同時に解除しない。前稿の保存定理を適用する。□

S4 は表の生成前提の一部を具体的な traversal に置き換える。receiver の寿命、保護導入政策、permission、元の source graph の正しさまでこの系だけで証明したとはしない。

## 5. 変数名変更と再帰を含む輸送の範囲

**定理 S5（同時の単射改名）。** graph の原子/binder、entry root、有限経路 label、receipt、receiver、target に、それぞれ整合した単射改名を施すと、S1–S4 の構成はその改名と可換である。

**証明。** 辺、符号、元の binder 参照を保つ graph 同型の下で traversal は一段ずつ対応する。従って I⁺ と L は経路同型による像であり、I⁺ の一致・非空性も保たれる。Recipe の各行に同じ写像を施すと改名後の内包式を満たし、逆向きも像上の逆写像で従う。ρ の対応する entry と同じ map を使えば B の行も対応する。単射性により tuple の等号・不等号を保存し、Match と集合和による crossing 更新が可換になる。□

これは未実行 recipe の一貫した freshening を扱える。保存済みの動的 evidence を raw resume のたびに freshening する規則ではない。fresh-use と capture が実際にどの名を新しくし、どの外部 receipt を保存するかは[既存の所有/capture 証明](2026-10-15-effect-scope-ownership-capture.md)の分離条件を満たす必要がある。

型変数を任意の型へ置換する操作は graph 同型ではない。新しい構造位置・別の極性・追加の effect 成分を持つ場合、S5 の単射改名として扱わず、置換後の graph と recipe の生成を照合する。その一般の correspondence は未完である。非正則 nominal の無限個の instance を一つの有限 graph に押し込める主張もしない。

## 6. 実際の collector との接点

Oracle の固定 commit `a58eefc31e22141574b6f20c6a5748151c6d79f1` の `compact/analysis/occurrence/mod.rs` を用いる。`visit_type_co_occurrence` は最初にその node の `along_group` を記録し、Function の二入力で反転、二出力で維持する。tuple/record/variant/row の構造辺と interval の lower/upper の向きは §2 の表に一致する。`record_group` は前稿補題 1 の交差更新である。

**補題 S6（再帰中心を除外しない有限構造走査との一致）。** root/role/bound の有限な構造走査で `ignored_vars` と `extra_vars` が空であり、同じ atom が同じ元 TypeVar を表すとする。各通常 node の group を位置とする I⁺ の一致と、collector の正極性 group 全体についての incidence の一致は同値である。row の補助 group もこの同値を壊さない。

**証明。** 通常 node の `along_group` の Var 部分はちょうど V(v) なので、その group の記録と構造経路の訪問が対応する。Exact 項は Var membership に影響しない。子の列挙と極性を上記の構造の場合分けで確認し、有限走査へ帰納する。

row の補助 group の Var 部分は、その tail と入れ子 tail の Var 集合の和である。`visit_type_co_occurrence` は同じ tail と入れ子 tail の通常 group も同じ極性で訪問する。通常 group 全てで a,b の membership が等しければ、その部分集合の和である補助 group でも等しい。逆に、全記録 group で等しければ、その中に含まれる通常 group でも等しい。補助 group が繰り返し記録されても同値は変わらない。□

この補題は phase 内の正極性判定を対象とする。recursive center を `ignored_vars` に入れる処理、別根拠の interval equality、負極性 pass、sandwich、変数除去、既に別の理由で併合された union class には適用範囲を拡張しない。source の型が compact root へ構成・合流される段階の対応も、collector の読み取りだけでは得られない。

## 7. 何が閉じ、何が残るか

位置集合が与えられるという前提を、有限 signed graph 上の構成と判定 S1 に置き換えた。完成した入力対応表が与えられるという前提を、入力 root と原子を走査して作る Recipe と actual lexical receipt からの B_t の構成 S2–S4 に置き換えた。単射改名 S5 と限定された実 collector 対応 S6 を得た。

元の CO-1 の残りは、すべての source constructor、型の compaction/merging、recursive center、非正則 instance の profile がこの構造対応を持つこと。CO-2 の全 substitution は別証明。CO-3 の経路集約は[重みの集約稿](2026-10-24-scoped-weight-join-compatibility.md)へ接続するが、異なる経路の stamp と protection を別々に union してよいとはしない。CO-4 の任意の型代入と全 fresh-use/source consumer の対応は、単射改名の定理では閉じない。

本稿は source-relative な有限 signature recipe の構成であり、既存の Pi_flow や A_all の政策採用、現 compiler の全正しさ、source 由来の反例、型健全性全体の完了ではない。元の全 source 領域をこの有限 graph の場合だけへ制限しない。

## 検査と凍結

関連 source は immutable Oracle object と固定 manuscript を read-only で確認した。実行例・tests・build・compiler 変更はない。証明は経路長・有限構造・有限実行操作の帰納と集合の等式による。元の依存 hash は contract に固定する。独立査読対象として r1 を凍結する。primary による作成を独立査読とは数えない。
