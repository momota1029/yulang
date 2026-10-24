# Yulang の意味論と型健全性：統合稿

2026年10月24日。研究稿。既存の採用済み仕様と、未採用の具体化を区別する。

本稿は、値型、効果、受領境界の保護、解除、継続の寿命を同じ証明の中で読むための入口である。**Yulang 全体の健全性は、まだ証明完了とは判定できない。** 未決定の意味論、全表層構文への対応、Simple-sub の元の A/B 義務が残っている。以下では到達した定理を述べ、残りを実装作業だけの問題に置き換えない。

## 1. 定理の対象

全体目標は、承認された source 領域の任意の有限プログラムについて、その型導出から実行意味論を構成し、全有限実行 prefix に対して次を示すことである。

1. 正常値、操作の payload/response、保存した継続が型を保つ。
2. 閉じた状態は正常値、型付き request、言語で定めた failure、次の一段のいずれかとなる。型不整合による stuck 状態にはならない。
3. 外へ出る効果は immediate 契約に入り、返却した値と継続の将来の効果は対応する latent/reentry 契約に入る。
4. 保護と許可は実際の受領境界と同じ操作 instance に属する。別の呼出しへ許可を移したり、失効した receiver を再開だけで復活させたりしない。
5. 引数の保護と出力への輸送・解除を先に定め、共起分析から得る共有変数と `'e?` の表記がその動作を保つことを示す。別の保護や効果そのものを消さない。

無限実行は許す。有限 prefix の不変条件から「最初の型安全性違反」が存在しないことを示す。停止性、主型性、推論器がすべての自然な導出を発見することは別の必要定理であり、上記から自動的には得られない。

## 2. 原稿と依存関係

| 対象 | 定義・証明の所在 | 今回の扱い |
| --- | --- | --- |
| 値、計算、完全 Call、shallow handler、raw continuation | [操作稿](yulang-operational-type-safety-ja.tex) §§1–6 | 元の有限導出を使用する。旧 evidence freshening は使用しない |
| receiver の寿命、source recipe、rank-2、解除、修正 permission | [ソース稿](yulang-source-type-safety-ja.tex) §§1–15 | 規則ごとの具体化。未採用の政策を含む |
| 有限選択証拠から code を作る | [選択稿](yulang-dot-selection-safety-ja.tex) | 証拠が与えられたときの構成。resolver 完全性とは区別 |
| 隠れた複数 witness、解除、再観測の有限表示 | [修正機械の simulation](../notes/theory/2026-10-24-corrected-machine-simulation.md) | 明示的な保守的構成と、既存 graph への適用条件 |
| 共変位置での共起と解除対象の集約 | [共起・解除の保存](../notes/theory/2026-10-24-cooccurrence-release-preservation.md) | 共起条件と provenance を保持する集約。全 source への対応義務は区別する |
| 位置から入力対応表を作る | [共起と source recipe](../notes/theory/2026-10-24-cooccurrence-source-recipes.md) | 有限 signed graph の traversal、実際の受領・潜在経路の照合、単射改名 |
| 複数経路の保護状態を集約する | [scoped weight の join](../notes/theory/2026-10-24-scoped-weight-join-compatibility.md) | 観測ごとの必要十分な要約。実 consumer と weight の対応は別義務 |
| handler の真偽分岐と No の後の再検索 | [joint cell による分岐保存](../notes/theory/2026-10-24-correlated-handler-observation.md) | 候補機械の現在状態から両分岐を構成。有限 table の経路と具体 successor inclusion を区別 |
| source の各構文から制御 graph を作る | [全制御経路と失敗終端](../notes/theory/2026-10-24-source-core-action-coverage.md) | 13式・11 pattern・3 statement と直接証拠から生成。失敗専用表示を含む候補構成。記載した前提の下で独立査読通過 |
| Yumark 内部の静的 node | [表層展開の証明](../notes/theory/2026-10-24-surface-elaboration-closure.md) | builder の全構成と値型導出。interpolation 等は未完 |

旧稿の定理を使う際は、その証明が参照する機械を固定する。訂正後の機械の結論を、訂正前の小さい効果型に無条件で適用してはならない。

## 3. 値型と完全 Call

実行型の主要な形は次である。これは効果を忘れた射影であり、完全な型は後述の契約を併せ持つ。

```text
A,B ::= 1 | Bool | Int | Str | (A1,…,An)
      | {li:Ai} | Variant | D⟨A1,…,An⟩
      | U A | C(A,B) | ∀a.A | μa.A | A∨B | A∧B | ⊤ | ⊥
```

`U A` は A を返す保持計算、`C(A,B)` は A を返す carrier を受領し B を返す callable である。Value entry は受領後に carrier を force し、Computation entry は carrier を保持して、body の実際の Force でだけ実行する。

```text
callee の評価
  → 呼出し owner の確保
  → 未実行の argument carrier の受領
  → entry の Value/Computation 規則
  → body
  → declared result consumer と result adapter
  → 返却
```

argument adapter は argument の保持計算の内側に置く。変換のためだけに新しい source 呼出しを捏造しない。各 App は一つの whole type instance を使い、引数・結果・効果・family・profile を別々に具体化しない。

全称導入は値判断に対して行い、自由な環境・共有資源の型に量化変数が現れないことを要求する。constructor application の計算全体を再一般化する必要はない。格納された `∀a.A` の payload を pattern で取り出すと、その全称型を保持し、各使用で型適用する。共有セルの型を使用ごとに変更する規則はない。

optional record の直接適合には非推移的な場合がある。直接証拠 `A ↝ B` と `B ↝ C` から、存在しない一段の `A ↝ C` を導入しない。必要なら二つの adapter を実際の順序で合成し、その code を型付けする。

## 4. 効果と許可を区別する

操作は一つの宣言 identity と同じ型引数 instance を持ち、payload `P_o` と response `Q_o` を結ぶ。request の現在の寄与を `q` とする。効果行に現れる operation の集合、受領による保護、注釈の許可、handler が実際に選ばれることはそれぞれ異なる事実である。

修正候補では source profile を次のように構成する。

| source の箇所 | 新しい保護 | 許可 |
| --- | --- | --- |
| 無注釈 formal の実際の upper output | 生成する | なし |
| negative concrete `[C, 'e]` | 生成する | 指定した具体 instance C |
| computation `[_]` の direct force | 生成しない | Wildcard |
| callback result `[_]` | 生成しない | 新しい許可なし。既存 view は輸送 |
| positive allowance / 生成専用 binder | 生成しない | なし |

これは[ソース稿 §15](yulang-source-type-safety-ja.tex)の修正候補であり、全 source に対する採用決定ではない。

候補 handler h に対する query は、**同じ寄与、同じ経路、同じ現在状態**で計算する。

\[
\begin{aligned}
B &= Active(h)\land Active(owner(h))\land RoleAllows(q,h)\land Covers(q,h),\\
Eligible^*(q,h)&=B\land\bigl(\neg P\lor G_C\lor(G_W\land\neg P_F)\bigr).
\end{aligned}
\]

P は未解除の有効な保護 witness の存在、`P_F` はそのうち receiver が `owner(h)` と異なる witness の存在である。`G_C,G_W` は handler owner 自身の authenticated route から得た concrete/wildcard 許可であり、別 receiver の許可ではない。

**命題 P1（wildcard による外来保護の迂回の排除）。** `P_F=1,G_C=0` なら、Wildcard の有無によらず `Eligible*=0`。`B=1,G_C=1` なら `Eligible*=1`。いずれも query だけでは新しい event を発生させず、arm の成功も保証しない。

**証明。** `P_F⇒P` なので第一の場合は三つの disjunct がすべて偽。第二の場合は中央の disjunct が真。式が書き換える状態はなく、perform と arm 試行は別の実行規則である。□

旧 `B∧(¬P∨G_C∨G_W)` との違いは、同じ分離済み packet に対して正確に `B∧P_F∧¬G_C∧G_W` の場合である。これは Boolean の場合分けで従う。旧 profile と新 profile 全体の観測同値を意味しない。

## 5. 保護の起点と解除

[直接の訂正](../notes/design/2026-10-24-cooccurrence-release-clarification.md)に従い、`'e?` 自体を独立した実行意味論の出発点にしない。先に実行前の引数の保護があり、全く同じ共変位置に現れる対象を共起分析が同じ変数へまとめる。その対象を解除のためにまとめても動作が保存されることが証明課題である。「複数入力のどれを解除対象に選ぶか」という追加の仕様選択ではない。

以下の Origin・target・L は、この動作を記述する既存の候補表示である。共起分析との対応が必要であり、ユーザーの訂正だけで候補全体を承認済みの規則へ読み替えない。[共起・解除の保存稿](../notes/theory/2026-10-24-cooccurrence-release-preservation.md)は、静的変数をまとめることと動的な受領を同一視することを区別して、この接続を扱う。

動的 receipt b、元 receiver r、静的 binder identity ε、typed path j から起点を作る。

\[
Origin(s)=(b,r,\epsilon,j).
\]

型の解が等しいだけでは b や ε を等置しない。共起による静的変数の併合も、動的 receipt や元 receiver を等置する根拠にはしない。候補表示では印付き出力の target t が、その output entry で lexical な入力 receipt の表 `B_t` を一度捕捉する。ソース稿の `A_all` は同じ binder の対応する全入力を集める具体化である。必要なのは、この表が保護・共起・出力の動作を正しく表すという導出であり、全入力か指定入力かを改めて選ぶ回答ではない。

一つの経路 witness w は起点 `s(w)` と、その経路で実際に輸送された target 集合 H(w) を持つ。同じ event に二経路があっても、一方の H を他方へ移さない。現在の解除履歴を `L⊆Scope×Target` とする。

\[
Released_L(w)\iff\exists t\in H(w).\ (s(w),t)\in L\land Active(r(s(w)))\land Match(t,s(w)).
\]

有効保護は、元の protection、現在の activity、receipt/route/Observe 条件を満たし、かつこの Released が偽の witness から計算する。

実際に request が `release_t` の外へ越えたときだけ、次を追加する。

\[
L'=L\cup\{(s,t)\mid s\in Scopes(q),\ From_s(q),\ Match(t,s),\ Active(r(s))\}.
\]

From は解除前の独立した actual route から計算する。handler が後に消した効果の集合から逆算しない。正常返却は t を結果へ輸送するが L を変更しない。latent value に t を保存することは、新しい release delimiter の設置ではない。

**定理 R1（履歴と局所性）。** 空の L から始まる任意の有限実行で、`(s,t)∈L` と、その同じ対について上の条件を満たす outward crossing が以前にあったことは同値である。w の解除は、その w が運ぶ target に限って作用する。固定した同じ crossing 列から得る追加集合は冪等である。

**証明。** 実行長に帰納する。crossing 以外は L を固定する。crossing は表示した有限集合との和なので、追加された各対には現在の transition が証人となり、それ以外は帰納仮説を用いる。逆向きは集合和が既存対を削除しないことによる。解除 query は `s(w),H(w)` の実際の membership を検査するので、H にない target への更新はその witness の Released を変えない。冪等性は集合和から従う。□

この可換性は追加集合の計算についてだけ成り立つ。source 上で二つの handler/delimiter を並べ替えると crossing 列そのものが変わりうるため、プログラムの交換法則は導かない。

### 5.1 共変位置から入力対応を作る

[構成 S1–S6](../notes/theory/2026-10-24-cooccurrence-source-recipes.md)では、有限の型付き signature graph の辺に極性を付ける。Function の二入力では反転、二出力では維持し、入力 root と有限経路語で元の位置を識別する。共変位置の集合が一致する変数をまとめ、出力位置に対応する元の入力経路を有限 recognizer として残す。regular な再帰経路を全展開する必要はない。

実際の output entry では、そこから生成した recipe と lexical な受領環境を合わせ、元の入力位置・変数・receipt・receiver・経路の組を捕捉する。後の通常呼出しが新しい receipt を作っても古い表には混入しない。潜在値を実際に使用した際の有限経路を、この表で照合できる。これは完成済みの対応表を仮定する代わりに、その構成を与える局所結果である。

全 source の型生成・compaction・recursive center・非正則な instance がこの signature graph と対応することは未完である。単射改名の保存を、任意の型代入の保存に読み替えない。

### 5.2 経路をまとめる際に残す情報

同じ非 scope 証拠 w の下で、入力由来の印 T と保護集合 U を持つ複数の代替状態を考える。[join の定理 1–3](../notes/theory/2026-10-24-scoped-weight-join-compatibility.md)は、StampInput・ProtectBody・Release の任意の有限列に対し、次の要約が正確になることを示す。

| 後で観測するもの | 保存に必要十分な情報 |
| --- | --- |
| どれかの代替に一つの指定保護が存在するか | T の共通部分と U の和集合。空の代替集合は別状態 |
| 同じ代替に指定した全保護が存在するか | T が少なく U が多い状態を上位とする順序の極大状態集合 |
| 同じ代替で指定保護の存在と不在を同時に読む | 元の状態間の完全な相関。等しい関係を圧縮して保存することは可能 |

T と U の両方を単に和集合にする操作は、一般には最初の観測さえ保存しない。`ProtectBody(s,u)` が「印 u がないときだけ s を追加する」ためである。この抽象的な不一致を、現コンパイラーの反例とはしない。

上の分類は同じ w 内の観測についての定理であり、別 receipt や route をまとめる許可ではない。§4 の Eligible* は保護の不在も読むため、単独の存在観測用の要約を無検査で適用しない。実際の query、経路選別、重みの表現がどの観測を保存するかを対応付ける必要がある。

[handler 分岐の証明 H1–H5](../notes/theory/2026-10-24-correlated-handler-observation.md)は、このうち候補機械の query と分岐を構成した。各 joint cell で `P_F⇒P` なので、Eligible* は条件に応じ false、true、`¬P`、`¬P_F` のいずれかになる。代替 cell の集合 X には `F_b(X)={c∈X | Eligible*(c)=b}` の真偽両方を適用する。否定は各 cell の内部で評価するため、どちらの filter も X の和集合を保存する。複数 cell の保護 bit を先に和集合にしてから一度だけ判定すると、実際に可能な分岐を落としうる。

## 6. 再開と受領の寿命

保存した evidence と、再開する code の実行 owner は分ける。`b.receiver`、Origin、既存 target、Observe、`B_t` は過去の immutable な値である。

\[
enter(i,u,C)=
\begin{cases}
(u,borrow,C)&Active(u,C),\\
(u',own,C+u')&\text{otherwise, }u'\text{ fresh}.
\end{cases}
\]

borrow の完了は元 owner を終了させない。own の完了は今回確保した u' だけを除く。選択された shallow handler は raw resume で自動再装着しない。転送した未選択 handler は source descriptor に従って再構成する。子の完了後は親の suffix を実行し、raw continuation の root だけが resumer へ返す。

**定理 L1（再開による復活の禁止）。** この候補機械の任意の有限実行において、raw resume だけでは expired receiver の evidence は有効性を取り戻さない。同じ継続を何度使っても、保存した evidence は不変であり、各再開は現在の L を読む。

**証明。** enter の active 分岐はもともと active な点を借りる。inactive 分岐は全既存 support と異なる点を作るので、元 receiver を active にしない。leave は own の現在点だけを除く。普通の新しい Call は新しい receipt を作るが、raw resume は過去の entry を replay しない。その他の metadata transport は既存 identity を保持する。crossing は現在の L へ追加するだけで、resume に L の snapshot を復元する規則はない。これを各 step について確認し、有限長に帰納する。□

この機械は[既存の owner 具体化](../notes/design/2026-10-02-typed-source-owner-realization.md)に従う候補である。「外側へ効果が抜ける」という採用済みの観測条件だけから、suspension の全場合についてこの一意の具体化を導いたとは扱わない。

handler の検索で eligibility が偽なら、その arm を実行せず次の候補へ進む。eligibility が真の arm を実行してから No が返る場合は別の経路である。この間に L や activity が変わりうるので、元の pending request の Origin・route・H を保持し、返却時の current world と Rejoin してから次候補の query を再計算する。候補 owner が変われば、foreign 判定や grant の query も更新する。[H3](../notes/theory/2026-10-24-correlated-handler-observation.md)は、この接続が具体的な後続を含むことを候補の局所 simulation から示す。

## 7. 有限の証明書から安全性へ

値の packet と実際の event を別の事実 `V(p,s),E(p,s)` にする。ここで s は同じ入力 tuple の有限 joint cell であり、receiver の等号、現在の activity、保護・許可、必要な経路観測を併せ持つ。未知の相関を都合のよい真偽に固定しない。

[simulation 稿](../notes/theory/2026-10-24-corrected-machine-simulation.md)は、隠れた witness の region を分割し、選択的な解除を行い、後の再観測で未知の二項関係を安全に再抽象化する構成を与える。二つの区別できない witness の片方だけを解除するとき、region 全体を解除済みにする transfer は不正である。source 到達性を未証明のまま、この情報損失例をコンパイラーの反例とは呼ばない。

各有限 graph G の証明書 U は、seed と全 mandatory edge の閉包

\[
F_G(U)\subseteq U
\]

および各出力で `U_E⊆Φ` を満たす。これは F に関する **pre-fixed point** の条件である。操作稿で同じ包含を post-fixed と呼ぶ箇所は、包含の式を優先して読む。閉包には body、adapter、失敗する試行、現在状態での No 再検索、latent/reentry、七種の capture frame を含める。

**証明の合成。** 実際の初期 packet は seed に入る。一段の具体出力は対応する transfer の出力集合に入り、閉包条件で次の port に入る。有限 capture の frame 列は cut grammar に帰納的な導出を持ち、その単調 summary に含まれる。これを現在の応答・ambient world ごとに適用し、有限実行長に帰納する。最外 request は `U_E⊆Φ` により契約内にある。空の Φ から request は出ない。

この合成には、**各構文から生成する edge が、その具体操作について証明された transfer を使用すること**が必要である。次節は候補の生成算法 Gen(d) についてこの対応を構成する。現存する任意の小さい型導出や旧 graph に、有限な保守的 transfer の存在だけから同じ結論を移すことはできない。自然な推論の完全性も別の命題である。

[H4–H5](../notes/theory/2026-10-24-correlated-handler-observation.md)では、真偽両 filter・action・Rejoin で構成する有限 relation graph の閉包が、その graph 自身の全有限経路の像と一致することを示した。具体的な実行に対して得るのは successor の包含である。Refresh が余分な cell を残す場合もあるので、閉包の全経路が実際に実行できるとは主張しない。名前解決済み核の生成対応は次節の対象であり、全表層や実 compiler の生成対応とは区別する。

### 7.1 source から graph を生成する

[生成証明 G1–G5](../notes/theory/2026-10-24-source-core-action-coverage.md)は、有限な source 導出 d を辿り、各命令に通常値・request・failure の出口を作る。再帰は登録済み code label への辺にし、実行を先回りして展開しない。対象は13式、11 pattern、Let/Expr/Module、順序付き root、有限の直接境界・選択証拠である。辞書の eapp は body の効果を保持し、新しい source receipt を作らない。

証明は三つの帰納法を使う。source/証拠の有限導出木から命令と接続を作り、管理遷移の場合分けで実際の後続の位置を示し、捕捉された七種の frame 列から継続の summary を構成する。これで「必要な action edge が存在する」という H5 の前提を、この Gen(d) について導出する。No は現在の world で再検索し、Fail は失敗出口へ進む。arm の body が返した後には、その導出が指定する結果 adapter を実行し、正常に返って初めて Yes を作る。adapter の request・failure も同じ生成規則で保持する。

**失敗の吸収。** この核では、active context が `E[Fail r]` になれば、各 frame は同じ r を外へ伝えるだけである。未実行の suffix、handler の次 arm、Resume は起動しない。frame 数の帰納法で最外の Fail へ至る。

そこで失敗専用の有限表示では reason tag だけを残し、以後読み取られない world を全て忘れる。通常の計算と No/resume では従来の完全な joint cell を使う。これは失敗時の owner cleanup を新たに決める操作ではなく、以後の観測がないことに基づく抽象化である。失敗後の内部 world を読む host の契約や具体的 cleanup は別に残る。

有限 interface と外部コードの導入契約の下で、追加した failure port を含む graph の閉包は全有限実行 prefix を含む。実行型保存・Bad 排除は独立の値型定理を必要とする。全表層の展開、nonregular instance の有限表示、候補政策の採用、旧証明書の保存はこの結論に含まれない。査読状態と固定版は[生成証明の outcome](../tasks/agent-loop/sprints/source-core-coverage-20261024-outcome.md)に記録する。

## 8. 全表層への接続と未完了箇所

静的 Yumark については、文書・文字列・paragraph・emphasis・strong・heading・section-close・list・item・item-body・code-fence・quote の全 node を列挙し、型付き builder を構成した。[証明 Y1–Y6](../notes/theory/2026-10-24-surface-elaboration-closure.md)が、外殻の中身を未指定とする前提を取り除く。

次の義務は引き続き全体目標の一部である。

| 義務 | 完了に必要なもの |
| --- | --- |
| 生成 graph の適用範囲 | Gen(d) の候補構成を各 finite interface・実 frontend・元の導出へ接続。失敗後の完全状態を観測する契約は別途確定 |
| 共起による集約と保護・解除 | 同じ共変位置の判定、provenance を保つ集約、生成・一般化・使用・解除への対応。追加の入力選択を求めない |
| non-Var/anonymous の受領 owner、wildcard policy | 候補の全期待挙動との照合と、実際に未決定な具体化の切り分け |
| Yumark interpolation/commands、module/use/realm/band、error/act-copy/derive | 全生成規則と型・効果を保つ展開。未対応の実装を仕様上の禁止へ転用しない |
| dot selection | compact/raw、snapshot/SCC 公開、一意性・完全性。有限証拠の code 構成から自動的には出ない |
| Simple-sub | 生成・蓄積・伝播・level・extrusion・intrusion・一般化の元の A/B、主型性、停止性 |
| 全証明の確定 | 適用する元の範囲での独立査読。局所定理の査読を全体の承認へ広げない |

実装を今回の範囲から外しても、この表の意味論と数学上の義務は残る。「実装以外は完成」と呼ぶには、この表を証明・反駁・明示的な仕様決定で解消する必要がある。
