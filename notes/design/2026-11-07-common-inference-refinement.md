# 共通推論の高速化と、参照実装からの refinement

状態: **Draft。内部の実装置換計画。高速化の実装・正当性証明・性能測定は未実施。**
日付: 2026-11-07。
対象: 現在の共通 carrier の全 instance 契約を維持する bounds 伝播と、今後の B 段階への接続。

## 1. 目的と根拠

[bounds 伝播の着想](../ideas/2026-11-07-fast-propagation-idea.md)にある「上界・下界をまとめる」操作を、
意味を変えずに実装できる単位へ分ける。採る内部方針は、**有向制約を残したまま伝播する情報を共有し、
将来の Lean 関数を現在の独立モデル集合に対して検証する**ことである。
速度の目標値や Simple-sub との優劣は、この方針からは結論しない。

既存の [Rust oracle 計画 §6](2026-11-06-rust-oracle-plan.md#6-推論の性能設計)は、
cache、let 選言、疎な worklist、行判定、scheme 共有、計測を分けている。
本書はそのうち共通 solver の置換契約を具体化する。既存の性能記録を新実装の測定値として再掲しない。
言語仕様の根拠は [型の要求順序・値制限](../../spec/04-types.md)と
[effect・handler](../../spec/05-effects.md)。ここで新しい一般化規則や近似による型付け規則は決めない。

## 2. 現在の参照実装が保証するもの

実装は [CommonSolvedSource](../../lean/Yulang/CommonSolvedSource.lean) の
`inferSource` → `solveClause` → [CommonBoundRefSolver.solveAll](../../lean/Yulang/CommonBoundRefSolver.lean)
→ [CommonBoundRefWorklist.run](../../lean/Yulang/CommonBoundRefWorklist.lean) を通る。
生成した formula の有限 clause 列を pack/compile し、有限の symbolic branch と row/clamped family を返す。
具体型 parameter を先に選んでから inspector を呼ぶ算法ではない。

元 clause の slot 数を `m`、元 compiled graph を `G = compile a` とする。
`rows : Fin m → Common.Row` と `values : Fin G.size → Common.Ty` は独立した任意の割当てである。
`G.Models rows values` は元 constructor 方程式・型比較辺・行制約の充足であり、solver 成功や cache の性質を含まない。
実際に生成された任意の clause に対する `generated_models_exact` は次の形を持つ。

```text
G.Models rows values
  ↔ ∃ S ∈ solveAll G, ∃ rowParameters, ∃ valueParameters,
      S.instantiateRows rowParameters = rows
      ∧ ∀ i, S.instantiateValues rowParameters valueParameters i ≈ values i
```

`≈` は [Common.Equivalent](../../lean/Yulang/Common.lean) の要求同値である。
全展開深さ・負位置の rank を量化する意味を保ち、元の全 compiled node を回収する。
`all_parameter_sound` はさらに、任意の実返却 `S` と**任意の**行・型 parameter について元の `Models` を結論する。
[CommonClampedRowFamily](../../lean/Yulang/CommonClampedRowFamily.lean) と source scheme の parameter は、
有限 ID から行・型への普通の関数の積であり、`Models`、`ResidualHolds`、support、fuel、成功証拠を条件に持たない。
`Scheme.parameters_nonempty` により parameter 領域の空性を利用した全称健全性でもない。

この完全性の入力は実 `compile a` である。`solveAll` が読む `origin` と graph 本体を独立に作った
手書き `Compiled` 全体へ契約を広げない。参照実装のこの境界は置換先でも明示する。

`run_bound` の `(5N+3)²` は、一つの返却 branch の inspection trace 長の上界である。
branch 総数、集合操作・到達計算・生成の費用、scheme の大きさを含む実行時間の上界ではない。
有限停止の証明から、入力サイズに対する線形時間や二乗時間を主張しない。

## 3. `α ≤ β`、等号、強連結成分を分ける

`α ≤ β` は、α が満たすべき要求を β から受け取り、α の下限を β へ流す有向辺である。
[LayerBoundTemplates](../../lean/Yulang/LayerBoundTemplates.lean) は lower/upper/flow/check を分け、
flow の到達関係を使って lower/upper を集めている。

| 入った情報 | 必要な伝播 | その情報だけからは導けないこと |
| --- | --- | --- |
| `α ≤ β` と `L ≤ α` | `L ≤ β` | `β ≤ α` |
| `α ≤ β` と `β ≤ U` | `α ≤ U` | `U ≤ β` |
| `L ≤ x` と `x ≤ U` | rigid 比較 `L ≤ U` の検査・分解 | `x = L`、`x = U` |
| `α ≤ β` と `β ≤ α` | `α ≈ β` | 型構文の文字どおりの等号、異なる binder/nominal identity の消去 |

例えば `α := int`、`β := int | str` は `α ≤ β` のモデルである。
両変数を一つにすると、この割当てを回収できない。`int | str` を `any` と同一視する理由もない。
bound の向きは arrow の分解で反転するため、ordered pair の左右を交換可能な key として扱わない。

有向 variable-flow graph の強連結成分（各点から互いへ到達できる集合）では、推移律から要求同値を得られる。
明示的な等式や、このように証明された相互比較の代表管理には union-find を使う余地がある。
有向包含の伝播と、同値な点の代表管理を別の責務にする。ただし、代表化の正当性には次も必要である。

- 元 ID から代表への写像と、全元 ID への readout を残す。
- constructor の子、正負の出現、外側 mask と各 query を同じ写像で移す。
- 任意の元モデルを要求同値まで回収し、任意の代表側 parameter の具体化を元モデルへ戻す。
- scope・capture・一般化の可否・rigid な識別子を代表の値だけから推測し直さない。

現在の [CommonBoundRefSolver.models_congr](../../lean/Yulang/CommonBoundRefSolver.lean) は、
同じ行の下で全 node の要求同値により元 `Models` が不変であることを示す。
これは代表化の意味側の部品であり、SCC 算法、metadata の更新、全 instance 回収の証明そのものではない。
将来 role/nominal を持つ graph に広げる場合は、その義務を含むモデルで改めて置換保存を示す。

## 4. bound 集合の共有は、変数の同一視ではない

最初の実装候補は、変数の ID と有向辺を保ち、下限・上限の**表現**を不変 DAG や持続的な集合で共有する方法である。
たとえば β の下限を「α から来る部分と、β 固有の部分の和」として表現できる。
β 固有の下限が増えても、それを α の下限へ逆流させてはならない。
これは集合和を共有する仕事であり、α と β を一つの型 parameter にする仕事ではない。

同じ境界集合を現在持つ二変数も、将来の更新先が別なら別の変数である。
共有する不変 node と、各変数からその node への参照・差分を分ける。
可変集合を偶然共有して一方への追加が他方にも入る実装は、対応する flow がある場合に限って正当化できる。
hash-consing では、同じ構文の子 ID・捕捉先・行式・mask/query を key に含める。
形だけが似た graph や、違う具体化の fresh slot は同じ key にならない。

worklist の候補は、新しく増えた edge/bound と、その影響を受ける隣接関係だけを処理する形である。
一度処理した `L ≤ U` 自体を重複登録しないことと、後から増えた下限と既存上限の新しい組合せを処理することは両立させる。
query の追加、whole default の分解、下限・上限の伝播が新しい義務を発生させる点も対象とする。
queue 順序の変更や遅延生成の後でも、停止時に必要な全 rigid 比較が分解済みであることを内部で証明する。

現在の [有限 query inventory](../../lean/Yulang/CommonOptionalPoolQueries.lean)と
[bound-reference inventory](../../lean/Yulang/CommonBoundRefCoalescing.lean)は、
遅延して作る node/edge の有限支持を証明する基準として使える。
既存の finite universe を実行時に先に全列挙する必要はないが、必要な要素の欠落を許すものではない。
branch ごとに異なる制約・選択を共有 cache で混ぜず、更新に依存する結果にはその依存と無効化条件を持たせる。

## 5. row/effect への接点と残る意味

[RowFlowSchemes](../../lean/Yulang/RowFlowSchemes.lean) の現在の制約は、変数・空行・join からなり、
右辺が変数または空行である場合を解く。下限の伝播、到達関係、共有 join の表現は型側と共通の候補になる。
`Common.Row` は occurrence の集合であり、互いの包含が成り立つ行は外延的に等しい。
行の代表化でも元 slot への復元は必要で、§2 の結果行の**等号**を相互包含だけへ弱めない。

最小解を一つ返すだけでは全 instance にならない。
例えば `r₀ ⊆ r₁` には両方空の最小解があるが、非空の `r₀/r₁` を含む多くの解がある。
自由な二つの行 parameter `p₀/p₁` を使う

```text
r₀ = p₀
r₁ = p₀ ∪ p₁
```

は全 parameter で制約を満たし、任意の `r₀ ⊆ r₁` は `p₀ := r₀`、`p₁ := r₁` で回収できる。
`RowFlowSchemes.solve_models_exact` と共通 family の `build_retract` は、このように共有を残した全解の契約を持つ。
型でも一つの最小型だけを返して、負位置を含む全 parameter family の代わりにはしない。

現在の row-flow solver には、operation head、protect/release、handler 境界の変換は入っていない。
それらには [Directed](../../lean/Yulang/Directed.lean)、[RowInference](../../lean/Yulang/RowInference.lean)、
[CoreEffectTyping](../../lean/Yulang/CoreEffectTyping.lean) の別の意味と規則がある。
将来は変換を辺のラベルや専用 node として保持し、各変換と包含の保存を示した範囲で同じ伝播基盤を使う。
operation key・境界の scope・符号付き weight・mask・非 capture を普通の無ラベル flow へ消さない。

とくに handler の operation-local 型は、呼出し側の存在的な選択と、handler 本体での全称的な検査が異なる。
`CoreEffectTyping` の multi/partial handler 規則は局所型割当てを全称量化する。
その binder を「解きやすい一つの型」へ具体化したり、外側の推論変数と union-find で結合したりしない。
handler 全称を扱う新しい constraint/solver 契約が閉じるまでは、M1 の存在的 clause solver がそのまま解くとは主張しない。

## 6. 将来の Lean 関数に要求する正確な refinement

以下は**今後証明する契約**であり、既存の theorem 宣言名ではない。
将来の `fastSolveAll` は有限入力から停止して有限 scheme 表現を計算する Lean 関数とする。
その parameter は無制約の有限 ID 割当てを維持する。
内部 node 数や parameter 数が変わる場合も、元 `G` の型・行 ID を読む readout を明示する。

`Instances(F, rows, values)` を、有限 scheme 列 `F` のいずれかと自由 parameter によって
`rows` を等号で、`values` の全 node を要求同値で回収できることとする。
実生成の任意の `a`、その `G = compile a`、任意独立 `rows/values` に対する主契約は次の二つである。

```text
G.Models rows values ↔ Instances(fastSolveAll G, rows, values)

∀ S ∈ fastSolveAll G, ∀ rowParameters, ∀ valueParameters,
  G.Models (readRows S rowParameters)
           (readValues S rowParameters valueParameters)
```

第一式から参照 family との
`Instances(fastSolveAll G, rows, values) ↔ Instances(solveAll G, rows, values)` を導く。
第二式は「回収に成功した代入だけ」でなく、返したすべての scheme のすべての自由代入を扱う。
成功・closed cache・fuel・`Models`・`ResidualHolds` を parameter の制限に移さない。
型の比較のために、有限深さの観測や具体化後の profile を公開前提に加えない。

scheme 列の並び順・重複・branch 数・parameter arity が参照実装と等しいことは要求しない。
同じ arity の全単射だけに対応を制限せず、必要なら両方向に別の branch と parameter を回収する。
選言を DAG として共有する場合は、その有限展開と instance の和が一致することを証明する。
branch を捨てる変更にはその全 instance の包含証明が必要であり、一つの成功 branch や最小代入の保存では足りない。
公開 API が List を返す間は、その列の materialization も費用に含める。
DAG を直接返す API へ変更する場合は、有限の分岐意味と instance 操作の対応を別に証明する。

最初は worklist・bound 表現だけを置き換え、既存の row/clamped family と source 出力 readout を再利用する。
row solver、scheme 具体化、branch 共有も変更する場合は、それぞれの全モデル回収を分けて証明する。
局所 step の表現不変条件だけでは停止時の閉性は出ないため、停止・全義務の処理・任意 parameter 健全性を接続する。
この合成により source 側の主型性、全 parameter の型付け、拒否 iff を回収する。

## 7. B 段階では生成と求解を別々に保つ

各段階は、独立した constructor 型判断、生成/lowering の exactness、solver の exactness を別の成果物にする。
生成がどの構文不変条件を保証するかを明記し、その条件は実生成から内部供給する。
solver の成功や fuel を型判断側の前提にしない。

現段階の接続先は [Core.CommonSyntax](../../lean/Yulang/CoreCommonSyntax.lean) と
[CommonSolvedCoreSyntax](../../lean/Yulang/CommonSolvedCoreSyntax.lean) である。
後者の `principal` / `all_parameter_sound` は実 finite source solver との合成になっている。
公開 `Core.infer` をこの経路へつなぐ際も、独立判断の範囲を同じように表示する。
現 `Signature.empty` では literal の int/str/bool/unit、構造的 data、strict application、
singleton unguarded bind-pattern case、leaf が presence 構文の内部へ再帰的に接続される。
float、nil/cons・nominal data、一般 case、effect/handler、role/method、nominal/cast 全体の接続を含めない。

| 段階 | 生成・lowering 側に保持する意味 | solver 置換で別に示すこと |
| --- | --- | --- |
| B1 literal/data | literal 内容と基底型の対応、構造的 data の constructor、評価行、値制限 | 既存 graph へ正確に下ろせる範囲では §6 を再利用。nominal list を pair/variant の都合へ変更しない |
| B2 case/pattern | 名前のスコープ、bind の単相性、guard/default の評価と行、順序・coverage | singleton name の既存 lowering と、未接続の複数 arm/scoped pattern を分ける。必要な選言・presence 制約を保持 |
| B3 effect/handler | request の署名、境界変換、継続、operation-local 全称、非 escape | 変換つき行制約と全称を含む独立意味に対する全解契約。M1 の row-flow completeness で代用しない |
| B4 role/method | qualified 義務・辞書・可視性、曖昧性、一般化と module 終端の保留 | 型の bounds が同じでも義務や evidence を削らない。追加義務を含むモデル・export の保存を示す |
| B5 nominal/cast | nominal identity、不変型引数、構築位置の保留境界、cast の方向 | identity と不変制約を保つ表現変換。構造的な要求同値だけで別 nominal を統合しない |
| B6 その他の Core 構文 | 各構成子の既存規則と翻訳の対応、strictApp の行、leaf の範囲、名前解決 | 未接続を fallback literal へ通さない。新規規則なしに既存の拒否を言語全体の型付け不能へ拡大しない |

この分離なら、新構文を同じ constraint 意味へ下ろせる限り solver refinement を使い回せる。
制約の語彙や量化子を増やす段階では、拡張した意味に対する solver theorem を追加する。
生成 theorem を `Formula.Holds` の別名にした新 `Typing` で閉じる方法は採らない。

## 8. 共有と簡約で保持する情報

表現の圧縮が触れる情報は、次を一まとまりとして検査する。

| 情報 | 保持する条件 |
| --- | --- |
| 型 parameter の正負 | arrow domain の向きと、正負両方に現れる同じ ID を保持する。正だけの変数を bottom にする等の pass は、その family 保存 theorem の対象内で使う |
| level・capture・weak | level は binder/escape 情報の実装候補。一般化できる slot、捕捉した slot、固定された弱い slot の区別を保つ。代表を選ぶ順序だけで一般化範囲を変えない |
| scheme の具体化 | 同じ具体化の内部では共有、別々の一般化 slot の具体化は fresh、捕捉 slot は元環境と共有。signature が固定する行も勝手に fresh にしない |
| whole default・mask・presence | 同じ元 ID から見た field/optional/presence の整合性を保つ。外側 mask は現在の record 層に作用し、payload へ無条件に伝播しない。hidden head の要求を tail へ再導入しない |
| regular graph | 全有限展開による意味を保ち、観測深さを実装 budget へ置き換えない。子の guarded 展開と同深さ tail/default を区別する |
| rigid・handler 全称 | 普通の存在的 parameter と別の binder 身分を保つ。局所型の非 escape と全称検査を cache/代表化で失わない |

[共通モデルの設計](2026-11-07-m1-common-model.md)の共有 profile、同深さの上限 clamp、
[一般化](../../lean/Yulang/QualifiedGeneralization.lean)の捕捉境界を参照する。
これらの義務を、公開 parameter に意味的条件を加える方法で補わない。

## 9. 内部選択、代案、速度を主張するための残作業

採る順序は、有向 edge と共有 ID を維持した bound 表現の共有から始め、
元モデル集合に対する Lean の置換定理を閉じ、その後で具体的な費用を評価する順序である。
理由は、現在の全解定理を proof boundary として残せ、生成側の B 拡張と衝突する範囲を小さくできることにある。

| 代案 | この段階で採らない理由・採れる条件 |
| --- | --- |
| すべての `α ≤ β` を union-find で結合 | 片方向のモデルを失う。相互到達などから要求同値が示され、共有・scope・readout の保存も閉じた場合だけ代表化の候補にする |
| 全 bound 集合・全 closure を先に展開 | 参照実装として見通しはよいが、同じ情報の走査・複製が減る保証はない。比較用の基準として保持する |
| 最小の型・行代入だけを返す | 任意の自由 parameter と全独立モデルを回収する契約を満たさない |
| 一つ成功した branch で探索を終える | 型付け可能性の証人にはなるが、有限 scheme の和としての全 instance を失いうる |
| Rust の速い実装だけを作り、例で一致を調べる | 差分試験は有用だが全量化の refinement ではない。Lean 関数と保存定理を先に境界に置く |

正当性の refinement と速度の主張は別の定理・測定である。
将来は source/constraint/node/query/branch/返却 scheme の大きさを入力・出力量として記録し、
集合の membership/union、隣接走査、ordered pair の処理、hash key 比較、node/edge の割当て、
row 変換・比較、具体化・readout の各費用を明示する。
可変長の型・行全体の等号比較を定数時間として数えない。
不変 DAG の共有による allocation 減少と、遅延した境界を読む回数の増減も分ける。

将来の計数付き Lean 関数は、計数を忘れると候補算法と同じ値を返すことを示し、
その費用モデルの範囲で上界を証明する。具体実装の計測は
[oracle 計画 §6.6](2026-11-06-rust-oracle-plan.md#66-最初の-benchmark-と計測条件)と
[performance policy](../../rules/performance.md)に従い、固定入力・baseline/candidate・build 条件・時間・memory・work counter を記録する。
branch 数や出力が増える場合も計測対象に含める。
意味の一致だけから高速化を達成したとは言わず、数例の速さだけから全入力の計算量改善とも言わない。

本書の追加に伴う solver/code の変更、benchmark、速度に関する新しい theorem はない。
残っているのは内部表現・証明・費用モデルの選択であり、`notes/questions/` へ新しい言語仕様の問いは追加しない。
