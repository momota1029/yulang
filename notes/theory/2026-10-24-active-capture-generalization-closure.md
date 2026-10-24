# ActiveCapture の一般化: 完了条件と原命題への適用判定

2026-10-24。ORIGINAL-CALL-ACTIVE-WALK-20261024/r1、著者 `/root`。Baseline `9cc452b357117e51161a74b94c756de364d6e3d7`。本稿は閉包を検査する稿であり、未導出の J_rec/J_pub を成立済みとしない。

## 1. 今回閉じるべき元の判断

元の [source 保存命題](2026-10-13-intrusion-source-preservation-proof.md) は、実 Value SCC で資格を得た extrusion の等置について、元の source scope、全共同 evidence、一般化と正当な複数 use、外部結論を保つことを要求する。型付き核の安全性、局所解の diagonal extension、SCC 計算の正しさだけではこの主張は出ない。

具体的対象は前稿と同じである。

```text
let rec f = lambda x.
  let g = lambda y. (lambda z.y)(f y)
  in {a=succ(g 0), b=g true}
in f
```

[構成済み registry](2026-10-24-original-recursive-formation-construction.md) は次を与える。

```text
ActiveCapture(p_g(h), use_f, K_f, r_f, FullRelation(K_f), scope_map)
```

この行は実 r_f とその全関係への参照を保持する。`FullRelation` の意味や dependency field を捨てた型略記ではない。一方、参照が存在することは、その対象が completed membership certificate であることも、その全 field が一般化可能であることも意味しない。

## 2. 元の walk を実際に適用するときの判断列

[Source-Generalize](2026-10-08-source-generalize-definition-and-proof.md) §3.3・§5.1–5.3 に従う。p_g の validating component を C_g、外側の recursive registration を C_f とする。SCC の F≈G から C_f=C_g を導かない。

| 対象 field | owning constructor から得た扱い | 適用結果 |
| --- | --- | --- |
| actual r_f、r_g(h)、closure allocation | operational identity / actual allocation | 元の同じ identity を固定し、new use で再実行しない |
| 元の source declaration、slot、解決済み Name | Intrinsic / Resolve | 同じ宣言・参照を保持する |
| actual y、response、current world、raw continuation | 実 entry/response の EventField と original telescope | その実 event 内に保持し、publication の外へ量化移動しない |
| g の ordinary parameter description A | Parameter が導入する Desc(C_g,q_y,…) | retain の対象。eligible かどうかは全 fix walk の終了後に判定する |
| g の latent checking proof | 実 owning rule の ViewLogic/EventProof/Check | original scope と依存を保持する。実行済み dictionary と同一視しない |
| ActiveCapture の FullRelation(K_f) | source-owned reference object は構成済み | **その全 field の分類・action が必要**。R5 の同根性だけでは retain/fix の全遷移は出ない |

最後の行が、元の walk を機械的に最後まで適用できない位置である。f は構成中なので完成済み external `Mono/Established` certificate を入力としては持たない。`Live(C_f,r_f)` という出自は保存するが、それを `Internal(C_g,r_f)` に変えて rule3 を適用してはならない。C_f の全関係を参照し続けるとき、C_g の bound/free description、Shared、actual EventField と latent EventProof の incidences がどこへ写るかを示す必要がある。

元の walk が、既に型付きの登録済み field graph を入力とすれば有限であることは既存定理の範囲である。今回不足するのは探索算法ではなく、この ActiveCapture に対する入力 graph/action の原規則との一致である。

### WA1（完全な型付き graph を得た後の判定）

§5.1 の全 node/edge と binder incidences が構成済みの有限 graph N を仮定する。`Fix_N(p)` を、元の fix seeds と fix 遷移から到達する自由 Desc 宣言の集合とする。すると A を p_g で template 化できるための条件は、A が retained な `Desc(C_g,q_y,…)` で、`A∉Fix_N(p_g)` である。

**証明。** これは eligible の定義を、実 field graph 上の到達可能性として展開したものである。初期 seeds は §5.1 rule1。Established/Intrinsic/OneShot の全自由依存を辿る rule2、own-component Internal の rule3、元の Shared/ViewLogic/EventProof telescope を扱う rule4 を固定点まで適用する。既に訪れた登録 graph edge を再展開しないので有限。到達した自由 A は固定 mark を得て、retain edge がその mark を解除する規則はない。到達しない、かつ retained な own Desc は rule5 で eligible になる。bound な Family/Published の parameter は、その binder の下のまま保持され自由依存として辿られない。従って同じ字面 A の出現数ではなく、元の binder incidence が判定を決める。□

WA1 は新しい一般化規則ではなく、既存規則の適用条件をそのまま露出した判定である。N の未提供 field を省けば別の graph の到達可能性を計算したことになり、J_pub は出ない。

### WA2（同根性・表示型だけから eligible は出ない）

R5 の raw root と full-relation **参照**の共有、および表示された F:U→V に A がないことから、`A∉Fix_N(p_g)` は導けない。

**証明。** R5 は参照を共有するという性質であり、その参照先の field 分類についての主張ではない。元の record 語彙で、固定された contract field が自由 Desc A に依存する場合には rule2 が A を mark する。一方、その座標が独立に型付いた `Family(∀β.R(β))` の内部 parameter で、自由 anchor に A がなければ、同じ rule2 はその bound β を外へ出さない。両方とも raw provider の identity と表示された U→V を変えずに記述できる。従ってそれらのデータ事実だけでは、どちらの walk が actual source に対応するかは決まらない。これは R5 からの含意がないことを示す例であり、actual f に新しい guard/Family を追加したり、二つの言語仕様を選択したりするものではない。□

実 source に対しては一つの original field graph を構成して検査すればよい。新しい `∀A` を先に置いてから「A は bound なので一般化できる」と結論する手順は、その binder introduction 自体を証明していなければ循環である。

## 3. 今回の whole-carrier action を元の残項へ戻す

[Call/admission 構成](2026-10-24-original-call-admission-construction.md) CA1 は `I_A=I_U∧Ret_A` から I_U への同一 tuple 上の射影を与える。CA2 と同稿 §8 は、今回構成する witness の I_U を original `Comp(empty,U)` の full policy に選ぶ場合、NameDelay の原点・inert license・全 Force/future を保って q_fy の入力を構成する。固定された別の inlet を上書きせず、admitted carrier を NameDelay の source image に制限しない。

この局所作用は original current-world/y certificate を入力として使う。未完成の S.W/S.V を完成済み νΦ certificate とみなす規則は含まない。従って、それを R4 に代入したときに閉じるのは inlet action の構成であり、全 `S⊆Φ(S)` ではない。

特に、次の推論はまだ使用できない。

```text
(F*,v_f,r_f,e) ∈ S.V
----------------------------------  [この規則はない]
全 raw ExecuteCallable(v_f,…) observation ∈ P_F*[S]
```

S は任意の候補集合であり、要素であることだけでは Φ の全 observation/guard clauses を満たす証拠を持たない。完成済み νΦ の elimination と異なる。必要なのは actual f/g/wrapper の配置と全 phase を使った joint one-step proof である。候補集合の定義に desired output correctness を追加しても、その集合が actual 全 observations を含むことが別義務として残る。

これを閉じるための exact judgment は、同じ actual contexts/histories と deterministic source witness strategy に対する

```text
S.V ⊆ Φ_V(S), S.W ⊆ Φ_W(S),
S.T ⊆ Φ_T(S), S.Car ⊆ Φ_Car(S)
```

の同時導出である。source input の projection、registration、finite-prefix ごとの別 witness は、この結論の代用にならない。現在の二稿はこれを証明済みと報告しない。

## 4. 固定 intersection による別の閉包経路の検査

g の二 use だけを証明するため、同じ actual g に対し固定した二 complete views `F_Int∧F_Bool` を構成する案もある。既存 §3.2 の same-value intersection は、両 complete certificates が同じ provider/world 上にあれば適用できる。この場合、A の generalization eligibility を通らずに二つの固定 view を使える可能性がある。

ただし、これは今得た証明ではない。原 admissible domain の全 actual observations に対し両 view を構成する必要がある。一つの Parameter Desc に Int と Bool の異なる assignment を別々に与えて結合してはならない。広い U→U の表示だけから result correlation も出ない。途中の f y を捨てず、actual y が Return されることと全 pending suffix を元の complete relation で証明する必要がある。

従って fixed-intersection 経路も上の joint one-step proof を迂回しない。成功した場合には source witness を元の native shared-C history と比較できるが、その前に元の required coverage を REFUTED としてはならない。

## 5. 完了判定

| 元の義務 | 今回の判定 |
| --- | --- |
| SCC と実 parent/copy 資格、局所 extrusion/等置 | 前回の査読範囲で閉じている |
| full carrier refinement / NameDelay 入力 action | 今回、明記した original policy と world/value premises の下で構成 |
| original joint recursive member/world J_rec | 全 one-step clauses の証明が未完 |
| active capture の original Generalize J_pub | full typed field action と WA1 の実適用が未完 |
| 元の source-qualified coverage 反例 | J_rec/J_pub または固定 views の完全 witness が未導出なので未成立 |
| 全言語の健全性・主型性・combined inference 停止 | 未完。上の局所結果から自動的に閉じない |

原命題を成立済みに変更する根拠は得ていない。「あと一息」という作業量の見積りも裏付けられていない。未解決を別の theorem premise に移して全体を閉じたとはしない。今後の直接対象は全 one-step derivation と actual field action であり、registry や SCC の再調査ではない。

本稿は static source/definition 読解と紙上の適用判定。実装、テスト、compiler/build は変更・実行していない。依存は sprint contract の固定23入力、および今回の Call/admission 稿の凍結 SHA-256 `c3aff32c3f966526019abd49d389b140b27614be120cc3280b4728545c65c2ee`。独立査読の固定 hash と判定は sprint outcome に記録する。
