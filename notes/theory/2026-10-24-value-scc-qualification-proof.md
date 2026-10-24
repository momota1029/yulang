# Value SCC、extrusion occurrence、intrusion 等置の証明

2026-10-24。EXTRUSION-INTRUSION-SCC-20261024/r2。著者 `/root`。
Baseline `3ca3a9867a9fdc20841b983d047192ca7de9b672`。独立査読で S1–S7/E1 の記載範囲を受理。E1 の empty memo 前提の MINOR 指摘を反映した。[固定版・査読記録](../../tasks/agent-loop/sprints/extrusion-intrusion-scc-20261024-outcome.md)を参照。

本稿は、承認された参照から SCC を作り、実 extrusion の等置対象を選び、有限な等置を処理する部分を証明する。元の [source 保存命題](2026-10-13-intrusion-source-preservation-proof.md) §1・§5 の lexical scope、一般化、共同 witness、完全 Call、required coverage は保持する。SCC が等しいという事実から、それらの保存を結論する規則は追加しない。

## 1. 対象と生成

`V` は名前解決済みの値 identity、`T` は型変数 identity とする。両者は別の集合である。`G=(V,Ref)` の辺は [承認された Value 参照](../design/2026-10-10-parent-copy-scc-intrusion.md) だけから作る。`a <: b`、型変数の bound、parent/copy link、FreshUse は Ref の生成規則ではない。

有限の source occurrence tree と名前解決写像 `res(n)` を固定する。definition root `d` の initializer/body を owner=d で走査する。通常の子式には同じ owner を渡し、nested definition `b=e` の initializer には owner=b を渡す。その宣言を含む block の残りは元の owner のままとする。Name occurrence n を訪れたときだけ `owner(n) → res(n)` を加える。Lambda の形式引数や型 level によって definition owner を変更しない。未解決 Name から辺を捏造しない。

Apply-result の参照は別に作る。承認済みの再帰的 Name/Apply fragment では

```text
Names(Name n) = {res(n)}
Names(Apply e1 e2) = Names(e1) ∪ Names(e2)
Names(literal) = ∅
R_Apply → v  iff  v ∈ Names(Apply e1 e2).
```

この式で Lambda、Block、Group などを無条件に透過させない。それぞれに承認された fragment membership が必要である。definition-root の走査と Apply-fragment の走査は異なる規則である。以下 S1 の Apply 部分は上の閉じた fragment、または独立に正当化された child relation に対して適用する。全 frontend constructor の membership をここで選択しない。

### S1（source incidence と圧縮表示）

上の owner 走査が生成する辺は、各 definition の source-owned initializer/body にある解決済み Name への辺に正確に等しい。Apply fragment の木を共有補助頂点で表示しても、元の Value 間の到達可能性と SCC は保存される。

**証明。** owner 走査の work item `(e,d)` に「e は現在 d に所属する」を不変条件とする。通常の子は所属を変えず、nested initializer だけが宣言 root へ移るので、source tree の深さへの帰納により各訪問の owner が一致する。Name case は実際の resolved target だけを追加し、それ以外の case は辺を追加しない。逆に任意の所属 Name は有限木の子訪問で到達され、その一辺が追加される。重複辺は関係として同一視できる。

fragment 表示では各 fragment occurrence e に新しい非 Value 頂点 `h_e` を置く。Apply result からその `h_e` へ、親 fragment から許可された子の `h_child` へ、Name fragment から `res(n)` へ辺を置く。内部 helper は source の真部分木へ進むので有限 DAG である。helper だけを内部に持つ `R_Apply → … → v` の道を末尾から反転すれば、ちょうど Names に含まれる一つの Name が得られる。逆に Names の導出を辿ればその道が得られる。

一般に各 semantic-to-semantic edge がこのような helper path に展開され、各 helper-only path が一つの承認済み incidence に縮約されるなら、任意の有限道を semantic vertex ごとに分割して展開・縮約できる。従って元 Value 間の到達可能性は両方向に保存される。相互到達可能性も保存される。helper を新しい source Value と解釈する必要はない。□

## 2. SCC の数学的性質

`u ↝ v` は長さ0を含む有限到達可能性とする。`u ≈ v` を `u ↝ v ∧ v ↝ u` と定義する。

### S2（唯一の成分分割）

≈ は同値関係であり、その同値類が G の強連結成分である。同値類を頂点とし、異なる類間の元の辺を残す condensation D は DAG である。

**証明。** 反射性は長さ0、対称性は定義、推移性は二つの道の連結から従う。一つの類は相互到達可能であり、相互到達可能な頂点を加えれば既に同じ類に属するため最大である。逆にどの強連結部分集合も一つの類に含まれる。D に非自明な有向 cycle があれば、その上の類は全て相互到達可能であって異なる類という仮定に反する。□

したがって singleton も SCC である。自己参照辺や非自明な cycle がなくても、同じ Value を両 endpoint に持つ extrusion は資格を満たす。

### S3（辺追加による正確な merge）

固定した有限頂点集合に辺 `a → b` を一つ追加する。旧成分を `A=[a], B=[b]` とする。

1. A=B なら成分分割は変化しない。
2. A≠B かつ旧 D に `B ↝ A` がなければ、成分分割は変化しない。
3. A≠B かつ `B ↝ A` なら、合併する成分は正確に

   `M = {C | B ↝ C ∧ C ↝ A} = Reach_D(B) ∩ Pred_D(A)`

   であり、M 外の成分は変化しない。

**証明。** 新しくできた cycle は新辺を使わなければならない。A=B の辺は旧成分内部で既に道に置換できる。A≠B の場合、新辺を含む単純 cycle からその辺を除くと旧 D 上の B→A の道になる。これがなければ新 cycle はない。

B↝A がある場合、C∈M は旧道 B↝C↝A と新辺 A→B により A と相互到達可能になる。従って M 全体が一成分になる。逆に旧来異なる成分 C が新しく A と相互到達可能になれば、A↝C、C↝A の道から cycle を取り除き、新辺の直後から C までと C から新辺の直前までを選べる。これらは旧 D 上の B↝C と C↝A を与える。A を含まない別の新 merge があっても、その cycle は新辺を含むので A と同じ新成分になる。よって M 外には merge がない。□

辺追加により資格は失われない。挿入順序によらず、同じ最終辺集合に対する成分分割は S2 の一意な ≈ である。これは辺削除・別 branch への rollback を対象にしない。

## 3. 凍結 graph に対する実 SCC 計算

凍結コード `candidate_value_graph.rs::Graph::seal` は、正方向 DFS の終了順を作り、その逆順に逆辺 DFS を行う。成功した初回 seal、有限で整合した forward/reverse adjacency、呼出し前の components が空であることを入力条件とする。空 graph は自明である。

### S4（seal と qualifies）

この条件の下で、seal の成功後、`components[u]==components[v]` と `u≈v` は同値である。既存 event の origin/receiver が有効な頂点なら、`qualifies(event)` は承認済み SCC 資格と同値である。計算は `O(|V_raw|+|E_raw|)` 時間、入力を除いて `O(|V_raw|)` scratch で終了する。ここで raw は helper 頂点も含む。

**証明。** 正方向 DFS は push 時に seen を立て、各頂点を一度だけ push する。stack の next は未検査の次の隣接辺を指し、一度検査すると増加する。全辺検査後に一度だけ finish へ追加される。従って再帰 DFS と同じ終了順であり有限である。

異なる SCC C,D に辺 C→D があれば、その最大終了時刻は f(C)>f(D) となる。C が先に発見されれば、C 内の未訪問頂点とそこから到達する未訪問 D は、その探索の終了前に処理される。D が先なら D から C へは到達しないので、D の探索終了後に C が終了する。この議論を最初に発見された各成分の頂点に適用する。

逆順の次の未割当頂点 s の成分 C は、残る condensation の source である。未割当の D→C があれば f(D)>f(C) に反するからである。逆辺探索は未割当頂点だけへ進むため C の外へ出ず、C の強連結性により全 C を訪れる。そこで同じ start を component label にする。処理済み成分を除いて帰納すれば全類が正確に得られる。label は比較用の代表値であり source identity を変えない。

qualifies は両 label の equality そのものである。S1 の条件下では raw graph の equality を元 Value の equality に戻せる。各 DFS は頂点を一度、辺を一度処理し、stack/seen/finish/component は各線形長である。□

**実コードへの適用境界。** `seal` は `components.len()==edges.len()` で早期 return し、再確保時も古い component entries を初期値へ戻さない。従って「頂点数を保った辺変更後の再 seal」や「部分 seal 失敗後の継続」を上の定理に含めない。成功して凍結した graph への再呼出しなら、同じ正しい label が返る。呼出し側がこの lifecycle を満たすことは別の全 caller 義務であり、本稿は全 error/retry 経路を認証しない。

また builder が現在扱う If/Sequence/Record/Tuple/Variant 等の全 fragment membership は、Name/Apply の承認だけからは導出しない。S4 はそれらを含む**構築済み graph の SCC 計算**については成立するが、その graph が全 source について正しいという主張には追加の S1 premise が必要である。

## 4. 実 extrusion occurrence からの等置

[承認済み association](../design/2026-10-12-intrusion-value-type-association.md) に従い、実 extrusion occurrence を

```text
e = (id_e, origin_e ∈ V, receiver_e ∈ V, P_e)
P_e = finite list of (copy, parent, polarity, target_level, kind)
Eligible_G(e) ⇔ origin_e ≈ receiver_e
Eq(G,E) = {(c,p) | e∈E, Eligible_G(e), (c,p,pol,l,k)∈P_e}.
```

とする。P_e はその実 extrusion が生成・保持した polar pairs に限る。異なる e が同じ pair を共有してもよい。parent/copy の type identity から origin/receiver を再構成しない。新しい Name edge を P_e から作らない。

### S5（資格・activation・順序独立性）

正確な G/E が与えられたとき、各 e の初回 eligible 時だけ P_e を発行し、後は発行済み flag を保つ手順は、有限の単調な辺/occurrence 追加の最後に正確に Eq(G,E) を発行する。全型等置の推移閉包は、辺の挿入順序、event の検査順序、pair の処理順序に依存しない。既存 e も graph の merge 後に検査する公平性を前提とする。

**証明。** 発行時に eligible を検査するため、その時点の pair は Eq に含まれる。S3 の単調性により最後にも含まれる。逆に最終 Eq の pair を持つ e は、生成時に既に eligible か、その後の最初の成分 merge により eligible になる。公平な検査で発行される。重複発行を除く flag はこの包含を変えない。同じ最終 G/E は同じ Eq を定め、等置結果は Eq を含む最小同値関係なので一意である。□

凍結 graph の場合、資格は occurrence 登録時から一定であり、merge 後の再検査は不要である。変換結果の再利用を新しい occurrence として記録する場合も、実際に再利用した元 pair list をその occurrence に保持して同じ証明を適用する。FreshUse だけでは新 occurrence を追加しない。

### S6（有限処理と境界）

固定 n 個の Value、有限 m 回の辺追加、有限 E と `P=Σ_e |P_e|`、有限 t 個の型座標の下では、成分数を減らす merge は最大 `max(n−1,0)` 回、pair 発行は最大 P 個、異なる型同値類の merge は最大 `max(t−1,0)` 回である。同じ類の重複 pair は no-op である。kind ごとに処理する場合は各非空 kind の同じ上界の和でよい。

**証明。** 各成分 merge は非負整数である成分数を少なくとも1減らす。各 event flag は一度しか変わらず、その時だけ有限 list を発行する。異なる型類の merge も型類数を1減らす。これらの測度と有限 list の残数で終了する。□

この結論は、propagation が無限に新しい row/occurrence を作らないことを証明しない。有限入力 source だけから E や t の有限上界を導くには combined inference の別測度が必要である。native の `settle_candidate_intrusion` が merge 中に発生させる仕事の全停止性も、この固定集合の上界だけでは出ない。

## 5. 等置後の型制約の意味

### E1（一回の native extrusion の終了と level）

元の `Typer.scala::extrude` を固定 target level l、初期状態が空の一つの polar memo で呼ぶ。実際の `constrain` からの入口も `MutMap.empty` を渡す。入力型と旧各 bound は有限の Function/Record/Primitive tree で、cycle は有限個の Variable を経由するものとする。途中で別 propagation を並行実行せず、この呼出し自身が加える parent link と copy bounds だけを許す。すると呼出しは終了し、結果の全変数は level≤l となる。旧 wrong-level 変数が h 個なら新 copy は最大2h個である。

**証明。** acceptable な型を返す場合と Primitive case は停止する。wrong-level variable a に初めて polarity p で達すると、native は fresh c を level l で作り、`memo(a,p)=c` を**選択 bound の再帰走査前**に挿入する。再訪は c を即座に返す。新 c は acceptable なので新しい wrong-level key を作らない。従って memo miss は旧 variable と二 polarity の組に限られ、最大2h回である。

各 miss が読む selected bound list は有限である。旧 list は有限で、今回旧 variable に加えるものは各 polar miss の単一 parent link だけだから、全追加も有限である。正負双方を訪れると、一方が加えた fresh copy の link がもう一方の selected list に入る場合があるが、その copy は level l なのでそこで停止する。新 c に格納する copied list は新しい高 level variable を生まない。

各 miss が一度だけ開く有限 list と最初の型 tree を、有限個の作業 container として数える。container 内では Function/Record の有限 tree を降り、variable は memo hit で止まるか、未開封の container を一度開く。未開封数は有限であり、開封済み container を再開する規則はない。従って無限 call chain はなく、全処理が終了する。これで cyclic bounds に対する構造帰納の循環を避けられる。

返り値が作られる順序に帰納する。acceptable subtree と fresh copy は level≤l。Function は両子、Record は全 field の level の最大なので同じ上界を持つ。返した memo copy の bounds に cycle があっても copy 自身の level は l である。□

E1 は既存局所意味保存定理の「完了した有限 invocation」という入力を、この native finite-store 条件で実際に供給する。raw Variable の level と source witness の依存 scope は同一視しない。また新たな bound propagation が次の extrusion を何回発生させるかは E1 の対象外である。

### S7（native constraint quotient の正確さと健全な向き）

K を有限の Function/Record/Primitive 型制約集合、Q を上記 Eq から生成した kind-preserving 同値関係とする。q:T→T/Q とし、`qK` は K の**全ての**型変数 occurrence を q で置換した制約集合とする。型解釈を外延的な通常の native 解釈とすると、次の二集合は全単射で対応する。

```text
models(qK)
{ρ | ρ ⊨ K and ∀(a,b)∈Q. ρ(a)=ρ(b)}.
```

**証明。** quotient 側の valuation η を `ρ(a)=η(q(a))` として持ち上げる。型構造への帰納により `⟦q(t)⟧η=⟦t⟧ρ`。関数の反変引数も両辺の解釈が等しいので保存され、record は全 field、primitive は同じ定数を保つ。各制約が同値になり、ρ は Q 上一定である。逆に Q 上一定の ρ から `η([a])=ρ(a)` は代表の選び方によらず定まり、同じ帰納を適用できる。二写像は逆である。□

したがって、両側の旧 bounds を欠落なく保持し、全変数参照を canonical 化する equality solver は、K に Eq を加えた問題を解く。これは解集合を広げない。元の [extrusion 局所定理](2026-10-13-intrusion-source-preservation-proof.md#4-direct-native-extrusion-derivation) の

```text
⟦t⟧ <: ⟦extrude(t,+,l)⟧
⟦extrude(t,−,l)⟧ <: ⟦t⟧
```

を合成すれば、等置後の解は、その局所 cut における元の未 extrusion demand も満たす。cyclic bounds は有限変数 valuation 上で解釈し、無限に型を展開して帰納しない。局所の pointwise diagonal construction は既存稿を再利用する。

この全単射は「元の全解が等置後にも残る」とは言わない。また scope・固定 capture・generalizable 座標・source effect witness を消す全単射でもない。型座標の quotient が原 source の quantifier telescope を保つことは別証明である。最小 level と non_generic の論理和は低い共有座標を誤って fresh にしないための情報であり、required coverage の証明にはならない。

## 6. 具体的 source と native owner への適用

```text
let rec f = lambda x.
  let g = lambda y. (lambda z.y)(f y)
  in {a=succ(g 0), b=g true}
in f
```

g initializer 内の `f` は G の所属なので G→F。g initializer を除く f body 内の二つの `g` は F の所属なので F→G。wrapper は新しい definition を宣言せず、g の owner を変えない。従って S1/S2 により F≈G。この二辺だけで資格が成立し、他の正当な辺が追加されても失われない。Apply の Lambda fragment をどう扱うかという未選択部分を使ってこの二辺を作ったわけではない。

`f y` の demand は元の [native 導出](2026-10-13-nested-live-root-generalization-derivation.md) により、origin G、receiver F、polar pairs `(C,B,+,1)` と `(D,R,−,1)` を持つ。S5 より選ばれる等置は C=B と D=R。型 copy C/D を Value graph の頂点にする必要はない。

| native owner | 本稿で得た対応 | 残る前提 |
| --- | --- | --- |
| `candidate_value_graph.rs::retain_source` owner pass | nested initializer の owner 切替、Name の resolved target、Apply event の `owners[index]` は S1 の構成 | 全 lowered source の tree/identity 対応、全 constructor の fragment authority |
| 同ファイル helper construction / `seal` / `qualifies` | S1 の helper-path lemma と S4 の成功初回 seal | 同じ graph を凍結して使う全 caller/error lifecycle |
| `candidate_intrusion.rs::retain_extrusion_parent` / `finish_candidate_extrusion` | 実 polar pair と occurrence/range を保持し、source event の資格で pending を作る | contextual `source_events(sources)` が実 occurrence に対応すること。複数 event の `any` を正当化する全 propagation/transport 対応 |
| 同ファイル `recapture_candidate_extrusion` | 実再利用 output の group に別 occurrence を付け、元記録を保持する | memo/transport の全経路で正しい group が選ばれること |
| 同ファイル `settle_candidate_intrusion` / `merge_candidate_rows` | pending pair を実 equality へ渡し、両 bound 側、最小 level、non_generic の論理和を移す | S7 の全 clause 保持を contextual effect/capture/future に拡張する証明、combined worklist 停止 |

この表は静的コード読解による owner 対応であり、実行・テスト結果ではない。全 consumer の保存定理を表から自動的に得ない。

## 7. 元の証明への帰結

これで次の連鎖の graph/selection 部分は具体的に構成された。

```text
承認された Name incidence
  → owner / fragment graph（S1）
  → 正確な SCC と変化（S2–S4）
  → 実 occurrence の polar pairs（S5）
  → 有限固定集合での equality 処理（S6）
  → 終了する局所 extrusion と旧 native demand を保つ解
      （E1 / S7 + 既存 extrusion 定理）
```

元の任意 source の型付けを **intrusion 後にも表せる** という逆向きは残る。具体例についても [元の member/world 稿](2026-10-24-correlated-helper-original-member.md) の J_rec/J_pub を別に構成する必要がある。SCC の資格は source component の登録、捕捉された型記述の telescope、generalization eligibility と同一ではない。

全 source の propagation/transport 対応、source lawful-use coverage、主型性、combined inference の停止性は OPEN。ここで扱わなかった constructor を source 言語から除外しない。intrusion が unsafe だという結論も、完全に正しいという結論も、上の局所定理だけでは出ない。

## 8. 凍結と検査

契約 `tasks/agent-loop/sprints/extrusion-intrusion-scc-20261024.md` の authority・native 入力に依拠する。補足の call-site 読解は同 baseline の `crates/yu-solver/src/lib.rs::ConstraintBatch` collection 終了時と SolveSession 初期化時の seal 呼出しに限る。数学的 S4 は上記の初回成功・凍結条件を明示しており、これらの call-site の存在だけを lifecycle 証明とは扱わない。

本稿の成果は紙上証明と source 静的対応。実装変更、テスト追加・実行、compiler/build 実行はない。独立査読の固定 hash と判定は sprint outcome に記録する。

補足静的入力の固定 bytes（既存 local extrusion 定理の source 対応を確認）:

- `crates/yu-solver/src/lib.rs`: `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07`
- `/home/momota1029/rust/simple-sub-reference/shared/src/main/scala/simplesub/Typer.scala`: `f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9`
