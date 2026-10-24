# 共起商と経路別解除の保存

Assignment-ID: COOCCURRENCE-PRESERVATION-20261024/r1
Author: `/root/astra_cooccurrence_proof`; descendants: none.
Status: 未査読の構成的数学と限定された source evidence。言語全体の定理、native 対応、production authority は OPEN。
Post-freeze review: 上記は producer の凍結時の状態。r1 の数学本文は独立査読で局所表示定理の範囲で ACCEPTED、BLOCKING/MAJOR 指摘なし。[査読・統合記録](../../tasks/agent-loop/sprints/cooccurrence-release-20261024-outcome.md)に対象 hash と範囲を記す。この一行のみ primary が査読後に追加した。
Contract: `tasks/agent-loop/sprints/cooccurrence-release-20261024.md`, SHA-256 `a30684fdb4c1880810f4e3eb8b521feb68adba43f270c3bed520dda02fb17db8`。
Baseline: `6602786c430df75312a2ffb74ebd9561113f3511`。
Requested model/effort: Astra/medium; observed model/effort: UNKNOWN。

## 1. 親への適用範囲と authority

親は元の承認された source 領域における Yulang 全体の型健全性であり、任意の型導出と任意の有限実行 prefix を量化する。Simple-sub の A/B、主型性、停止性、独立した continuation の量化は残る。本稿はこの量化を有限個の例や一つの release frame に縮めない。

直接の訂正は `notes/design/2026-10-24-cooccurrence-release-clarification.md` に従う。実行前に供給引数を保護し、全く同じ共変位置で共起する成分を同じ変数で表示する。`'e?` から独立の実行意味論を設けない。共起した対象の grouped release は追加仕様選択ではないが、その表示が保護と解除を保存する証明は必要である。旧 `A_all` の binder 名だけによる選択を承認済みに読み替えない。

本稿の到達点は、(i) 実際の正極性 group collector の交差不変式、(ii) 同じ位置集合を持つ成分の商において動的証拠を fiber として保持する明示的構成、(iii) その構成の保護導入・輸送・実際の crossing・query 保存である。静的型変数をまとめても receipt、receiver、scope、route witness、target はまとめない。この fiber は証明上の表示であり、追加の runtime table を設計・要求するものではない。

## 2. 実際の正極性 group に関する補題

固定した一回の `collect_co_occurrences(root, roles)` が `record_group` に渡す正極性 group の列を `(G_p)_{p∈P}` とする。p は呼出し occurrence の索引であり、同じ集合を二回記録しても索引は別でよい。各 G_p は `AlongItem` の集合である。`Var(a)` の incidence を

`I(a) = {p ∈ P | Var(a) ∈ G_p}`

と定める。この段階では P を全 source の実行 path と同一視しない。実際の traversal は root、再帰 bound、role を訪問し、Function の arg/arg_eff で極性を反転し ret/ret_eff で維持する。row-tail の group、ignored recursive center、interval の処理も含む。

**補題 1（交差不変式）。** 全 group を記録した表 T について、I(a) が非空なら

`T[a] = ⋂_{p∈I(a)} G_p`。

I(a) が空なら a の entry は存在しない。

証明。空列では全 entry がない。一つの G を追加すると、G に a がなければ entry は変わらない。a があり初回なら G の clone を挿入し、既存なら `retain(|item| group.contains(item))` が交差を取る。列長への帰納で得る。Exact 項の混在はこの等式を変えない。□

**補題 2（相互 membership）。** I(a), I(b) が非空なら、

`Var(b) ∈ T[a] ∧ Var(a) ∈ T[b] ⇔ I(a)=I(b)`。

証明。左の第一項は `I(a)⊆I(b)`、第二項は逆包含に等しい。逆向きも交差の定義による。□

実際の `register_co_occurrence_table(positive, negative, ...)` は両 membership を確認し、さらに `opposite_co_occurrence_compatible` と simplification candidate/level/non_generic 条件を通す。従ってこの正極性 pass が直接提案する pair は同じ I を持つ。追加条件を本補題から削除せず、それらが併合を拒む場合も認める。同じ I の pair だけの推移閉包は同じ I の class になる。

**厳密な source 境界。** `CoOccurrences::substitution` は先に interval equality を登録し、正極性 pass に加えて負極性 pass と両向き sandwich flattening を行う。union の代表がこれらの別証明由来の成分を既に含む場合、上の正極性 pair の性質だけでは最終 union class の性質は言えない。sandwich の Exact 分岐には変数除去もある。従って「実際の全 merge が正の equal-incidence」という主張はしない。補題 2 は空 incidence の変数を勝手に統合する許可にもならない。

## 3. 相関を保持する商の明示的構成

有限な位置集合 P と成分集合 A、非空 incidence I(a) を固定し、`a ~ b ⇔ I(a)=I(b)` と置く。`q:A→A/~` は静的ラベルだけの商である。位置 p の元の成分集合を A_p とすると

`q⁻¹(q(A_p))=A_p`。

証明。a が p にあり a~b なら同じ incidence により b も p にある。逆包含は自明。□

これは共起条件の具体的な用途である。class をある出力位置の対象に使ったとき、別位置だけにあった静的成分が混入しない。grouped target を p に現れる class c ごとに作るなら、元の対象 `{a | q(a)=c, p∈I(a)}` は c の全要素と等しい。ただしこの静的等式は actual receipt の選択や crossing の成立を含意しない。

各動的 witness は一つの scope に属するものとし、同じ event に複数 scope がある場合は scope ごとに別 witness を残す。証明用データを

`d=(w, a, b, r, s, route, H, Prot, origin, port, other)`

と書く。b は actual receipt、r は元 receiver、s は scope、H はこの route が輸送した target 集合である。`other` は query に使う family/type instance、path、Observe などの既存証拠を全て含む。これは必要な既存証拠を明示する記法であり、それを既に native が保持するという仮定ではない。

Q は d を消去せず、class q(a) の下に元の d 全体を置く。位置別、port 別の incidence と witness ID を保持するので、同じ w が二 port にあっても二つの独立 witness に複製しない。異なる w は全ての観測値が等しくても同一化しない。Q は outer key の商であり、その fiber の内容を無名の protection bit や target 和集合に置き換えない。

有限な source recipe に actual environment ρ を適用して対象表を作るときも、class c の表は各 a∈c の **元の recipe と actual receipt をタグ付きで合わせたもの** とする。具体的には `(a,b,r,origin-path)` の関係を保ち、Match はその同じ tuple 内で成立させる。各列を独立に射影して直積を再構成しない。重複する同一 tuple の set 化はよいが、別 receipt は残る。新しい call の b' を既存 target に後付けしない。

**補題 3（保護導入）。** execution 前の supplied argument の actual receipt について fresh scope/witness を導入し、その immutable origin を保存する操作 Protect と Q は可換である。

証明。元表示で各 actual receipt に作った tuple を Q 後の対応 fiber に挿入する。商表示で同じ actual receipt を列挙して挿入しても、同じ tuple と同じ class を得る。freshness は既存の全動的 ID に対して取り、静的 class に対して取らない。予約 receipt のみで witness が未発生なら両側とも witness を挿入しない。複数 receipt が同じ class にあっても tuple 数は変わらない。□

## 4. 輸送・crossing・観測の保存

以下は corrected candidate の実際の式を使う局所的表示定理である。候補式の言語全体への採用を主張しない。現 world の activity を Act、release 関係を `L⊆Scope×Target`、元の tuple から読む照合を Match とする。

`C_L(w) = ∃t∈H(w). L(s(w),t) ∧ Act(r(w)) ∧ Match(t,s(w))`

`Live_L(w) = Prot(w) ∧ ¬C_L(w)`。

元の query の他の全条件を D_j(w)、foreign receiver 条件を F_j(w) とし、

`P_j=∃w. D_j(w)∧Live_L(w)`、
`PF_j=∃w. D_j(w)∧Live_L(w)∧F_j(w)`。

Q 後も同じ tuple で連言を評価し、fiber 内、次に class 間で存在量化する。

**補題 4（輸送）。** 構造射影で actual component の witness を選ぶ操作、alias で同じ witness を参照する操作、fresh route w' を作り `H(w')=H(w)∪{t}` とする view 操作は Q と可換である。

証明。選択は保存された component/port/path で同じ行を選ぶ。alias は同じ ID を参照する。view は元行を残し、同じ親から同じ fresh ID の子行を両側で作る。追加される t は子の H のみに入る。いずれも class key の変更と行操作の順序は独立である。source の型代入が incidence を変える場合にはこの固定 Q を自動再利用しない。再計算した class と既存行を対応付ける bridge が別途必要である。□

**補題 5（実際の crossing）。** actual packet z が delimiter t を外向きに越えるとき

`J(z,t)={s∈Scopes(z) | From_s(z) ∧ Match(t,s) ∧ Act(r(s))}`

`L'=L∪{(s,t) | s∈J(z,t)}`

とする。この更新と Q は可換である。

証明。Scopes、From、Match、Act は同じ actual route と immutable tuple、現在の world を読む。Q は全てを保持するため J が等しく、同じ pair 集合を L に追加する。H への target 輸送は補題 4 による。静的 class 全体を J として追加する操作はこの証明の式ではない。Ret/Fail で L を変えない場合も両側で一致する。□

**補題 6（query と grouped release）。** 全ての j について P_j、PF_j、および

`Eligible_j = Base_j ∧ (¬P_j ∨ GC_j ∨ (GW_j ∧ ¬PF_j))`

は Q 前後で一致する。別々の成分の同一 actual target t に対する対象集合を class fiber 内でまとめて評価しても一致する。

証明。Q は witness 集合を class ごとに分割しているだけなので、元の存在量化を fiber 内外の二重存在量化へ変形できる。D、Live、F は同一 witness 上のままである。target の Match 表をタグ付き union にしたときの membership は「元のどれかの同じ tuple に一致する」と同値であり、crossing の J も同じ union になる。L 更新は集合の union なので同じ t に対する部分集合ごとの更新と一括更新が等しい。Base/GC/GW の元の評価を変更しないので Eligible も等しい。別 target t,u の ID を一つにする定理ではない。□

これらを有限操作列の長さに関する帰納で合成すると、列中の各時点で Q による表示対応と query の一致を得る。receiver activity の変化も同じ world の更新を両表示で行う限り一致する。保存継続の再開では過去の L/Act/query を復元せず現在の world を読む。任意の foreign continuation の source 構成・適合性はこの局所帰納からは得られない。

### 反例 discriminator

`I(a)=I(b)={p}`、別 actual receipt b₁≠b₂、別 scope s₁≠s₂、別 witness w₁,w₂、同じ対象 t を取る。両 receiver は active、Prot は真、Match(t,s₁), Match(t,s₂) は真、H(w₁)=H(w₂)={t} とする。初期 L は空。w₁ のみを actual route に持つ packet が crossing すれば `L'={(s₁,t)}`。従って `Live(w₁)=false`、`Live(w₂)=true`。

Q は同じ class の fiber に二行を保持するのでこの結果を保存する。「class が一度解除された」という一 bit に縮める方式は w₂ まで解除して失敗する。これは co-occurrence の意味に対する反例ではなく、動的証拠を潰す表示に対する反例である。source reachability の証明済み反例とは分類しない。同じ event の二 route で H が片方にだけある場合も、H を event 単位で union する方式は同様に失敗する。

## 5. 親への適用と正確に残る bridge

共起は静的な対象範囲の飽和性を与え、動的な解除は actual receipt/route の証拠で行う。この分離により、同じ変数で複数入力を表示することと、一方の actual route の保護だけが解除されることが両立する。compose の identity forwarding では、輸送された出力内の同じ scope にも更新後 L を適用でき、別 scope の保護は保持される。これを compose/id 特例や ordinary inference の制限にしない。

親に対して新たに得たものは、同じ incidence の static quotient に伴う追加の解除障害が、証拠を保持する表示では生じないという局所構成と、実際の正極性 collector がこの incidence 条件を検出する証明である。全 source theorem の欠落を「共起なら安全」という仮定に包んでいない。次の owner 別 bridge が未解決である。

| TODO | owning source / consumer | 必要な証拠と falsifier |
|---|---|---|
| CO-1 | `collect_co_occurrences`, `visit_type_co_occurrence`, `visit_bounds_co_occurrence`, `visit_role_arg_co_occurrence` → source protection recipes | 記録 group の位置と、実際の supplied argument/output の対応。row-tail、再帰 center、polarity、roles を含む。falsifier は同じ I なのに対象 output recipe の位置が異なる actual constructor。 |
| CO-2 | `CoOccurrences::substitution`, `register_sandwich_flattening`, `record_interval_equalities`, `VarUnion::into_substitution` | 負極性・interval・sandwich・removal と既存 union class の別証明。正の pair 補題だけでは不可。falsifier は正の incidence が異なる class に補題 2 を適用する経路。 |
| CO-3 | `rewrite_type_vars`, `push_compact_var_with_unioned_weight`, `merge_compact_vars`, `ConstraintWeight::parallel_union` | 重み・origin の実表現から上の相関を保持した fiber への解釈と消費の可換性。falsifier は二 receipt/route の片方だけ crossing で他方の保護を失う例。 |
| CO-4 | 候補の `R-Inputs/R-Capture/R-Match`, `R-Cross/R-Project`, protection introduction, FreshUse/generalization の source consumer | binder 名による旧 A_all 表ではなく、正確な共起位置と actual environment から本稿の表が得られること。生成・蓄積・伝播・levels・extrusion・qualifying intrusion・generalization の各段階を保持。falsifier は fresh call が旧 target に混入、または独立 witness の消去。 |

CO-3 について実 source は `rewrite_type_vars` が代表変数へ置換後 `push_compact_var_with_unioned_weight` を呼び、同じ代表の weight を `parallel_union`、origin を `merged` する。`merge_compact_vars` も同じ方向である。`parallel_union` は filter の intersection と両側 entry の挿入を行う。これは上の fiber 関係を保持する証明そのものではない。重みの順序・scope identity・attachment の意味を確認せず set-union の定理を転用しない。

実装は今回の scope 外であり、minimal provisional TODO は CO-3 の既存 owner 入出力と最終 query を二 receipt discriminator で対応付ける read-only trace の設計までである。新しい instrumentation の実行・出力 lease は Luna が別途与える。native source の全 constructor、owner activity、latent transport、反復 resume、foreign continuation、型健全性の global quantifier は OPEN。新 semantics、bypass、source 制限は導入していない。

## 6. 依存、再利用、資源、凍結

全ての以下の bytes を SHA-256 で照合した。Oracle は `/home/momota1029/rust/yulang2-oracle-capture` 内の immutable commit `a58eefc31e22141574b6f20c6a5748151c6d79f1` に対する `git show` で読み、mutable checkout の source は使用していない。

| input | SHA-256 |
|---|---|
| clarification | `c9eb9b8d274172f02bc82088896c30dd92e219a02adf6ba22418b2cc34207d12` |
| compose authority | `fd56f819f9b33adc5d75cbfdae378c90903e4aa3a266fc053c05dda315d40679` |
| concrete compatibility boundary | `5b0b4321d8644f88a7a946aff31b6b3190d37a9076ac698fa91fdfeef1470f16` |
| corrected machine simulation | `fffb4f1540739020a0702d4f7b07d41cd9b68a9063f36d24292914b84e6b606d` |
| occurrence/mod.rs | `7bf082236f7c90a33fe9d0084dc3d993d3528bb5a272a44265df8f27728e46a2` |
| occurrence/substitution.rs | `b6d04c187a870892239db84a16360f700f7efaef4c0ba7b731d1389db31f9bf2` |
| merge/entries.rs | `d848f4034fa57cb7581e58116aba5e825b3f78c79d48bbd08800352dcfc3b10f` |
| poly/src/types.rs | `9211e62291b82e71e1b78763b83fe9f1d81e0fe4396d9e12d42e9a4a9b13b47c` |

corrected machine 稿の author は `/root/astra_corrected_machine`、修正 author は `/root`。その joint witness query、route Fork、現在 world の再結合を実際の候補という前提内で再利用する。古い revision 1 の witness 非挿入、route 上書き、stale world 復元は再利用しない。source 稿の R-* 節も式の確認に限定して参照し、旧 A_all の採用・全 source 対応・原稿の歴史的未回答状態を引き継がない。その他の依存 author は frozen file/commit の既存帰属に従い、本 producer の作としない。

三段階を実施: incidence/source audit、商構成と保存、親への適用と不足 bridge。上限 195 秒、三段階。正確な active duration は UNKNOWN とし、予約 195 秒を返却しない。`python` は環境に存在せず一回失敗し、`python3` による hash/read-only source inspection を行った。テスト、build、compiler 実行、network、Git mutation は行っていない。数学的検討と source inspection は independent review ではない。

新規・scratch path はこの artifact 一つのみ。handoff は最終メッセージ一つ。全書込みを終了して r1 を凍結する。descendants はゼロ。次は Luna による独立レビューと CO-1〜CO-4 の所有者への割当であり、本 worker は待機中の実行を装わず STOPPED。親と production の gate は OPEN。
