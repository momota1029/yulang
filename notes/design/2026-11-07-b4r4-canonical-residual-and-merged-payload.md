# B4r4: canonical residual と、variant 合流後に残る冪等 payload

状態: **承認後の record 捕捉を保存した、新しい core-registry E2**（2026-11-07）。
仕様の正本は spec 6.3 / K2、4.3 / 4.5、10.4。
今回の変更は新規 Lean 8 module と import / Audit / README の追記だけ。
旧 E2 と既存 proof、spec、公開入口は変更しない。

## 1. 旧 tail-clock は今回の反例ではない

承認後、具体的な record G に対する head `{x:P,..a}` の tail は、G から明示した可視 label を引いた残り。
`G={x:int}` なら `a={}` だけであり、`a={x:int}` への選び直しは許さない。
goal に未解決 tail があれば解決を開始せず、qualified obligation として待つ。
`CommonRoleFiniteTailObstruction.normalized_registry_undecidable` は旧 arbitrary-assignment 意味の定理として保存するが、
現在の canonical-residual 意味へ適用しない。

新規 `CommonRoleCanonicalRows` は payload 型を任意にして、行を有限 label/payload 列とする。

```text
normalize row = first-field-wins で後の同名 entry を除いた row
residual labels row = label が labels にない entry を元順序で残した row
capture labels row = residual labels (normalize row)
Captures labels row tail ↔ tail = capture labels row
```

capture は同値方程式の任意解ではなく、この実関数の結果だけを受け取る。
label の相違を除き payload を推測しないため、一意性、隠れた label の不在、
normalize 前後の一致、任意 payload 写像との可換性を証明できる。
任意非負 payload weight を与え、entry を1+weightで数えると selected と residual の質量は元の質量を分割する。
明示 label が実際にあれば residual は真に小さい。旧一field clockの捕捉は空行になる。
これは canonical residual の局所的な正当化であり、全 Common row solver / 全 N / full E1 の完成ではない。

複数 tail へ残りを任意に分配する意味は採用していない。
一般の複数-tail source lowering、union を持つ record、open variant row の全 decoder は未実装。
その不足を今回の E2 の前提へ移さず、tail のない実 registry で全称目標を反証する。

## 2. 実 variant merge と size の相違

一般 union 型注釈を source に書けるとは仮定しない。
同じ variant tag と同じ有限 data pattern P を n+1回書いた row を用い、
実 `Variants.Merged.normalize joinTerm` を実行する。

```text
data grammar P ::= var | int | pair(P,P) | variant(tag,P)
joinTerm A B = app 4 [A,B]  -- payload union の固定 codec
padded 0 P = P
padded (n+1) P = union(P,padded n P)
rawRow n P = [(tick,P),...,(tick,P)]   -- n+1 entry
mergedRow n P = 実 normalize joinTerm (rawRow n P)
```

`merged_entries` は実 entries が `[(tick,padded n P)]` に等しいこと、`merged_tag_unique` は tag Nodup を示す。
head はこの実 singleton row から作った `tick(padded n P)`。
`all_heads_from_merge` は任意 Code の全 visible 実 impl の head についてこの由来を証明する。
constructor ID は arity と組で区別し、app4の二引数はunion、一引数はvariant tag1となる。
固定 interpreter がこの区別を実行する。意味を表す外部 oracle は取らない。

spec10.4 の実 merge は payload 冪等則を要求せず、tag の重複だけを取り除く。
一方、Common の union は join なので任意 Common A に対し `padded n A ≈ A`。
有限構文サイズは `(n+1)*size(P)+n`、各変数の出現回数は `(n+1)*occ(P)`。
したがって、record の重複 field 除去だけでは、意味で消える大きさをすべて取り除けない。
この反例で必要なのは payload union の冪等性だけであり、分配則、nominal unfolding、associated projection は使わない。

## 3. N、実 checker、associated と requirements

承認済み N は hidden record field を構造的に除くものとして維持する。
今回の head / where は record を一切含まないため、全実 declaration で `N impl = impl`。
旧 `CommonRoleNormalizedDeclarations.normalizeTerm` もこの family で固定になる。
この事実を全 Common grammar に対する N の完成と読み替えない。

新 `checkImpl` は下の decoder で head / where を読めることを検査し、
その後に実 `CheckedRoles.checkImpl (N impl)` を実行する decidable な十分条件 checker。
既存の Pattern 限定 `VerifiedDeclaration` API がこの union encoding を読めるとは主張しない。
全 finite Code の compile はこの新 checker と実 raw checker / WF を通る。
Raw checker は承認された N 後の size/occurrence 条件そのものであり、追加の停止仮定を取らない。

全 associated RHS は実格納 field の定数 int。
signature は既存の unary role 5個、associated type 0を必須とする表で、scope / completeness / arity を証明する。
`HeadDeterminesAssociated` は任意二 Common 代入と実 head / RHS 解釈を量化する。
head の解釈が未定義なための空虚な主張ではない。

さらに `HeadDeterminesRequirements` を次で定義した。

```text
任意 i∈visible、任意 σ τ : Nat→Common.Ty、
全実head termのσ/τ解釈が定義され要求同値なら、
任意実where childについて両解釈が定義され、roleは等しく、型引数は要求同値。
```

`head_determines_requirements` は任意 Code の全実 registry がこれを満たすことを示す。
任意 finite source だけの条件ではない。rigid data pattern の同値から各使用変数の同値を回収し、
元 linear rule の occurrence 条件で right の使用変数も覆う。
この条件を加えるだけでは、今回の E2 は除外できない。
一般の canonical record/variant residual に同条件が必要か・十分かという別問題は未証明。

## 4. 独立 canonical matching と実辞書

決定済み goal は `R tick(Ground)`。Ground は有限 int/pair/variant 木で、自由変数も tail もない。
decoder は、payload の `union(P,P)` の同一 branch だけを再帰的に縮約し、残りを rigid data pattern として読む。
任意の union 分割、代入後に都合のよい同値解選択は行わない。

独立 `Matches i g σ` は、実 head の decoder が P を返し、role が等しく、
`P.instantiate σ = g.value` であること。σ は finite Ground の構造的捕捉。
実 `headMatches` Bool は構文 walk で canonical capture を計算して再構成の等号を検査する。
`head_matches_exact` が両者の iff、`capture_agrees` が全使用変数の一意性を示す。
同じ head に一致する二捕捉の where child は等しい。

`generated_match_exact` / `visible_candidate_exact` は、この generated family の全有限 goal について、
独立構造一致の代入存在 iff 実格納 head を任意 Common 代入で解釈して要求同値にできることを示す。
したがって、decoder を狭めて candidate を見落とすことで作った障害ではない。
`unique_common` は canonical 候補一意性を任意 Common 候補一意性にも移す。

独立 Dictionary は実 visible 所属、独立 Matches、全 visible 候補の一意性、
実 constraints field の各要素を同じ捕捉で解釈した**全 where child**の Dictionary を要求する帰納的 Type。
child も根と同じ visible を使う。実 impl / key と全 child を `RoleDictionaries.Plan` へ消去し、
全格納 impl が visible であることを証明する。
成功自身を resolver の停止仮定として渡していない。

K2 は承認されたまま：root の構造的再帰型に達したとき、および非変数 head がその constructor を調べる時点で拒否。
変数捕捉は constructor 検査でない。nominal body は展開しない。
今回の全 goal / 全 child は有限木なので、再帰型の graph 判定の内部選択によらず両拒否は起きない。
既存 `finite_ready` と新 `goal_ready` が任意 visible でこの事実を示す。
旧 countergrammar の cycle classifier を全 regular graph classifier の完成と主張しない。
E2 は全 regular 入力の部分集合である有限木だけで成立し、full classifier 実装を待たずに全称 E1 を否定する。

拒否が起きる候補が一つでもあれば曖昧性より拒否を先にするのは、依然**作業上の選択**。
[既存の未決質問](../questions/2026-11-07-b4r2-rejection-priority.md) を確定扱いしない。
この family には拒否がないため、優先順位を逆にしても E2 は同じ。

## 5. 全域 resolver がないこと

任意有限 linear data rule left→right を実 head `tick(padded k left)`、
実 where `tick(right)` へ翻訳する。k=rawSize(right)+1 とする。
宣言 checker の size 真下降と occurrence 条件を満たすが、意味上の right の大きさは制限されない。
既存 finite linear interpreter の全 Code を、この実 registry へ compile する。

`dictionary_exact` は任意 Code,inputについて、全whereを持つ実有限 Dictionary 存在 iff `∃output,Eval Code input output`。
`actual_plan_exact` は全実 Plan 宣言の visible 所属を加えても同じ iff。
上位の任意 Common 代入 Derives は、一意性/K2を要求しない大きな判断だが、
`arbitrary_common_exact` / `canonical_iff_arbitrary_common` が同じ成功集合であることを示す。
これは現在の canonical matching を arbitrary tail 意味へ戻す定義ではなく、意味の比較定理。

wire は実 associated impl の head/where/key/associated RHS、実 role signature、実 finite goal description を保存する。
固定 queryCode が descriptor の database と Code quotation をコピーし、raw input を有限 data 記述へ埋める。
descriptor に停止答や semantic oracle はない。
その実 query に対する全域 finite tape machine が成功bitだけでも正確に返すと、既存 Halts 非決定性に矛盾する。
これが `canonical_merged_registry_undecidable` の E2。
selection / rejection / ambiguity / 実辞書を全部返す resolver はこの必要成功bitも返すため排除される。
単に一つの nonterminating recursive search を示した定理ではない。

## 6. source 境界と他の可能性

質問 note の source variant 例は実 parser probeで ok1 / recovery0。
実 merge → 実 stored head の Lean bridge は証明した。
full source elaborator、constructor ID allocator、全 source declaration checker の正確性は証明していない。
対象は元契約の任意 verified core registry。source-generated registryだけに狭めた別定理を反証したとは言わない。

小例は一tag・二payloadコピー・一whereの self-loop（size4/2、変数なし）と、
一変数でboxを増やす例（size4/3、occ2/1）。絶対最小性は主張しない。
source 一般 union 注釈の禁止では、実 variant merge 後の payload union を core checkerから排除できない。
提案は payload 冪等縮約も size/occurrence 前に実行すること。承認はまだない。

今回、record の複数 tail、variant tail の恣意的分割、associated RHS の他role展開、nominal body 展開は使わない。
名目再帰型への新規拒否は追加しないが、一般 nominal agreement 定理を証明したとも言わない。
その他すべての type-equivalence-invisible size の完全分類、全 union/row 正規形の完成も未証明。
「record の duplicate 除去だけが唯一の問題」という主張は、この payload idempotence の実構成で否定された。

## 7. qualified の正確な未証明 lemma

単独の finite qualified generator が存在しないとは証明していない。
registry E2 が B4 全体の連言を否定する一方、元7.6の生成部分の残りは次の数学的 interface statement。
新identifierをLeanで宣言したという意味ではない。

```text
任意有限 declaration D、任意 caller-visible V⊆D、任意有限検証済み method 表 M、
任意有限 kind付き自由名集合 A、任意有限 scheme環境 Γ over A、
任意 full Common 式 e、任意有限結果型/行項 out over A について、
  NormalizedWellFormed D ∧ HeadDeterminesAssociated D ∧ VerifiedMethods D M
なら、実 generator は有限 package C を返す。
C は実 method ID、ordinary型/行等式、pending role obligations、
weak/captured/generalizedの分類をそれぞれ保持し、
任意 kind保存ρ（Aのtype名→任意Common.Ty、row名→任意Common.Row）について、
  IndependentQualifiedTyping D V M (Γ.eval ρ) e (out.eval ρ)
  ↔ ∃ kind保存 local割当てι,
      C.ordinary が(ρ,ι)で成立 ∧
      C.pendingの全具体化goalがcanonical residualと両K2を含む独立有限辞書を持つ ∧
      C.associated の等式が同じordinary store上で成立 ∧
      capturedは同じρを共有し、generalizedは各使用で独立に具体化する。
```

未解決 record tail を持つ symbolic obligation は生成時に解かない。
上の任意ρで具体化した後に canonical residual を使う。ρを有限木や成功する解へ制限しない。
左辺は独立 typing であって、生成後の Satisfies の別名でない。
ordinary等式・associated等式・role evidenceは右辺の意味の一部であり、外部前提へ逃がさない。

さらに全自由 parameter family の未証明 lemma は、任意同D,V,M,Γ,e,outについて実返却scheme族をSとすると、
任意s∈Sの任意無制約kind保存parameter割当てpが同ordinary/associated/role意味のmodelを与え、
逆に任意元modelはあるs∈Sとpで同じrowおよび要求同値の全type slotとして回収されること。
`Satisfies` を p の追加条件にすることは許さない。
今回、この実generatorのiffも全familyも証明していないし、その単独非存在も主張しない。

## 8. 終了範囲

E2で終了する。full E1、全Common N、全regular matcher、一般finite-tree/nominal agreement、qualified実生成と全family、
source/public入口/Rust統合は残る。
小例の提案縮約を修正E1として採用せず、ユーザー承認用の [一問](../questions/2026-11-07-b4r4-merged-payload-size.md) に置いた。
prover roleは設定にもlive schemaにもなく、prover agentは起動していない。
primaryが構成し、別agent二名によるcountersearch/独立reviewを受けた。最終検証はresultsに記録する。
