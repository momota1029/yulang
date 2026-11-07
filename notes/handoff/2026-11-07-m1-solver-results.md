# M1 solver 継続作業の結果

Status: Verified partial completion. Full presence M1 remains open.

Date: 2026-11-07

Branch: `integration/m1-solver`

Base: `integration/types` at `52c3410c31e0bfe2d4a0f23e8a2394358d557211`.

## 1. 到達点

新しい contextual 要求順序を、実際の constructor inspector、全入力の分岐付き飽和、
全自由 parameter の regular 解、型/行の simultaneous inference、旧 supported source/Core の主型性へ接続した。
旧 supported source について、新独立 Typing から同じ scheme family へ戻る完全性と、決定46の旧 Typing への
同じ結果行での要求同値を除く反映も閉じた。

別の positive data-demand 文法では、由来を持たない非 guarded な tail の循環を求解し、
単一 concrete layer 由来の mask family と、全深さの regular 解を構成した。

速度の側では、実 selection の局所性、実行中に snapshot を作る任意合法 SCC schedule の順序独立性、
selection/具体化/全簡約 pipeline の費用上界、cache 再利用と増分 build の全体再計算との一致を証明した。
Rust 前段の設計と最初の benchmark は既存 oracle-plan 第7節に記録した。

**M1 全体は未完了。** 上の constructor/arrow/row の carrier と positive tail/data の carrier はまだ同じものではない。
exactEmpty・required・strict な whole recordDefault image・関数・行・自由 mask を統合した具体モデルが必要である。
統合 `Core.infer` はまだ公開していない。既存の実入口を新順序で解釈する alias と、新しい証明を追加した。
完全な interface 標準形も未完である。

追加した **32 Lean module・498 public theorem** の名前と暗黙引数を含む完全な型は
[全定理一覧](2026-11-07-m1-solver-theorem-index.md) にある。
以下は主要な定理を、量化と前提を明示して日本語で説明する。

## 2. 共通の記法と前提

- `S ≤ᴾ T` は contextual `ProducerLe`、`S ≡ᴾ T` はその双方向比較。
- regular 版は、すべての constructor 観測深さ・負の文脈の rank・要求環境・union-free な要求を量化する。
  観測深さや rank は solver の fuel ではない。
- 「行前順序」は、任意の行 `r` に対する反射律と、任意の行 `a,b,c` に対する推移律。
- 「正確な行検査」は、すべての行 `a,b` について `rowCheck a b = true ↔ leRow a b`。
- `RowFlowSchemes.Algebra Row` は empty/join、行前順序、empty の下界性、join の最小上界則を持つ。
  source/joint の定理ではさらに `∀ a b, a ≤ b → b ≤ a → a = b` を仮定する。
- 「旧 supported」は旧実行可能 support checker が true であること。推論成功ではない。
  この checker は symbolic compile・shape 検査・行問題の support 検査を含む。
- `RecordFree` は既存の構文条件で、record 構築と recordDefault を除く。
  lambda/application/branch/let/pair/projection/variant/field/literal/旧 empty record を含む。
  Core では既存の埋込み構文条件も含み、let の hint は `none`。

## 3. 要求順序と完全な arrow 分解

### `ProducerContextual.producerLe_refl` / `producerLe_trans`

任意の行型、任意の行関係、任意の有限型 `A,B,C` について、`A ≤ᴾ A` が成立し、
`A ≤ᴾ B` と `B ≤ᴾ C` から `A ≤ᴾ C` を得る。regular 版は任意の graph と layer について同じ主張を持つ。

### `structural_subtype_preserved`（有限版・regular 版）

任意の行型、推移的な行関係、任意の旧有限型または任意 graph 上の旧 regular 型 `S,T` に対し、
旧構造部分型 `S ≤ T` なら `S ≤ᴾ T`。role の保存則を追加公理として受け取らず、具体 head 観測から証明する。

### `pair_union_group` / `record_union_group` / `variant_union`（有限版・regular 版）

任意の行関係と任意の成分型について、同じ constructor の union と、各成分の union をまとめた型は要求同値。
record は同じ label、variant は同じ tag を前提にする。pair は両成分、record は payload と tail の両成分をまとめる。
これは型の要求順序の等式であり、strict data image の等号ではない。

### `ProducerContextual.producerLe_arrow_iff`

任意の行前順序、任意の有限型 `A,A',B,B'`、任意の4行 `r,r',s,s'` について、

```text
(A -r/s→ B) ≤ᴾ (A' -r'/s'→ B')
  ↔ A' ≤ᴾ A ∧ r' ≤ r ∧ B ≤ᴾ B' ∧ s ≤ s'
```

`ProducerContextualRegular.producerLe_arrow_reference_iff` は、任意の graph、任意の4つの graph state と4行について
同じ比較を全深さで示す。`ProducerContextualRegular.producerLe_arrow_iff` は実際の inference carrier の任意型で同じ iff。
closed Negative 制限、引数を分離するという仮定、solver 成功、fuel はない。

要求変数は任意の意味型を表し、role 要求は具体的な head table を読む。
`Examples.mixed_union_not_equivalent_top` と `mixed_arrow_not_equivalent_top_arrow` は、任意の行関係の下で
`int | str` と top を区別し、その区別が arrow の引数文脈でも保たれることを示す。
条件付き impl・辞書全体の意味を、この head table が実装したという主張ではない。

### `ProducerContextualRecord.producerLe_record_iff` / `fieldLe_record_iff`

任意の行関係、任意の同一 label `l` の record 型と成分について、record 比較は payload の通常の比較と、
`l` を除く tail の field 要求の比較に同値である。任意の hidden label 列の下では、head 自身が hidden なら
payload の比較も不要となる。`Regular.record_reference_iff` / `Regular.record_iff` は任意 graph/具体 regular 型の全深さ版。
tail に渡す観測深さは減らさない。

`singleton_requirement_iff` は、target の rest が旧 width record である同一 label の singleton required demand に対して、
payload の比較だけが必要十分となることを示す。`shadowed_head_equivalent` は任意の同名内側 head の消去で要求同値を保つ。
どちらも hidden field の式の評価を省く主張ではない。

## 4. 全有限 constructor 入力の分岐・Closed・全解 family

この節の graph は slot 数 `n` の有限 graph であり、node 文法は var/base/bottom/top/pair/arrow と両行/
proper record spine/variant。意味型は任意の union/inter と regular 再帰を含む。
presence の exact/optional/default/mask-tail node を黙ってこの文法に含めていない。

### `ContextualNestedModels.saturate_models_iff` / `solve_none_iff`

任意の行前順序、任意の有限 graph `g`、任意の入力辺列 `E`、任意の外部 regular graph `G` と元 slot の割当て `ρ` について、
`ρ` が元の constructor 意味と辺列を満たすことと、実 `saturate g E` の cache を満たすことが同値。
正確な行検査を加えると、任意の `g,E` で実 `solve` の `none` と独立 contextual regular model の不存在が同値となる。
全入力定理に成功・モデル存在・Closed・fuel の前提はない。

### `ContextualBranchSolver.solve_models_exact` / `accepted_closed_capacity` / `solve_nil_iff`

任意の行前順序と正確な行検査、任意の有限 graph `g`、truth/falsity/edge/and/or からなる任意の有限 formula `F`、
任意の独立 regular graph と割当てについて、入力のモデルであることと、実 `solve g F` が返すある枝の cache のモデルであることが同値。

任意の Boolean 行検査、任意の `g,F`、実返却リストに含まれる任意の branch から、
`NestedValueSolver.Closed`、行整合性、cache 長 `≤ n²` を得る。これは constructor/variable の Closed であり、
反例のある旧 all-mask presence cache を流用したものではない。

行前順序と正確な行検査の下で、任意の `g,F` の空結果と独立モデル不存在が同値。

### `ContextualValueBounds.expand_equivalent` / `ContextualCoalescing.coalesceGraph_retraction`

任意の行関係・任意の flat bound problem とその任意の独立 contextual solution `ρ` に対し、
実 `ValueBoundSchemes.expand` に `ρ` を共有 parameter として入れると、全 slot が `ρ` と要求同値になる。
旧 structural solution という前提は不要。

任意の行前順序、任意の finite graph/cache、任意の独立 regular graph と元割当てが rigid constructor の意味と全 cache 辺を満たすなら、
その解の root layer を共有 parameter とした実 `coalesceGraph` が、全 slot・全深さで元解を回収する。
負位置や slot 間の共有を別々の parameter に分離しない。

### `ContextualRegularInference.models_exact` / `instances_exact`

任意の行前順序と正確な行検査、任意の有限 graph と辺列、任意の具体 regular 値割当て `ρ` について、

```text
独立 Models(g,E,ρ)
↔ ∃ cache, solve(g,E) = some cache ∧
   ∃ p : Fin n → RegularInferenceModel.Ty Row,
     ∀ i, solution(g,cache,p,i) ≡ᴾ ρ(i)
```

任意の出力 root と target `T` についても、独立モデルで root が `T` 以下となることと、
実返却 cache のある自由 parameter 具体化が `T` 以下となることが同値である。
cache・成功・元解は公開定理の入力前提ではなく、実計算を指定した結論の側に現れる。
parameter に元の制約を課す predicate は残らない。

### `ContextualBranchInstances.models_exact` / `instances_exact` / `solve_nil_iff`

同じ行の前提、任意の有限 graph/formula/元割当てについて、独立モデルと、
実受理 branch と自由 parameter による実 solution block の全 slot 要求同値が同値になる。
任意の root/target について独立出力 instance と実 family の上方 instance も同値。
空結果は、**同じ具体 inference carrier 内**での独立モデル不存在と同値となる。

## 5. 実 compiler・行求解・source/Core の主型性

### `ContextualTypeConstraintGraph.compile_assignment_exact` / `compile_output_instances_exact`

任意の行前順序、empty/join、元 slot 数、行割当て、型制約列、実 `compile` が返す compiled graph、任意の元値割当てについて、
元制約の充足と、元共有変数を同じ値へ restrict する contextual graph model の存在が同値。
任意 output/target の上方 instance にも同じ保存・反映がある。実 compiler 返却であることを前提にする中間補題であり、
solver 成功は仮定しない。

### `ContextualTypeConstraintInference.infer_correct` / `infer_models_exact` / `infer_instances_exact`

任意の行前順序、正確な rowCheck、empty/join、任意の元 slot 数・行割当て・型制約列について、
変更しない実 fixed-row 入口の全 status を新しい意味で正しく分類する。
supported な制約では、任意の元値割当ての充足 iff 実 family の Models、任意 output/target の元 instance iff 実 family の Instance。
`infer_rejected_iff` は任意入力で rejected iff supported かつ充足割当て不存在。

### `ContextualJointConstraintInference.infer_correct` / `infer_models_exact` / `infer_instances_exact`

任意の行 join 代数とその反対称律、任意の paired 型/行制約について、実 symbolic joint solver の全 status が正しい。
`supported problem = true` を仮定した任意の問題について、任意の元値割当てと行割当てを、
自由な row/value parameter の実 scheme family と一致させる。行割当ては関数として等号で回収し、値型は要求同値で回収する。
任意 output/期待 computation の上方 instance も同値となる。
行代数・意味的 rowCheck・初期の行割当て・solver 解・fuel を実 algorithm へ入力していない。

### `ContextualSourcePrincipalInference.infer_instances_exact`

任意の反対称な行 join 代数、任意の旧 source 式 `e`、旧 executable support checker が true であるという前提、
任意の値/行結果 `c` について、実 `infer e` の contextual Instance と、独立した新 model の `Typing [] e c` が同値。
実 collect/infer/scheme evaluator は旧実装の alias で、Typing に instance の定義を埋め込んでいない。

### `Core.ContextualRequiredInference.principal_exact`

任意の反対称な行 join 代数、任意の Core required term `e`、旧 syntax/support checker が true、任意の結果 `c` について、

```text
Typing [] e c
↔ ∃ P, 実 infer e = inferred P ∧
   ∃ S ∈ P,
   ∃ rows : Fin S.slots → Row,
   ∃ values : Fin S.scheme.size → RegularInferenceModel.Ty Row,
     S.scheme.instantiate rows values S.output ≤ᴾ c
```

最後の computation 比較は、値型に contextual 順序、行に元の行順序を使う。
scheme 具体化の行と要求結果の行が等しいという主張ではなく、通常の行 subsumption を含む。

### `recordFree_principal` / `recordFree_rejected_iff` / `recordFree_ne_unsupported`

任意の反対称な行 join 代数、任意の構文的 RecordFree term `e`、任意の結果 `c` について、上の principal iff が成立する。
同じ断片の任意 `e` について、rejected iff 任意結果で型付け不能であり、unsupported は出ない。
support checker の成功・推論成功・solver 解・cache・fuel を前提にしない。
未束縛変数や不正な projection を構文から除外せず、拒否完全性で扱う。

### `producerInstance_iff` / `legacy_source_typing_exact` / `legacy_core_typing_exact`

任意の行 join 代数・任意の旧 Result・任意結果で、今回の Instance と前の
`Core.ProducerContextualInstances.Instance` は同じ scheme と同じ全 parameter を直接評価する定義であり、iff は `rfl` で閉じる。

行の反対称律を加え、任意の旧 supported source と任意結果について、この Instance と新しい独立 source/Core Typing が同値。
これが以前残っていた逆向き完全性である。

### `source_typing_exact_modulo` / `core_typing_exact_modulo`

任意の反対称な行 join 代数、任意の旧 supported 式 `e`、任意の旧 carrier 上の結果 `(T,r)` について、

```text
新 Typing [] e (T,r)
↔ ∃ U, 旧 Typing [] e (U,r) ∧ U ≡ᴾ T
```

反映先の結果行は文字通り同じ `r`。旧 instance の保存と合わせ、決定46の形になる。
旧 `no_semantic_legacy_instance_exact` は変更していない。
将来の presence 共通モデルでは、旧結果型の embedding の範囲で同じ契約を再度接続する必要がある。

## 6. 由来のない tail 循環と具体 mask family

### `PositiveEquationElimination.solve_sound` / `solve_retract` / `solved_instances_exact`

任意の有限座標全列、任意の var/atom/bottom/top/union/inter の正方程式系、任意の atom 命題割当てについて、
全自由 parameter から計算した有限式は不動点であり、任意の独立不動点を同じ parameter で回収する。
任意割当て `v` について `F(v)=v` iff ある自由 parameter の実消去結果が `v`。
入力の source 由来、guardedness、成功、解の存在、fuel は前提にない。

### `PresenceTailElimination.solve_mask` / `coordinates_length`

任意の自然数 slots/labels、任意の finite Body graph、任意の自由 concrete layer parameter family、任意 slot と内部 mask に対し、
解 layer をその mask で mask した**構文**が、対応する mask 座標の解に等しい。
座標数は `slots * 2^labels`。深さごとの任意述語 family を free parameter と仮定せず、一つの layer から mask family を作る。

### `PresenceTailRegular.solveGraph_realizes`

任意の自然数 slots/labels、任意の型 Index、任意の graph
`Fin slots → Body labels (Fin slots) (Fin slots)`、任意の外部 regular graph、任意の
`Fin slots → Layer Index` parameter に対して、実 solveGraph が独立 Realizes を満たす。
Realizes は任意の深さ、任意の外側 Nat mask、内部有限 mask、slot、data 値について元の Body 方程式を要求する。
同深さの tail ref の自己循環・相互循環を許し、payload 参照でだけ観測深さを減らす。

### `PresenceTailRegular.solveGraph_retract` / `solved_instances_exact`

同じ任意の入力と任意の独立候補 graph `G`、root map `r` について、

```text
Realizes(g,G,r)
↔ ∃ p : Fin slots → Layer Index,
   ∀ depth hidden i value,
     observeMasked(solveGraph(g,G,p), depth, hidden, inl i, value)
       ↔ observeMasked(G, depth, hidden, r i, value)
```

存在 parameter は、すべての深さ・外側 mask・slot・値の量化の外側にある。
内部 mask の語彙は有限だが、外側 mask と atom/parameter 中の label は任意の Nat を許す。
この文法には関数・行・exactEmpty・whole default がなく、Body.record は要求側の演算である。

## 7. 計数・cache・増分更新の定理

### 分岐と cache

`ContextualBranchCost.branches_length_le` / `branch_length_le` / `branches_total_edges_le` は、任意 formula F、
その either node 数 D、edge leaf 数 E について、実枝数≤2^D、任意実枝長≤E、全辺 occurrence≤2^D E を示す。
任意の行検査と slot 数 n の任意 graph について、`solve_length_le` / `accepted_total_cache_edges_le` は、
実受理枝数≤2^D、実受理 cache 長総和≤2^D n²。意味的 rowCheck exactness も前提にしない。
`duplicateTruth_counts` は任意 k に対し、k 個の `truth ∨ truth` の積が E=0 でも正確に2^k枝を列挙すると示す。

### selection

`MethodResolutionCost.unknownCount_bound` は任意 scope/name に対して可視 role 数 R で `1+2R`、
既知 receiver の `knownCount_bound` は任意型/名前/fallback に対して型 node 数 V で `1+V` 以下。
各 value theorem は、成功・欠落・曖昧を含めて既存 resolver と同じ値を返すことを示す。

`MethodResolutionIndex.resolveNamesCount_exact` は、任意の有限 catalog・可視 role 列・名前列について、
同じ role/name が同じ declaration を表す関数性を前提に、index による答えと旧 unknown resolver の答えを一致させる。
`resolveNamesCount_bound` は任意の既に可視な declaration 列 D 件と名前列 N 件で、費用≤3D+2N。
この上界には関数性・成功は不要。visibility filtering と map の内部実装の費用は別である。

### scheme 具体化

`InferenceSubstitutionCost.instantiate_value` は任意の stored scheme と置換先 computation について既存の実具体化と値一致。
`instantiate_bound` / `instantiate_size_bound` は、scheme の全 node 数 N、binder 深さ H、
置換先の値/行を合わせた node 数 K に対し、費用≤N(1+max(2,K)H)≤N(1+max(2,K)N)。
成功や source の再推論は前提にしない。

### 簡約の全4段階

`TypeSimplificationCheckCost.symbolicCount_value` は任意の型項対で実 symbolicCheck と同じ Bool を返す。
型/行等号と record spine の再帰走査も計数する。
`symbolicCount_size_bound` は任意の自然数 S と、行込み node 数の和が S 以下の任意の二型項について、
費用≤B(S)=(S+1)128^S。外部 fuel・成功は仮定しない。

`TypeSimplificationCost.simplifyAllCount_value` / `simplifyAllCount_bound` は、任意 n と任意 TyTerm(Fin n) で、
実 simplifyAll と同じ値を返し、行込み入力 node 数 M に対して次の明示上界を持つ。

```text
B(M)     = (M+1)*128^M
V(M)     = 1+M*(M+1)+M*(2+2*M)
W(M)     = 7+2*M+B(2*M)
G(M)     = 3+10*M+2*B(4*M)
SA(n,M)  = 4+10*n+4*n*(W(M)+1)
GA(n,M)  = n+n*(1+2*n)+n*n*(G(M)+1)
Total    = 3+2*V(M)+SA(n,M)+GA(n,M)
```

候補 inventory のコピーと map/product/append、4n個の scalar sandwich、n²個の merge の全検査を数える。
inventory `finRange` の library 内 materialization、ID bit cost、allocator は含めない。
constructor dispatch と有界個の局所検査を一単位とし、明示した conj/disj 等は別に数える。
全原始 Boolean 命令を厳密に一単位ずつ数える主張ではない。

`simplifyAllCount_instances_exact` は、任意の行前順序・empty/join・固定行割当て・型項・期待型について、
計数付き結果と元項の旧 StructuralBase の Instances が同値。新 contextual carrier への意味の移送は別の義務である。

### 合法 SCC schedule

`ModuleScheduling.run_legal` / `run_build_exact` / `schedule_independent` は、任意の pure compile、source/key 表、
`Dependencies = (i : Nat) → List (Fin i)`、空 store からの任意合法 schedule に対して成立する。
合法とは、各 node が未処理で、直接依存がすべて先に処理済みであること。
実 store の依存 artifact を読んだ実行が完走し、同じ node 集合の二合法順序なら同じ artifact 表に到達する。
全 node を含めれば既存の全体 build と一致する。
`run_once_bound` は全 ID が N 未満なら実 compile 呼出 trace が重複せず N 以下と示す。

`MethodResolutionScheduling.schedule_independent` は、任意の局所 pure prepare、source/key と依存表、同じ node 集合の二合法順序で、
実行中に作る export/receiver/scope/fallback を含む snapshot と実 resolve の三状態結果が一致すると示す。
固定 snapshot や SameFacts は入力前提でない。
`run_selection_exact` は任意の処理済 node・任意の位置・任意 reference について、unique になること iff 独立 Selects。
`scheduled_once` は実 compile 呼出の高々一回性を保つ。

### cache と増分 build

`ModuleIncremental.dirty_exact` は任意の変更 flag・依存 graph・node について、実 dirty 判定 iff 独立した逆依存経路 Affected。
`rebuild_changed_graph_exact` は任意の純粋 compile、新旧 source/key・新旧依存 graph について、
clean flag の node の自身の source/key と依存列が不変であり、cache が旧全体 build なら、実増分 build と新全体 build が等しい。
`rebuild_normal_forms` は任意の決定的 normalize を適用した後も等しい。normalize の完全性は仮定も結論もしない。

`ModuleInterfaceCache.rebuild_exact` は、source/key と Interface の decidable equality、任意の純粋 compile、
任意の新旧 source/key と graph、正しい旧 build に対して、入力等号を実検査する cache 再利用と新全体 build を一致させる。
実際に入力が変わった node だけ compile し、source が変わっても生成 interface が同じ地点で下流の再計算を止められる。
呼出は重複せず node 数以下。source からの依存抽出と完全な型標準形の接続はこの定理には含めない。

## 8. 閉じていない部分と正確な次の契約

完全な量化と prospective Lean 風 statement は
[残契約](../design/2026-11-07-m1-remaining-contracts.md) に記す。次の名前は未実装契約の仮名であり、追加公理ではない。

1. **共通 carrier:** 具体的な要求意味から common_subtype_exact を構成し、任意の旧 regular S,T について
   embedding 後の比較 iff 現 contextual 比較を示す。exactEmpty/width/required、任意引数の arrow iff、
   strict whole default image を同じ carrier で示す必要がある。
2. **default の完全分解:** 任意 label と任意 source/fallback/target 型について、default の比較 iff
   実 inspector のある有限枝の独立子 obligation が成立、を示す。元の未分解比較を結論側に再包装してはならない。
3. **mask/tail と producer 順序の接続:** 任意自由 parameter と任意 mask に対する具体評価則を構成し、
   任意 finite presence graph・任意元割当てで、実 branch/tail compiler の全モデルを保存・反映する。
   現 positive data-demand 解と contextual constructor 解の二 family を同じ carrier で結ぶ必要がある。
4. **全 source の solved family:** 任意の対象 source と任意結果について、生成制約の独立 Typing 完全性を具体共通 model へ適用し、
   existential 制約を残さない全自由 parameter family に接続する。record 構築・recordDefault を含め、
   support checker 結果・推論成功・solver 解・fuel を公開前提にしない主型性／拒否 iff／unsupported 排除が必要。
5. **決定46の共通モデル版:** 任意旧 supported 式と任意旧結果型の embedding について、旧 instance を保存し、
   新 instance から同じ結果行の要求同値な旧 instance を回収する。任意の新 exact 型へ対象を勝手に拡大しない。
6. **完全な interface 標準形:** role/nominal/effect/regular graph を含む任意二 interface で、意味的同値 iff 同じ実 canonical encoding。
   現 grouping は `normalize_not_complete` の反例があり、この義務を満たさない。
7. **source からの局所性:** 任意 source の参照収集/SCC 縮約が完全な依存表を作ることと、実 SCC solver の確定結果が
   source/key と全依存 artifact だけを読む pure prepare で表せること。抽象 DAG の順序独立性から、この二点を省略しない。
8. **性能の残り:** 共有 DAG・lazy branch・重複排除の意味と費用、map/ID/allocator の具体実装費用、
   新 contextual instance での既存簡約保存、完全標準形の serialization 保存。Rust benchmark の実測は今回行っていない。

`EOFNoDefaulting.accepted_export_independent` は同じ入力条件で両 finish が成功した場合の公開型の一致。
追加 impl による曖昧性を否定しないため、公開型 cache と EOF 診断/辞書 artifact の依存を混同しない。

## 9. Rust 前段設計

[Rust oracle plan 第7節](../design/2026-11-06-rust-oracle-plan.md) に、次を追加した。

- arena による安定 ID、intern した path、持続的な module/scope map と代案。
- 本体の lowering 完了を待つのではなく、宣言と本体参照の事前収集で SCC を確定する境界。
- role/method-name index の missing/unique/ambiguous を保持し、SCC 確定時に selection を一度解決する設計。
- モジュールまたは import SCC 単位の依存完了と一般化、captured slot・行・名目 identity・辞書依存を含む cache key。
- 最初の三群の benchmark: selection の入力規模、lowering 各段階の再走査と allocation、
  依存 chain/fan-out/無関係 sibling の変更伝播。snapshot・cache・量化の理論と、まだ接続しない実装の境界。

## 10. 検証と問い

全体 `lake build` と `lake env lean --trust=0 Audit.lean` が exit 0。追加498 public theorem の `#check @...` も exit 0。
Audit は既存の Lean 基本公理 `propext` / `Classical.choice` / `Quot.sound` の範囲で、追加公理、sorry、native_decide は使っていない。
既存の定理の主張、旧 `{}` の width 意味、テスト期待値は変更していない。
README の証明範囲は source/Core と tail を別々に読み直し、独立レビューの指摘を反映した。

`notes/questions/` に新しく積んだ問いは **0件**。
内部の mask・layer・cache・schedule・費用単位の選択、理由と代案は設計メモに記録した。
回答済み Q1/Q5 と Q4 の明示した仮の前提は維持する。

作業 branch は `integration/m1-solver` のみ。`integration/types` / `yulang3` へは push しない。
作業中に `origin/yulang3` を複数回 fetch し、取り込み済みであることを確認した。
