# 漸近的型付け風 monomorphization plan

作成日: 2026-05-23

## 目的

`yulang-runtime` の現行 monomorphize / runtime type finalization は、主型の展開、
local refresh、型変数代入、既存 specialization への寄せ、cast 挿入、hole default、
到達性 prune が絡み合っている。結果として、IR の一部へ新しい処理を挟むたびに、別の
段階の暫定型や古い default が再び制約として扱われ、局所的な修正が増える。

この文書では、ユーザー案の「漸近的型付け風処理」を、runtime IR の新しい単一化・
単相化アルゴリズムとして整理する。中心に置く考え方は次の通りである。

- top-level 式は実行対象なので、最終的に閉じた単相型を持つ。
- top-level から到達する多相関数は、実際の呼び出し引数から単相化できる。
- 多相関数本体全体を一度に global unify しない。
- call site ごとに、主型のうち引数に関係する最小グラフだけを先に閉じる。
- 閉じた主型を持つ関数 instance の内部だけを、同じ下界解決規則で次に閉じる。
- すべての型変数は、同一 instance 内で観測された下界から materialize する。
- 下界で埋めた結果、required upper と合わない場所だけに cast / diagnostic を置く。

ここでいう「漸近的」は、全 IR を一気に閉じるのではなく、top-level 実行要求から見て
必要になった多相境界を内側から順番に閉じていく、という意味で使う。

## 評価

この案は、現在の `monomorphize-type-graph-pipeline-plan.md` の下界仮説と相性がよい。
特に、`Expr.ty` に残った古い暫定型を全体制約として再利用する経路を断てる点が大きい。
関数 instance の境界ごとに graph を切るため、別 call site の `a = int` と `a = bool`
が混ざる失敗も避けやすい。

一方で、この案を成立させるには、不変条件をかなり明確にする必要がある。特に次の点は
曖昧にすると旧 pipeline と同じように壊れる。

- 「一番内側にいる多相関数」の定義。
- 関数値を返す式、高階引数、closure capture をどう instance 境界へ入れるか。
- 再帰関数と相互再帰関数をどう閉じるか。
- effect row / handler / resumption の下界を、値型と同じ graph に混ぜるか、別 lane にするか。
- role associated type を required upper からではなく receiver の下界から復元できるか。
- `Never` / `Any` / `Unknown` / `mzero` のような inhabited lower を持たない型を候補生成から外せるか。
- cast 挿入が「型を合わせるための後段上書き」ではなく、closed lower と upper audit の衝突処理になっているか。

したがって、旧 `principal_unify` を直接置き換えるより、新 crate でアルゴリズムの境界を
明確にしたうえで、小さい fixture から移植する方針がよい。

## crate 境界

すでに `yulang-runtime-ir` が runtime IR の所有 crate として存在するため、新しく切る crate は
IR ではなく finalization 専用にする。

候補名:

- `yulang-runtime-finalize`
- `yulang-monomorphize`

推奨は `yulang-runtime-finalize`。責務を monomorphize だけに閉じず、型閉鎖、cast 挿入、
hole default、specialization planning まで持てるためである。

依存方向:

```text
yulang-typed-ir
  -> yulang-runtime-ir
      -> yulang-runtime-finalize
          -> yulang-runtime
          -> yulang-vm
```

実際には `yulang-runtime` が lowering / validation / diagnostics も持っているため、移行中は
次の過渡構成になる。

```text
yulang-runtime-ir
  -> yulang-runtime-finalize
  -> yulang-runtime
```

`yulang-runtime` は当面、lowering と旧 compatibility entrypoint を持つ。新 finalizer が安定したら、
`yulang-runtime::monomorphize` は薄い adapter に寄せる。

## 入力と出力

### 入力

新 finalizer の入力は、runtime lowering 済みの `Module` と、型推論から持ち込まれた
構造化 evidence である。

最小入力:

- `yulang_runtime_ir::Module`
- binding scheme
- `ApplyEvidence`
- `TypeInstantiation`
- role impl graph
- root / top-level expression list
- runtime lowering が持つ thunk / effect / handler の構造

禁止する入力:

- source path の文字列を型規則として読む情報
- fixture 名
- std helper 名だけを通す分岐
- 古い `Expr.ty` を provenance なしに強い制約として扱うこと

`Expr.ty` は初期 slot の注釈としては読めるが、下界・上界・equality のどれに相当するかを
provenance 付きで分類できない場合、候補生成の根拠にしない。

### 出力

出力は closed runtime module と structured report である。

- closed `Module`
- emitted specialization list
- inserted cast list
- unresolved holes
- upper audit conflicts
- residual polymorphic bindings
- finalization profile

VM に渡す module は、型変数・effect 変数・未解決 role requirement を持たない。残る場合は
VM validation ではなく finalizer diagnostic として落とす。

## 中心データ構造

### `TopLevelDemand`

実行対象の root / top-level expression から始まる閉じた要求。

```text
TopLevelDemand {
  root_id,
  expected_value,
  expected_effect,
}
```

top-level 式が型注釈を持つ場合はそれを expected として使う。持たない場合は、runtime 実行に
必要な最小 shape まで lowering / inference が決めていることを前提にする。ここが閉じない場合は、
monomorphize の問題ではなく top-level inference の未解決として扱う。

### `InstanceKey`

単相化 instance の同一性。

```text
InstanceKey {
  original_binding,
  closed_param_types,
  closed_result_type,
  closed_effect,
  captured_env_shape,
}
```

最初は `original_binding + closed argument lower snapshot` から作り、body finalization 後に
result / effect を audit する。result / effect が key と矛盾する場合は同じ instance を
書き換えず、conflict として止める。

### `PrincipalGraph`

binding scheme / principal type から作る小さい graph。関数本体ではなく、主型だけを扱う。

責務:

- type param slot を作る。
- param / result / effect slot を作る。
- declared scheme の構造 edge を作る。
- role associated projection の入口を作る。
- call site の実引数型を param slot の observed lower として流す。

この graph は instance key を作るためのものなので、関数本体の local slot を持たない。

### `BodyGraph`

単相化された binding body 内の graph。`PrincipalGraph` で閉じた param lower を入口として使う。

責務:

- local binding slot
- expression value slot
- expression effect slot
- pattern slot
- apply callee / argument / result slot
- handler / resume slot
- capture slot

body 内でさらに多相 call が見つかった場合、直接本体へ入らず `NestedPolymorphicCall` として
finalization queue に積む。戻り値 slot には、作られた instance の closed result を lower として流す。

### `LowerSolution`

observed lower から materialize した solution。

```text
LowerSolution {
  slot_candidates,
  type_var_substitutions_by_scope,
  effect_var_substitutions_by_scope,
  associated_type_substitutions_by_scope,
}
```

候補生成は lower の join と equality closure だけで行う。required upper は候補生成に使わず、
後段の audit で検査する。

## 処理順

### 1. top-level demand を作る

root と top-level expression を走査し、実行対象の要求を作る。

不変条件:

- top-level demand は閉じている。
- top-level demand は多相 scheme ではない。
- 閉じていない場合は、ここで `UnresolvedTopLevelType` を返す。

### 2. top-level 式を外側から走査し、多相 call frontier を見つける

top-level expression の中で、単相化が必要な多相 binding call を検出する。

ここでいう frontier は、「この call を閉じないと親式の lower solution が閉じない境界」である。
構文木の単純な最深ノードではなく、型依存 graph 上の境界として見る。

例:

- `f(g(x))` では、`g(x)` の result が `f` の引数下界になるため、`g` が先。
- `map(f, xs)` では、`map` の主型を閉じるには `f` と `xs` の引数 shape が必要になる。
  ただし `f` 自体が多相値なら、`map` の body finalization 中に element 型から `f` の
  instance を作る。
- `let h = polymorphic_fn in h(1)` では、binding reference の slot を経由して call frontier を張る。

frontier 検出では path 文字列を見ない。callee が `BindingId` / `DefinitionId` / role method /
intrinsic kind のどれかとして解決済みであることを前提にする。

### 3. 主型だけを graph 化し、実引数の下界で解く

frontier call ごとに `PrincipalGraph` を作る。

入力:

- callee の declared scheme
- call site の argument lower
- call site の expected result lower があればそれ
- call site の allowed effect upper

処理:

1. scheme の type vars を call-site scope へ freshen する。
2. param slot へ実引数の closed lower を流す。
3. result の期待 lower があれば result slot へ流す。
4. equality closure と lower join で type var substitution を作る。
5. associated type は receiver / input lower が閉じた場合だけ射影する。
6. required upper を audit する。

出力:

- `InstanceKey`
- closed param substitutions
- provisional closed result / effect
- principal conflicts

ここでは関数本体を見ない。主型が閉じない場合は、body 側で補える問題ではないため、
`IncompletePrincipalInstance` として止める。

### 4. 単相 instance 名を予約する

`InstanceKey` ができたら、先に別名を予約する。

目的:

- 再帰 call が同じ instance を参照できる。
- 相互再帰の cycle を queue 上で扱える。
- body finalization 中に同じ call site が再出現しても重複生成しない。

予約状態:

```text
InstanceState::Reserved
InstanceState::Finalizing
InstanceState::Finalized
InstanceState::Failed
```

`Reserved` の instance を body から参照する場合は、closed scheme だけを使う。本体がまだ
emit されていないことを理由に別の型候補を合成しない。

### 5. body graph を切り出して、引数下界を埋める

original binding body を clone し、instance-local な `BodyGraph` を作る。

入口 lower:

- param pattern / local param slot へ closed param type
- capture がある場合は capture slot へ call site から得た closed env type
- recursive self reference へ予約済み instance の closed function type

処理:

1. body の expression / pattern / local binding slot を作る。
2. declared annotation は required upper または equality として分類する。
3. 実際に生成された value / effect を observed lower として流す。
4. nested polymorphic call は `NestedPolymorphicCall` として queue に積む。
5. nested call が finalized したら、その result / effect を body graph の lower として継ぎ足す。
6. graph が安定するまで instance-local worklist を回す。

body graph は他の instance と共有しない。同じ original binding でも call site が違えば、
lower evidence は別 graph に入る。

### 6. 型変数を下界で materialize する

`LowerSolution` を作り、全 slot の型変数を同一 scope の下界で埋める。

規則:

- `a = b`, `b = int` は `a = int` まで閉じる。
- cycle は無限展開しない。閉じない cycle は residual open として残す。
- `Never` / `Any` / `Unknown` / bottom-like lower は候補生成から外す。
- numeric widening などの互換 join は `type_compatible` 相当の構造化規則へ寄せる。
- 別 call-site scope の同名 type var へ伝播しない。

この段階で closed にならない slot は、ただちに `unit` などで埋めない。`UnresolvedLower`
として report に残し、hole default が責務を持つ段階まで送る。

### 7. upper audit と cast 挿入

materialized lower を required upper に照合する。

結果:

- lower が upper を満たす: そのまま採用。
- cast / coercion で説明できる: edge provenance に基づき cast を挿入。
- 説明できない: structured conflict として失敗。

cast 挿入の禁止事項:

- result を expected に合わせるために後段で型を書き換える。
- callee 名や std path によって cast を選ぶ。
- upper を使って候補型そのものを作る。

cast は、closed lower と required upper が両方あり、既存の coercion 規則で説明できる場合だけ
挿入する。

### 8. instance を emit する

body graph が closed になったら、予約済み alias の body と scheme を確定する。

emit する binding:

- type params は空。
- scheme は closed param / result / effect から作る。
- body 内の多相参照は finalized instance alias へ置き換える。
- generic original binding は runtime module へ直接出さない。ただし、他の未確定 instance が
  参照している間は finalizer 内部 table に保持する。

### 9. 次の frontier へ進む

top-level demand / instance queue が空になるまで 2 から 8 を繰り返す。

終了条件:

- すべての top-level root が closed expression になっている。
- final runtime module に generic binding が残っていない。
- residual role requirement がない。
- residual type/effect var がない。
- unresolved hole が policy に従って埋まっているか、diagnostic として返っている。

## 再帰と相互再帰

再帰では、instance alias を先に予約する必要がある。

単純再帰:

```text
fact(int) -> int
```

`fact__int` を `Reserved` にしてから body graph を作る。body 内の `fact(n - 1)` は同じ
`InstanceKey` を参照するため、新しい graph を作らない。

相互再帰:

```text
even(int) -> bool
odd(int) -> bool
```

`even__int` finalization 中に `odd__int` が必要になったら、`odd__int` を予約して queue に積む。
`odd__int` から `even__int` が見えた場合は既存予約を使う。

注意点:

- result / effect が主型だけで閉じない再帰は、body から result lower が戻るまで仮置きが必要。
- 仮置きは `Unknown` ではなく `PendingInstanceResult` として扱い、候補生成には使わない。
- cycle 完了後に result / effect が閉じない場合は、hole default ではなく再帰 instance の
  diagnostic にする方がよい。

## 高階関数と関数値

高階関数では、「多相関数値」をそのまま runtime value として閉じるのか、呼び出し地点で
instance 化するのかを分ける。

初期方針:

- runtime に多相関数値を渡さない。
- 関数値 slot は closed function type を持つ。
- 多相 binding reference が関数引数として渡される場合、受け側の body finalization で
  実際の element / argument lower が分かった時点で instance 化する。
- 受け側が関数を呼ばない場合、関数値は opaque closed function value として残せるかを
  別途検証する。

この方針により、`map(id, [1, 2])` の `id` は `map` の主型だけで無理に閉じず、`map` body
内の apply edge で `id__int` を作る。

ただし、関数値を data structure に保存して後で呼ぶ場合は、保存時に closed function type が
必要になる。ここは初期 milestone では unsupported diagnostic にしてよい。

## effect row / handler

effect は value type と同じ graph に置けるが、lane は分ける。

- performed effect: observed lower
- allowed handler row: required upper
- handled effect subtraction: graph transform
- resumption result: value lower と effect lower の組

`Never` effect は bottom-like lower として候補生成から外す場面と、closed empty effect として
採用する場面がある。ここは source role で区別する。

- unreachable / `mzero` 由来: lower candidate にしない。
- handler 後に実際に empty と確定した effect row: closed candidate にする。

この区別を `EffectEvidenceKind` として持たないと、旧 pipeline のように `Never` / `Any` の
default が別段階へ漏れる。

## role associated type

role associated type は required upper から型を作らない。receiver / input lower が閉じた場合にだけ、
role impl graph から associated type を射影する。

処理:

1. role requirement の input slot に lower があるか見る。
2. impl input と構造照合する。
3. 一意な impl があれば associated type を射影する。
4. impl input の structural substitution も同じ scope の lower evidence として入れる。
5. 複数 impl が候補になる場合は ambiguity。
6. input lower がない場合は upper-only dependency として残す。

これにより `Index (lines 'e): type value = ref 'e str` のような associated result は、
`value = ref<t, str>` だけでなく、impl input から得た `'e = t` も同じ scope で閉じられる。

## hole default

hole default は最後の一箇所だけで行う。

初期 policy:

- value hole: `unit`
- closed empty effect hole: `Never`
- open effect row hole: context を見て `Never` / `Any` を選ぶ

ただし、top-level demand、principal graph、reserved instance key に残る hole は default しない。
それらは finalizer の入口不変条件違反または principal incompleteness として扱う。

## diagnostics

finalizer は表示文言ではなく structured error を返す。

候補:

- `UnresolvedTopLevelType`
- `IncompletePrincipalInstance`
- `AmbiguousLowerJoin`
- `UpperAuditConflict`
- `UnsupportedPolymorphicValue`
- `RecursiveInstanceDidNotClose`
- `AmbiguousRoleImpl`
- `MissingRoleImpl`
- `UnresolvedAssociatedType`
- `ResidualRuntimeTypeVar`
- `ResidualRuntimeEffectVar`
- `UnresolvedHole`

diagnostic formatting は `yulang-runtime` 側か dedicated diagnostics module に置く。
solver 内で表示用文字列を組み立てない。

## migration milestones

### Milestone 0: crate skeleton

- `crates/yulang-runtime-finalize` を追加する。
- 入力は `yulang_runtime_ir::Module`。
- 出力は `FinalizeOutput { module, report }`。
- 既存 `yulang-runtime` からはまだ呼ばない。

### Milestone 1: principal graph only

- binding scheme から `PrincipalGraph` を作る。
- closed 引数 lower から `InstanceKey` を作る。
- fixture は小さい関数適用だけにする。
- body はまだ emit しない。

テスト:

- `id(1)` が `id__int` key を作る。
- `id(1)` と `id(true)` が別 key になる。
- 別 call site の type var lower が混ざらない。

### Milestone 2: body graph without nested polymorphism

- 単相 body の local / apply / block を graph 化する。
- param lower から body result を閉じる。
- cast なしで閉じる小さいケースを通す。

テスト:

- `let inc x = x + 1; inc(2)`
- local let
- tuple / record / variant の構造下界

### Milestone 3: nested polymorphic call queue

- body graph から nested call を queue に積む。
- finalized instance result を body graph に戻す。

テスト:

- `f(g(1))`
- `let h x = id(x); h(1)`
- 同じ generic を別型で 2 回呼ぶ top-level expression

### Milestone 4: recursion

- `Reserved` / `Finalizing` / `Finalized` state を入れる。
- simple recursion と mutual recursion を扱う。

テスト:

- closed annotated recursive function
- mutually recursive bool/int case
- result が閉じない recursion の diagnostic

### Milestone 5: roles and associated types

- receiver lower から impl を選ぶ。
- associated type を同一 scope の lower として射影する。

テスト:

- `Index` associated value
- `Display (list int)`
- impl ambiguity
- missing impl

### Milestone 6: effects and handlers

- value lane と effect lane を分ける。
- performed effect lower と allowed effect upper を audit する。
- handler subtraction を graph transform として入れる。

テスト:

- effect-free function
- handled effect
- resumption result
- `mzero` / unreachable が lower candidate にならないこと

### Milestone 7: cast and hole default

- upper audit conflict から cast を挿入する。
- final hole default を一箇所に集める。

テスト:

- int / float widening
- branch merge cast
- unresolved top-level hole が default されず diagnostic になること

### Milestone 8: adapter integration

- hidden env var で `yulang-runtime-finalize` を呼ぶ。
- 旧 pipeline と closed module / VM result を比較する。
- 差分 report を fixture 化する。

候補 env var:

- `YULANG_EXPERIMENTAL_ASYMPTOTIC_FINALIZE=1`

## 既存 pipeline から移さないもの

最初から移さないもの:

- 旧 demand-driven fixpoint の alias cleanup。
- `principal_unify` 内の局所 fallback。
- path 文字列に依存する型 projection。
- validation を通すための後段 type rewrite。
- generic impl member を runtime module に残す reachability workaround。

これらは新 finalizer の diagnostic / graph edge / reachability policy へ分解してから移す。

## 成立条件

この設計が成立したと言える条件:

- top-level から到達する runtime module が closed になる。
- 同じ original generic でも call site ごとの lower が混ざらない。
- 主型が閉じない場合に、body 側で取り繕わず diagnostic になる。
- lower 候補と upper audit が分かれている。
- cast が conflict にだけ反応する。
- final runtime module に residual generic binding が残らない。
- VM validation が型閉鎖の責務を持たない。
- 名前・module path・fixture 名を変えても、同じ構造なら同じ instance が作られる。

## 反証条件

次が見つかった場合は、この設計か下界仮説を見直す。

- receiver / argument / result / effect のどこにも observed lower がないのに、runtime 実行に
  必要な concrete type を upper だけから作る必要がある。
- 多相関数値を runtime value として保持しないと、既存言語機能を表現できない。
- recursive instance の result / effect が主型と body lower の両方から閉じられない。
- associated type が receiver lower と impl graph から一意に復元できない。
- cast 挿入なしでは閉じない箇所が、仕様上の coercion ではなく型推論の代用になっている。

ただし、最初に upper-only が出ても即反証ではない。graph construction が本来の lower evidence を
落としている可能性を先に疑う。

## 次にやること

1. `yulang-runtime-finalize` の skeleton を作る。
2. `PrincipalGraph` / `InstanceKey` / `FinalizeOutput` だけを定義する。
3. 小さい fixture で `id(1)` と `id(true)` の instance key 分離を固定する。
4. 既存 `TypeGraph` preview から reuse できる lower join / recursive substitution helper を
   runtime crate 依存なしの場所へ出す。
5. 旧 `principal_unify` の修正は止め、必要な観測だけを `notes/progress/daily/2026-05-23.md` に残す。
