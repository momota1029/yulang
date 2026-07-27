# concrete subtype fallthrough closure 設計

日付: 2026-07-28

状態: **ユーザ承認済み（2026-07-28）**。実装を認可する。

調査基準は `175db5b609b3`。本設計は、既に再現・確定済みの soundness gap を前提に、
どの concrete-head pair を拒否し、どの representation bridge を残し、どの段階で
診断するかを決める。反例の再調査や、同形 subtype 規則の再設計は行わない。

## 0. 決定の要約

本設計の決定は次の通り。

1. inference の `step_subtype` と specialization の `TypeGraph::process_subtype` の両方を
   fail-closed にする。`check` が source diagnostic を返すことと、specialize が独立に
   不正な IR を拒否することは、どちらも今回の soundness fix に含める。
2. fixed concrete head は `Con`、`Fun`、`Tuple`、`Record`、`PolyVariant`、`EffectRow`
   の六つとする。両辺がこの集合に入り、同形 branch または明示した bridge に該当しない
   ordered pair はすべて拒否する。
3. `OpenVar`、`Union`、`Intersection` は fixed concrete head に含めない。candidate
   resolution 前に正しい alternative を失わないよう、従来どおり deferred とする。
4. `Any` は Top、`Never` は Bottom として既存規則を維持する。未解決を `Any` へ落とす
   fallback は追加しない。
5. `Con -> Record` は nominal `struct` に限って metadata-driven に検査する。
   `Record -> Con` は拒否する。anonymous record を nominal value にする操作は subtype
   fallthrough ではなく、明示された constructor が所有する。
6. `Con -> EffectRow` は、その `Con` が登録済み effect family のときだけ singleton row
   に正規化し、既存 row comparison へ送る。`EffectRow -> Con` と non-effect `Con ->
   EffectRow` は拒否する。
7. inference の source-facing code は新設せず、既存の
   `yulang.unsatisfied-subtype` を再利用する。内部には inference 用の構造化された
   shape-mismatch diagnostic を追加する。
8. generic `Coerce` の emission も今回の project の最終防御 slice に含める。明示的に
   support された boundary kind 以外は emission 時に `UnsatisfiedSubtype` として拒否し、
   subtype solver の将来の見落としを bare coercion に変えない。

## 1. 問題

### 1.1 確定済みの soundness gap

inference の `crates/infer/src/constraints/machine/propagate.rs` にある
`step_subtype` と、specialization の
`crates/specialize/src/specialize2/type_graph.rs` にある `process_subtype` は、
明示 branch に入らない subtype pair を成功扱いにする。

2026-07-26 の `9d8217d3` は、specialize で concrete non-tuple value を tuple parameter
へ渡す一方向を閉じた。しかし、同じ原因を持つ次の cross-shape pair は残っている。

- integer value と function requirement
- function value と nominal scalar requirement
- tuple value と nominal scalar requirement
- polyvariant value と nominal scalar requirement
- record value と function requirement
- anonymous record value と nominal struct requirement

これらは ordinary surface program から到達し、`check` が診断せず、`run` が宣言型と異なる
root value を返すことまで確認済みである。

原因は runtime value の変換不足ではない。どの変換規則も成立していない concrete pair を、
inference と specialization がともに「処理なしの成功」としたことにある。したがって修正位置は
formatter や runtime ではなく、両 subtype decision point である。

### 1.2 二つの正当な representation relationship

cross-shape を一律拒否すると、次の二つを壊す。

#### nominal struct と record-shaped body

`struct` の runtime body は record であり、constructor と field projection がその境界を
所有する。正当な向きは次である。

```text
explicit constructor: Record(fields) -> NominalStruct
field projection:     NominalStruct -> FieldType
```

ここから `Record <: NominalStruct` という一般規則は導けない。anonymous record を nominal
struct として受理してはならない。一方、nominal struct が要求された record field を持つかを
調べる `NominalStruct <: Record(requirements)` は、projection metadata に基づけば正当に
判定できる。

#### effect family と singleton effect row

effect-family `Con` は、一つの effect item を持つ row として正規化できる。
ただし「`Con` という形なら effect」と見なしてはならない。act declaration、synthetic var
effect などから作られた structured effect-family certificate が必要である。

## 2. `Con -> EffectRow` の specialize 到達性

### 2.1 確認した call order

`effect_candidate_items` の gate は `process_subtype` より前に必ず走るものではない。
現在の順序は次の通り。

```text
TaskSolver / TypeGraph caller
    -> constrain_subtype または constrain_materialized_subtype
    -> pending: VecDeque<SubtypeConstraint>
    -> solve_constraints
    -> process_subtype
    -> 後続の slot candidate resolution / join / meet
       で effect_candidate_items
```

`candidate.rs` 自身にも「`process_subtype` runs before candidate resolution」と記録されている。
`effect_candidate_items` は candidate join/meet、effect slot bound normalization、
effect-row candidate resolution では gate になるが、raw pending constraint の admission
gate ではない。

raw pair を作る production path もある。代表例は次の通り。

```text
TaskSolver::residual_effect_after_handling
    -> graph.constrain_subtype(scrutinee_effect, Type::EffectRow(...))
    -> pending
    -> solve_constraints
    -> process_subtype
```

同様に、definition/body/application boundary の `constrain_materialized_subtype` と、
`constrain_consumed_computation_effect` も candidate resolution を先に要求せず raw subtype
pair を queue へ入れる。これらの入口は、受け取った `Con` の path が effect family かを
検査しない。

### 2.2 結論

`process_subtype` の `Con -> EffectRow` fallthrough は
redundant-but-harmless ではない。candidate gate より先に到達できる独立した fail-open
decision point である。

したがって `process_subtype` 自身に次の branch を置く。

```text
Con(path, args) <: EffectRow(items)
    if is_effect_family_path(path):
        EffectRow([Con(path, args)]) <: EffectRow(items)
        を既存 weighted row comparison へ送る
    else:
        UnsatisfiedSubtype
```

`EffectRow <: Con` はこの bridge に含めない。正しい effect lowering は whole effect の期待側を
row として表し、row item の nominal comparison は row 内部の `Con` 同士で行う。
candidate resolution で effect slot の `Con` が先に row へ正規化される既存経路も維持する。
将来、正当な production path が逆向き pair を必要とすると判明した場合は、その path と
意味論を先に設計し、この branch を無条件に対称化しない。

## 3. fixed concrete-head policy

### 3.1 ordered matrix

次の表は lower を行、upper を列にした decision table である。

| lower \ upper | `Con` | `Fun` | `Tuple` | `Record` | `PolyVariant` | `EffectRow` |
| --- | --- | --- | --- | --- | --- | --- |
| `Con` | 既存 nominal / cast branch | reject | reject | struct metadata check | reject | effect-family check |
| `Fun` | reject | 既存 structural branch | reject | reject | reject | reject |
| `Tuple` | reject | reject | 既存 structural branch | reject | reject | reject |
| `Record` | reject | reject | reject | 既存 structural branch | reject | reject |
| `PolyVariant` | reject | reject | reject | reject | 既存 structural branch | reject |
| `EffectRow` | reject | reject | reject | reject | reject | 既存 row branch |

表の `reject` は、inference では structured analysis diagnostic、specialization では
`SpecializeError::UnsatisfiedSubtype` を意味する。silent success や placeholder への置換を
意味しない。

### 3.2 同形 branch は out of scope

次は既存 branch が所有し、本設計では意味論を変えない。

- `Fun -> Fun`
- `Tuple -> Tuple`。arity mismatch を含む既存の検査を維持する
- `Record -> Record`
- `PolyVariant -> PolyVariant`
- `EffectRow -> EffectRow`
- `Con -> Con`。same-path invariant argument と ordinary nominal cast の既存処理を含む

同形 branch の内部に別の soundness gap が見つかった場合は、この cross-shape closure に
混ぜず、別の原因として扱う。

### 3.3 deferred head

specialize の `OpenVar` と、未解決 alternative を持つ `Union` / `Intersection` は
candidate resolution 前に拒否しない。inference の variable と polarity 上の
union/intersection も、既存の bound propagation / branch decomposition を先に行う。

実装では「相手と同じ syntactic head でない」を reject 条件にしない。両辺を
`fixed_concrete_head` として分類できたときだけ matrix を確定させる。

inference の `RecordTailSpread` / `RecordHeadSpread` は fixed-head mismatch の分類では
`Record` とする。ただし `Neg::Record` に対する既存 spread decomposition は先に実行する。

`Thunk` はこの六形に含めない。specialize には force/make-thunk の明示 branch があり、
stack wrapper も `peel_stack_weight` が所有する。これらを cross-shape default と一緒に
閉じない。

## 4. nominal struct / record bridge

### 4.1 path や constructor arity から推測しない

`Con -> Record` を許可できるのは、`Con.path` が実在する `struct` declaration を指す場合だけ
である。次の推測は禁止する。

- type path の文字列規則
- constructor 名と owner 名の一致
- record payload constructor の arity
- field projection の名前だけ
- runtime value がたまたま record であること

enum variant が record payload を持つ場合も、owner type 自体を nominal record shape として
登録しない。

### 4.2 shared compiler certificate

lowering は `struct` declaration から、概念上次の certificate を一度だけ作る。

```rust
struct NominalRecordShape {
    owner_path: Vec<String>,
    fields: Vec<NominalRecordField>,
}

struct NominalRecordField {
    name: String,
    projection: DefId,
}
```

`projection` は既存の synthetic field-projection definition を指す。field 型の正本を別に
複製せず、projection の通常の polymorphic scheme を使う。generic struct の owner arguments
と field result の関係も、その scheme の通常の instantiate / constraint 経路で保つ。

certificate は `poly::Arena` に structured metadata として置き、inference の
`AnalysisSession` と specialization の `TypeGraph` が同じ宣言事実を読む。比較 helper 自体は
共有しない。inference は `PosId` / `NegId` と canonical constraint provenance を扱い、
specialize は materialized `mono::Type` と weighted constraints を扱うため、無理に一つの
関数へ寄せると責務を混ぜる。

certificate は compiled/cached prefix にも保存し、import 時に `DefId` を通常どおり remap
する。現在の compiled-unit format 20 にはこの field がないため、実装 slice では 21 へ
bump する。古い cache から metadata が欠けた状態を「record bridge を許す」fallback には
しない。format mismatch による cold rebuild を選ぶ。

### 4.3 check algorithm

`Con(path, args) <: Record(required_fields)` は次の順で処理する。

1. `path` で `NominalRecordShape` を一回 lookup する。見つからなければ reject。
2. upper の required field ごとに certificate の field を lookup する。required field が
   無ければ reject。optional field が無いことは許可する。
3. 対応する projection scheme を owner `Con(path, args)` に対して通常経路で instantiate
   する。receiver が同じ nominal owner に適用されることを制約し、projection result を
   upper field type の lower として subtype constraint へ戻す。
4. field ごとの nested mismatch は、既存 subtype branch と provenance propagation に任せる。
5. すべての field obligation が成立したときだけ bridge 成立とする。

field 名は record semantics の一部なので metadata lookup key に使ってよい。type path や
field 名を見て型を捏造するのではなく、宣言済み projection definition を引くために使う。

`Record <: Con` にはこの algorithm を使わない。明示 constructor application は既存の
constructor definition と runtime constructor emission を通るので、subtype layer が
anonymous record を nominal に昇格させる必要はない。

### 4.4 inference routing

`ConstraintMachine` は module table や projection scheme lifecycle を直接所有しない。
したがって `step_subtype` の `Pos::Con -> Neg::Record` branch は成功扱いせず、producer
`ConstraintRecordId` と両 endpoint を持つ structured
`NominalRecordShapeObligation` event を `AnalysisSession` へ送る。

`AnalysisSession` は certificate と projection scheme を使って §4.3 を処理し、成立した
field constraint を同じ constraint machine へ戻す。不成立なら §6 の diagnostic を作る。
同じ producer の obligation は canonical key で deduplicate し、projection scheme がまだ
settle していない場合は既存 analysis work lifecycle に従って保留する。quiescence で
未解決の obligation を成功扱いにしてはならない。

この event boundary により、constraint core の hot path へ module traversal や CST 再走査を
入れずに済む。lookup cost は owner 一回と requested field 数に線形な範囲に抑える。

specialize は immutable な poly certificate と既に materialize 可能な projection scheme を
持つため、`process_subtype` から専用 helper へ同期的に送れる。

## 5. effect-family bridge

effect-family identity も structured certificate だけを正本とする。specialize では既存の
`effect_family_paths` / `is_effect_family_path` を使う。inference でも act declaration と
synthetic effect 登録から同じ意味の registry を constraint lifecycle へ渡し、naked
`Pos::Con` を row item として扱う前に family membership を確認する。

この変更は row semantics を作り直さない。family membership が確認できた後は、inference の
既存 `enqueue_row_item_to_upper_row` と specialize の既存 weighted effect-row comparison を
使う。row item argument invariance、tail、subtraction、stack weight の規則はそのまま残す。

non-effect `Con` は、open row tail があるという理由だけで effect row へ流してはならない。
open tail は「どの value shape も effect になれる」という意味ではない。

## 6. inference diagnostic

### 6.1 code

新しい public diagnostic code は作らない。inference で検出した concrete shape mismatch も
`yulang.unsatisfied-subtype` とする。

同じ source program が cold inference、cached prefix、specialize fallback のどこで検出されたか
によって code が変わると、diagnostic contract が stage topology に依存する。既存 code は
「specialize stage 専用」という言語仕様ではなく、unsatisfied subtype という意味を既に表して
いるため再利用する。

内部には次のような structured variant を置く。

```rust
AnalysisDiagnostic::UnsatisfiedSubtypeShape {
    actual: ConcreteSubtypeHead,
    expected: ConcreteSubtypeHead,
    producer: ConstraintRecordId,
    source_span: Option<SourceSpan>,
    related: Vec<SubtypeMismatchSite>,
}
```

`ConcreteSubtypeHead` は `Constructor(path)`、`Function`、`Tuple(arity)`、
`Record(field summary)`、`PolyVariant(tag summary)`、`EffectRow` のような構造化された
summary とする。formatter 用文字列を constraint machine 内で組み立てない。

specialize の既存 `SpecializeError::UnsatisfiedSubtype` は materialized lower/upper type を
保持し続ける。inference variant は source-aware な早期診断、specialize error は
fail-closed fallback であり、別の user-facing code にはしない。

### 6.2 source location

cross-shape event は producer `ConstraintRecordId` を必ず保持する。`AnalysisSession` は既存の
canonical provenance / source-boundary infrastructure を bounded query し、次を優先する。

1. actual value を書いた application argument または expression site
2. expected shape を要求した parameter annotation / body requirement
3. pattern または return boundary

exact な primary site が一つ選べる場合だけ `source_span` を設定する。expected requirement の
exact site は related information に置く。複数の不一致な root、budget truncation、
internal-only origin しかない場合は span を捏造せず `None` にするが、semantic rejection 自体は
取り消さない。

diagnostic dedup は `(producer, actual head, expected head)` の canonical identity で行う。
表示文字列や source text を key にしない。

### 6.3 wording

基本形は次とする。

```text
compile error [yulang.unsatisfied-subtype]:
type shape `<actual>` is not compatible with required shape `<expected>`
```

nominal-record bridge の missing field では、既存 specialize diagnostic と揃えて field 名を
主情報にできる。nested field type mismatch は派生した通常 subtype obligation の actual /
expected head を表示する。

## 7. fix を置く段階

### 7.1 inference は必須

confirmed symptom には「`check` が何も出さない」が含まれる。specialization だけを閉じると
`run` は止まっても `check` は不正な program を valid と報告し続けるため、soundness fix として
不十分である。

inference は source boundary と canonical constraint producer をまだ持つ。ここで拒否すれば、
actual / expected を作った source site を診断できる。

### 7.2 specialization も必須

specialization は次に対する独立した invariant boundary である。

- compiled/cached prefix
- provenance が incomplete な program
- inference 以外から構築された poly arena
- 将来追加される lowering path
- inference bug が再発した場合

inference が診断したはずだという前提で `process_subtype` の default success を残してはならない。
specialize では両辺が fixed concrete head の時点で最終的に accept / reject を決める。

### 7.3 shared helper ではなく shared facts

共有するのは次だけ。

- nominal-record shape certificate
- effect-family certificate
- ordered matrix という contract と対になる tests

`step_subtype` と `process_subtype` の実装 helper は分ける。前者は polarity ID、event、
canonical provenance を扱い、後者は owned mono type、stack weight、slot bound を扱う。
representation を消すための共通 enum への往復は hot path の clone と情報落ちを増やす。

## 8. generic coercion emission hardening

### 8.1 今回の scope に含める

`9d8217d3` が記録したとおり、今回と同系統の不具合は subtype solver の fallthrough だけでなく、
emitter が未承認の type difference を bare `Coerce` に変えたことで runtime まで到達した。
二つの solver を閉じても、将来新しい type head が追加されたときに同じ三段 fail-open が再発しうる。

そのため、generic `Coerce` hardening は別 projectへ defer せず、本 project の最終 semantic
slice に含める。ただし subtype closure より先には入れない。先に入れると原因側の gap が runtime
boundary error に隠れる。

### 8.2 explicit allowlist

mono type を入力にする pure な `ValueBoundaryKind` classifier を一つ置き、specialize emitter と
runtime support check が同じ contract を読む。少なくとも次を区別する。

- equivalent / Top target / Bottom source
- function adapter
- make / force thunk
- same-arity tuple element adaptation
- record field-preserving adaptation
- unsupported

generic `ExprKind::Coerce` を emit できるのは、classifier が bare coercion の runtime support を
明示した pair だけとする。function と thunk は専用 IR node を使う。unsupported pair は
`SpecializeError::UnsatisfiedSubtype` として compile time に拒否する。

runtime 側の unsupported-boundary error は defense in depth として残す。emitter の allowlist を
追加したから runtime check を削除してはならない。

nominal struct / record bridge は generic `Coerce` の allowlist に入れない。constructor と
field projection の明示 runtime operation が所有する。

## 9. slicing plan

各 slice は独立 commit とし、一つ前が green になってから進める。solver / runtime を含む command
には repository 規則どおり timeout を付ける。

### STF-A: characterization と matrix contract

変更:

- confirmed six surface counterexample を小さい contract fixture として固定する
- infer machine と specialize `TypeGraph` に ordered fixed-head matrix の characterization を置く
- valid controls として open var、union/intersection、Top/Bottom、同形 pair、正当な effect family、
  nominal field projection を置く

check:

- characterization が現在の fail-open 箇所を正確に指し、無関係な same-shape failure を混ぜない
- `timeout 120s cargo test -p infer constraints`
- `timeout 120s cargo test -p specialize specialize2`

この slice は target expectation を現在の誤出力へ変更しない。known-gap witness として保持し、
後続 slice で reject expectation を有効にする。

### STF-B: structured bridge certificates と cache transport

変更:

- `struct` だけから `NominalRecordShape` certificate を作る
- field projection `DefId`、effect-family identity、import remap を poly metadata へ通す
- compiled/cached transport を追加し、compiled-unit format を 20 から 21 へ bump する
- metadata 欠落を allow に変換しない

check:

- generic struct、同名 enum record variant、別 module の同名 field を区別する unit test
- cold / warm / imported prefix で certificate が同一になる parity test
- `timeout 180s cargo test -p infer compiled`
- `timeout 180s cargo test -p yulang cache`

この slice だけでは subtype の成功・失敗を変えない。

### STF-C: inference diagnostic plumbing

変更:

- `ConcreteSubtypeHead`、cross-shape event、`AnalysisDiagnostic::UnsatisfiedSubtypeShape` を追加する
- producer provenance から primary / related source site を bounded に投影する
- yulang formatter で `yulang.unsatisfied-subtype` へ接続する
- canonical producer 単位の dedup を追加する

check:

- synthetic event から code、actual/expected shape、primary span、related span を確認する
- internal-only / incomplete provenance でも span を捏造せず diagnostic 自体は残ることを確認する
- `timeout 120s cargo test -p infer analysis`
- `timeout 120s cargo test -p yulang source`

この slice は event を生成する pair をまだ増やさない。

### STF-D: inference の non-bridge concrete pair closure

変更:

- `step_subtype` の同形 branch 後に fixed concrete-head classifier を置く
- matrix の `reject` pair を cross-shape diagnostic event へ送る
- `Record -> Con` を明示的に拒否する
- positive record spread を mismatch 分類上 record head として扱う
- variable / union / intersection を deferred のまま保つ

check:

- integer/function、function/integer、tuple/integer、polyvariant/integer、
  record/function、anonymous-record/nominal の `check` が失敗する
- head 名や module path を変えても同じ構造なら同じ結果になる
- open `Intersection(OpenVar, Tuple)` の `9d8217d3` regression が通る
- `timeout 180s cargo test -p infer`
- `timeout 180s cargo test -p yulang --test cli`

### STF-E: inference の二つの bridge

変更:

- `Pos::Con -> Neg::Record` を `NominalRecordShapeObligation` として route する
- projection scheme から required field constraint を通常経路へ戻す
- `Pos::Con -> Neg::Row` で effect-family certificate を確認してから既存 row rule を使う
- non-effect `Con -> Row` を reject する

check:

- generic struct の存在 field / nested field type / optional field / missing field
- anonymous record から nominal への逆向きは引き続き reject
- struct 名、field 名、module path を変えた同型 control
- real effect family の singleton-row normalization と、`int` など non-effect Con の拒否
- `timeout 180s cargo test -p infer`

### STF-F: specialization の closed matrix と effect gate

変更:

- `process_subtype` の同形 branch 後に fixed concrete-head reject を置く
- existing tuple-target 専用 guard を general matrix helper に統合する
- `Con -> EffectRow` を `is_effect_family_path` で gate し、singleton row として既存 weighted
  row comparison へ送る
- `EffectRow -> Con` と non-effect `Con -> EffectRow` を reject する
- provenance を `record_shadow_failure` から既存 `UnsatisfiedSubtype` へ保つ

check:

- matrix unit test の全 reject cell
- open var / union / intersection controls
- weighted effect-family item が既存 stack filter semantics を保つこと
- `timeout 180s cargo test -p specialize specialize2`

### STF-G: specialization の nominal-record bridge

変更:

- `Con -> Record` を poly certificate と projection scheme で検査する
- required field result の subtype obligation を weighted / provenance-aware に派生させる
- missing owner、missing required field、nested field mismatch を `UnsatisfiedSubtype` にする
- `Record -> Con` は reject のままにする

check:

- infer を通さず直接 `TypeGraph` を構築する defense-in-depth unit test
- generic struct と imported certificate の test
- constructor application と field projection の existing runtime output parity
- `timeout 180s cargo test -p specialize`

### STF-H: generic `Coerce` allowlist

変更:

- shared `ValueBoundaryKind` classifier を追加する
- emitter が unsupported generic coercion を compile time に拒否する
- function / thunk の専用 node と tuple / record の supported coercion を維持する
- runtime unsupported-boundary check を残す

check:

- matrix の reject pair が `ExprKind::Coerce` を一つも emit しない
- supported tuple / record adaptation と function / thunk adapter の runtime test
- synthetic unsupported boundary が emission で `UnsatisfiedSubtype` になる test
- `timeout 180s cargo test -p specialize`
- `timeout 180s cargo test -p mono-runtime`

### STF-I: end-to-end contract と cold/warm parity

変更:

- STF-A の known-gap fixture を final reject contract へ切り替える
- `check` と `run` が同じ六反例を compile error にすることを固定する
- cold / warm / cached-prefix で code と acceptance が一致することを固定する
- 正当な struct projection、constructor、effect handler の controls を固定する

check:

- `timeout 240s cargo test -p yulang`
- `timeout 240s cargo test --workspace`
- repository の release gate 相当 command

## 10. この設計がしないこと

- same-shape `Fun`、`Tuple`、`Record`、`PolyVariant`、`EffectRow` の subtype semantics を
  変更しない。
- `Con -> Con` の ordinary cast cardinality、role、variance を変更しない。
- anonymous record を field 一致だけで nominal struct に変換しない。
- nominal struct の runtime representation を record 以外へ変えない。
- effect row の inclusion、tail subtraction、stack weight、residual semantics を変更しない。
- `EffectRow -> Con` という新しい surface bridge を追加しない。
- open var、union、intersection を soundness fix の都合で rigid 化、保護、早期 reject しない。
- `Any` を Unknown / fallback として使わない。`Never` を error placeholder にしない。
- CST を再走査して struct field や diagnostic span を復元しない。
- path、module、function、fixture 名の文字列 special case を inference に追加しない。
- current failing output に合わせて test expectation を書き換えない。
- general subtype provenance project や diagnostic wording 全体を再設計しない。
- compiled-unit format 20 の内容を metadata 無しで安全と見なす compatibility shim を追加しない。
- 本 draft の作成 slice では source、test、task log、daily note を変更しない。

## 11. stop / rollback conditions

### 11.1 stop conditions

次のいずれかが判明した時点で、その semantic slice を止め、design review へ戻す。

1. `struct` と enum record variant を cold / warm の両方で certificate から区別できない。
2. generic struct の field 型を projection scheme の通常 instantiate 経路で表せず、path や
   rendered type の照合が必要になる。
3. `Con -> Record` を通すために module table / CST の hot-path 再走査が必要になる。
4. fixed-head reject が open var / union / intersection を含む正当な candidate を拒否する。
5. production 上の正当な `EffectRow -> Con` path が見つかる。この場合は無条件 accept に変えず、
   その path の direction と row semantics を先に設計する。
6. effect-family certificate が cached/imported path で失われ、non-effect `Con` と区別できない。
7. bridge を保つために solver core へ名前 special case、rigid set、blocked pair、fallback `Any`
   が必要になる。
8. generic `Coerce` allowlist と runtime support contract が一つの classifier で表せず、
   二つの許可表が drift する。
9. owner lookup が requested field 数を超える再走査を毎 constraint で必要とし、hot-path cost を
   bounded にできない。

source span を exact に選べないことは soundness slice の rollback 条件ではない。その場合は
span を省略して診断し、provenance 改善を別 slice に残す。診断 location の不足を理由に
cross-shape pair を成功へ戻してはならない。

### 11.2 rollback unit

rollback は STF-B〜I の slice 単位で行う。matrix closure と bridge certificate を一つの
巨大 commit にしない。

- diagnostic integration に問題があれば STF-C を戻しても、specialize の STF-F/G は
  `UnsatisfiedSubtype` で fail-closed を維持できる。
- nominal metadata に問題があれば STF-E/G を止め、`Con -> Record` を暫定 accept に戻さず
  reject 側へ倒す。
- coercion allowlist に未分類の legitimate boundary が見つかれば STF-H だけを止め、
  subtype closure STF-D〜G の結果を維持する。
- cache transport に問題があれば format 21 の rollout を止め、metadata 無しの warm path を
  accept する compatibility fallback は入れない。

## 12. completion contract

本 project の完了条件は次のすべてである。

1. confirmed six counterexample を `check` と `run` が compile time に拒否する。
2. inference と specialization の fixed-head matrix が同じ acceptance contract を持つ。
3. valid `Con -> Record` は実在 struct と requested projection fields に限られる。
4. anonymous `Record -> Con` は field が一致しても拒否される。
5. valid `Con -> EffectRow` は registered effect family に限られる。
6. open candidates、Top/Bottom、same-shape branches の既存 control が通る。
7. unsupported pair から generic `Coerce` が emit されない。
8. cold / warm / imported-prefix の acceptance と diagnostic code が一致する。
9. implementation diff が slice ごとに原因へ対応し、無関係な refactor を含まない。

---
著者: Claude (Sol xhigh, via Codex MCP, supervised by Claude Sonnet 5)
状態: ユーザ承認済み（2026-07-28）
