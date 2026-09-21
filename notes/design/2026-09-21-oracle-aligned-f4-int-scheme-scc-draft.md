# Oracle-aligned F4: int scheme と静的 SCC 推論

Status: Authoritative

Date: 2026-09-21

Drafted-by: primary agent

Reviewed-by: compiler referee, specification auditor, performance auditor

Approved-by: user

Approved-at: 2026-09-21

Scope: F0--F3b の構造を保ったまま、現在受理済みの binding-body
`Integer` / resolved `Name` に対して、Yulang2 と同じ正方向の展開・簡約、
component 単位の generalization、closed-use instantiation、通常の
Bottom/`Never` root result を導入する。

Supersedes:

- SCC foundation の resolved binding-body Name が component/fact/body relation を
  持たないという限定;
- binding-body/root gate の generalization 前 root `Unknown` 限定;
- integer slice の resolved Name `(Unknown, Unknown)` 限定;
- F3 design の finalized scheme が `root_value_for` を変更しないという限定。

supersession は F0 `DefinitionUse` を持つ resolved binding-body Name、全 admitted
root の generalization、finalized root result、新しい scheme/counter/API に限る。
direct-root Name と既存 Integer occurrence の exact projection は保持する。

Function、application、parameter、annotation、import、method/role、Core IR は
対象外とする。

## 1. Oracle から引き継ぐ意味論

`yulang2-oracle@a58eefc3` から次をそのまま引き継ぐ。

- 定義の生きた root は SCC が開いている間の推論変数である。
- internal use は `target.root <: use.value` として生きた root へ接続する。
- component の全 member draft を先に作り、全 draft を finalizer から参照可能に
  してから、各 member を finalize/install する。
- component の全 scheme が確定してから incoming use を instantiate する。
- scheme は正の predicate を持ち、closed use はその正の predicate を freshen して
  `predicate <: use.value` を追加する。
- lowering/type error は SCC failure ではない。登録済み root は通常どおり
  generalize され、依存側も継続する。
- 未拘束 root は通常の bottom、すなわち `Never` へ generalize される。
  error 状態から `Never` を注入する分岐は作らない。

Yulang2 の incremental SCC、reachability、component merge、event queue、per-edge
sort、cache、shadow oracle はコピーしない。F2 の sealed static plan が scheduling
authority である。

## 2. 一つの推論 owner

private `InferenceSession` が次を所有する。

- consumed `ConstraintBatch` と immutable `SccPlan`;
- canonical `ConstraintStore` と provenance;
- resolved binding-body Name の value/effect component;
- lower/upper bound table、canonical constraint-pair cache、generalization scratch;
- component draft scratch;
- definition-root keyed finalized scheme table;
- diagnostics、public projections、production counters。

generic backend、opaque payload、Failed/Blocked state、publication query、第二の
solved-result authorityは導入しない。

## 3. Scheme payload

`yu-types` に public canonical closed value scheme を置く。

```text
ClosedValueScheme {
    body: ClosedPositiveValue
}

ClosedPositiveValue ::= Bottom | Int
```

Rust API は `pub enum ClosedPositiveValue { Bottom, Int }` と
`pub struct ClosedValueScheme { body: ClosedPositiveValue }`、
`pub const fn new(body: ClosedPositiveValue) -> Self`、
`pub const fn body(self) -> ClosedPositiveValue`、
`Clone + Copy + Debug + Eq + PartialEq + Hash` とする。
`SolvedModule` はscheme tableをprivateに保持し、public `scheme_for` は追加しない。

- binder は 0 個。
- negative predicate、effect、recursive bound、`Unknown`、error marker、solver
  leaf は持たない。
- `Bottom` は通常の正の bottom であり、表示上の `Never` に対応する。
- `Int` は closed semantic type であり、`IntPositive` leaf そのものではない。
- `Int` の instantiation は `IntPositive <: fresh use.value` を追加する。
- `Bottom` の instantiation は `Bottom <: use.value` という自明な意味操作を実行
  したものとして数えるが、fact/provenance は追加しない。

将来の quantifier、recursive bound、role predicate、latent effect をこの型へ先回り
して入れない。拡張時には payload を別途 supersede する。

## 4. Identity と ownership

- `DefinitionOrderId` と `SccComponentId` は scheduling 専用。
- semantic definition identity は既存の artifact-branded
  `DefinitionRootId`。
- finalized scheme table は `DefinitionOrderId` ordinal と同じ D 件の dense
  `Vec<Option<ClosedValueScheme>>` として一度だけ確保する。物理positionはscheduling
  ordinalだが、各slotはF2 memberからexact `CollectedDefinition.root`を一度検証して
  得るためsemantic keyは`DefinitionRootId`である。
- F0 collection の definition registration と同時に専用
  `DefinitionRootId -> DefinitionOrderId ordinal` indexを構築し、totality/duplicateを
  endpoint freeze時に検証して`SolvedModule`へmoveする。既存
  `root_component_positions` と `root_value_component` は別authorityのまま保持する。
  indexのcapacity/bytes/growth/rebuild、probe、identity hash-byte、logical successful
  equality-byte incidencesを個別に測る。drain中にroot spelling/pathをhashしない。
- `DefinitionUseId` は一つの resolved binding-body use の stable handle。
- use の value/effect component identity は既存の exact `HirOccurrenceId` と
  `ComponentKind` の組であり、新しい occurrence identity は作らない。
- 同じ payload を持つ duplicate definition も root identity が異なるため、別々の
  scheme slot を持つ。

## 5. Resolved Name の事実

F0 `DefinitionUse` に記録された resolved binding-body Name だけを対象にする。
direct-root Name はこの gate では変えない。

各 use に value/effect component を一つずつ割り当て、既存の occurrence-local slot
規則を拡張する。

```text
slot 0: routed value relation
        internal     target.root <: use.value
        incoming Int IntPositive <: use.value
        incoming Bot retained fact なし
slot 1: EffectBottomPositive <: use.effect
slot 2: use.effect <: EmptyEffectNegative
slot 3: whole-body result <: parent.root
```

現在の Name-only binding body では whole-body result がその Name occurrence である
ため、slot 3 は `use.value <: parent.root` になる。将来 nested expression が入っても
任意の nested Name を直接 definition root へ結ばない。

slot 1--3 は既存の一回の HIR collection traversal で収集する。slot 0 はbatch
occurrenceには入れず、F2 partitionからsessionが動的に作る。IDは
`ConstraintOccurrenceId(use.occurrence, local_slot=0)`、store用`CauseId`もその
occurrence-local IDを包む。route前にbatch-branded `DefinitionUseCause`とexact
`DefinitionUseId`の一致を検証する。別collectionのuse causeはbrand不一致となる。

- internal/incoming `Int` はslot-0 occurrenceをtransactionへ渡しfact/provenanceを
  retainする。
- incoming `Bottom` はstore occurrence/fact/provenanceを作らずlogical routeだけを
  retainする。
- 全routeはprivate dense `RoutedUseProvenance { use_id, fact_id, kind }`として
  `SolvedModule`へmoveする。occurrence IDは`use_id`のrecordと固定slot 0から導出し、
  二重retain/cloneしない。`kind`は`Internal | IncomingInt |
  IncomingBottomTrivial`。前二者は`Some(FactId)`、Bottomは`None`だけを許す。
  public queryはまだ追加しない。cause/use mismatchは`CauseMismatch`、同一useへの二重
  route installはcompiler invariant violation。
- 「slot 0が一つ」は各useのroute recordが正確に一つという意味である。

## 6. Simple-Sub型のbounds伝播と正方向展開

F4は二点ラベルの到達可能性問題を別に作らない。`Bottom | IntQueued | IntDrained`
のようなcomponent状態、semantic adjacency、closure queueは置かない。F2のSCCは
definitionのgeneralize/instantiate順序を決めるものであり、型変数間のsubtypingを
別のSCC到達可能性エンジンへ変換する根拠にはしない。

各value type variableは、Simple-Subとoracleと同じくlower boundsとupper boundsを持つ。
F4で現れるtype shapeは`Int+`、`Int-`、positive variable、negative variableだけだが、
処理はshapeごとの`constrain(lower, upper)`として書く。

```text
constrain(Int+, Int-)       = success
constrain(Var(v)+, upper)  = upperをv.upperへ追加し、v.lowerの各要素をupperへconstrain
constrain(lower, Var(v)-)  = lowerをv.lowerへ追加し、v.upperの各要素へlowerをconstrain
```

`Var(a)+ <: Var(b)-`は上の二規則の合成であり、`b.lower`へ`Var(a)+`、`a.upper`へ
`Var(b)-`を記録する。新しいboundは再帰へ入る前にinstallする。constraint pairの
canonical cacheを一回のsessionで共有し、既処理pairはreturnする。これはcycle停止と
重複work抑制の唯一のsemantic visited機構である。initial batch factとlater routed
factは同じ`constrain`入口へ渡す。`CrossKind`はboundsへ入れない。

generalization/coalescingはrootをpositive polarityで展開する。positive variableでは
そのlower boundsだけを再帰的に展開してunionし、同じpolar variableを展開中に再訪
した場合だけrecursive occurrenceとして残す。その後、scheme内でpositiveにしか現れず
quantifyする情報を持たないvariableを`Bot`へeliminateする。F4の閉じた整数sliceでは
最後に`Bot | Int -> Int`、重複`Int | Int -> Int`を簡約する。したがってlive variableに
lower boundがないことは推論中の`Bottom`状態ではなく、generalization時の展開・eliminate
結果だけが`Bottom` schemeになる。推論中のbounds伝播と、公開schemeを作る展開・簡約を
混ぜない。

したがって integer binding は次のように簡約される。

```text
Int+ <: body.value <: definition.value

expand+(definition.value)
  = definition.value | body.value | int
  -> int
```

definition root に `Int-` upper bound は不要である。literal の
`body.value <: Int-` は literal occurrence 自身の exact projection にだけ使う。

closed Name use でも同じである。

```text
instantiate scheme(a): Int+ <: use_b.value
use_b.value <: root_b

expand+(root_b)
  = root_b | use_b.value | int
  -> int
```

よって `my a = 42; my b = a; my c = b` は三定義すべて canonical `Int`
scheme になる。instantiation は finalized scheme を読み、旧 root projection を
推論入力にしない。

## 7. Component lifecycle

F2 の dependency-sink-first component ごとに次を実行する。

1. component member/internal/incoming slice を borrow する。clone しない。
2. internal use を `DefinitionUseId` 順に `constrain` へadmitし、boundsを伝播する。
3. reusable `Vec<DraftScheme>` を clear し、member 順に全 draft を作る。
4. ordinal-indexed borrowed `DraftView` を freeze する。
5. 全 draft 可視 barrier を test observer へ通知する。
6. member 順に own draft を O(1) lookupし、F2 memberからroot/positionを検証して
   final schemeをdense slotへ直接move/installする。finalizerはdraft sliceを全走査
   しない。
7. component quantification が完了した後だけ incoming use を順に instantiate する。
8. 次の component へ進む。

`ConstraintStore::finish_accounting()` はinitial admission後には呼ばず、全componentの
slot-0 routingとprovenance記録が完了した後、`SolvedModule`へmoveする直前に一度だけ
呼ぶ。later admissionを含む容量・fact・receipt accountingを確定する。

draft は scratch であり、component 完了後に clear する。durable scheme と並ぶ第二
authorityにはしない。final slot は順に埋めてよいが、incoming use は component
全体の完了まで一つも観測しない。

## 8. Public definition result

既存の `root_value_for` が F4 後も常に `Unknown` を返すという旧 gate の契約を
この文書が supersede する。

- finalized scheme が definition type の唯一の意味 authority である。
- `root_value_for(root)` はその root の finalized scheme を public
  `SolvedValue` へ写像する。
- `ClosedPositiveValue::Int -> SolvedValue::Int`。
- public `SolvedValue` に `Never` variant を追加する。
- `ClosedPositiveValue::Bottom -> SolvedValue::Never`。`Never` は通常の
  bottom 表示であり、error fallback ではない。
- foreign artifact は従来どおり `ArtifactMismatch`。
- current `root_values: HashMap<DefinitionRootId, SolvedValue>`は削除する。
  `root_value_for`はretained root-position indexでdense scheme slotを引き、その場で
  `SolvedValue`へ写像する。scheme tableとroot result mapを並立させない。
- admitted definition に scheme slot がない状態は compiler invariant violation で
  あり、`Unknown` で隠さない。

この変更は binding-root gate の「generalization前は root projection が Unknown」
という限定契約だけを supersede する。occurrence projection の exact interval 規則は
変えない。Name occurrence は positive lower しか持たないため value projection は
`Unknown`、effect は `Empty` のままでよい。definitionの型は occurrence projector
ではなく finalized scheme から得る。

## 9. Provenance

- literal/name effect/body-to-root fact は既存の expression occurrence cause を使う。
- internal/incoming Int の slot-0 relation は F0 が保持する exact
  `DefinitionUseCause` を使う。
- Bottom instantiation は retained fact を作らないため provenance edge も作らない。
- draft/finalization のための synthetic cause は作らない。
- scheme explanation は store facts と use causes から導出する。eager explanation
  snapshot は作らない。

既存の public opaque `CauseId` の等価性や形を変更しない。slot-0 adapterと
`RoutedUseProvenance`がexact use identityを保持する。Bottom fact省略は二点domainに
限定したoracleからの意図的最適化であり、post-solve説明はroute recordまでを示すが、
存在しないfact edgeは返さない。

## 10. Error boundary

public `SolveAvailabilityError` は既存の四つを保つ。

```text
ArtifactMismatch | CauseMismatch | ReceiptMismatch | IdentityExhausted
```

availability failure は private session 全体を drop し、partial `SolvedModule` を返さない。
same-artifact missing record、duplicate/missing final slot、non-total internal table は
compiler invariant violation とし、semantic diagnostic や別名の availability error に
しない。

`CrossKind` は従来どおり local diagnostic であり、他の scheme を抑止しない。
`CollectedBodyStatus::Error` を generalization 分岐で読まない。error root と complete
unconstrained root は同じ通常のpositive coalescingとpolar-variable eliminationにより
Bottomになる。
`CollectionAvailabilityError` は別の既存public enumであり、このgateでは変更しない。

## 11. Test-only ordering observer

`cfg(test)` の bounded observer だけを用いる。

```text
InternalUse(use_id)
Drafted(member)
DraftsVisible(component, count)
Installed(root)
IncomingUse(use_id, Int | BottomTrivial)
```

capacity を越えた event は保存せず `omitted` だけを増やす。focused ordering test は
`omitted == 0`、scale test は capacity 0 とする。production trace/lifecycle query は
追加しない。borrowed IDを使い、capacity checkをevent構築・cloneより先に行う。
capacity 0 のscale observer workはtest-onlyでありproduction evidenceに数えない。

## 12. Required tests

- isolated integer definition は `Int` scheme と `root_value_for == Int`。
- isolated unconstrained/error root は通常の Bottom/`Never`。error-status injection は
  存在しない。
- forward/backward chain と `a -> b -> c` は全 definition が `Int`。
- diamond は shared sink を一度だけ finalize し、各 incoming use を一度ずつ
  instantiate する。
- self/mutual recursion は internal relation が draft より前に入り、未seedなら
  ordinary Bottom scheme。
- internal cycleの一memberへ`Int+`が入れば、draft前のbounds伝播とpositive
  coalescingで全memberが`Int`。
- 同一constraint pairへ収束する複数の異なる `DefinitionUseId` を各一度 route する。
  同じ ID の重複は
  F0 invariant violationのまま。
- resolved Name の slot 1/2/3 と、F2 由来の slot 0 が正確に一つずつ存在する。
- direct-root Name は変化しない。
- error target の predecessor は Bottom instantiationを経て通常どおり完了する。
- error root と independent integer が共存し、後者の `Int` が保持される。
- duplicate definitions は payload が等しくても root-keyed entry が分離する。
- Name occurrence value は `Unknown`、effect は `Empty`、definition root は finalized
  scheme に従う。
- foreign/cause/receipt/exhaustion failure は partial result を返さない。
- ordering は
  `internal -> all drafts -> DraftsVisible -> install all -> incoming`。
- `my f x = x` は F4 では未表現の negative scope control とする。Function gate の
  quantifier/polarity acceptance に使い、F4へ fixture-specific 分岐を作らない。
  現在のHIRにFunction branch/scheme/accepted fixtureが増えていないことをassertする。

source surfaceで作れないdiamond、same-pair複数use、Int-bounded cycle、wide
internal fan-outは一つの
`cfg(test)` synthetic semantic-batch builderで作る。builderは本物のartifact brand、
一意なoccurrence/use ID、total definition/root/use index、sealed F2 planを生成し、
既存transactionを通してInt seedだけを注入する。productionから到達不能で、同一use
ID重複は既存`DuplicateDefinitionUseId`を返す。error-root fixtureはError/completeの
同じ未拘束rootが共にBottomになることと、body statusを読んだ分岐がないことをassertする。

Public/expected-output contract:

- public `SolvedValue` のsource orderはappend-onlyに `Int, Unknown, Never`。
  downstream exhaustive matchを更新する。
- public `SolveAvailabilityError` の四variant/traitsは不変。
- rustdoc public-path diffで新規surfaceをyu-types二型、`SolvedValue::Never`、下記の
  new counter accessors、新しいdeprecation metadataに限定する。それ以外のpublic path
  追加・削除・reorder・visibility変更は認めない。
- `ConstraintBatch::occurrences()` はF0 `DefinitionUse`-backed resolved binding-body
  Nameのslot 1--3を含み、`components_for` はそのNameのvalue/effectを含む。
  `projection_for` はそのNameに限り `(Unknown, Empty)`。
- store/provenance orderはinitial slotsの後にF2 execution順のrouted slot 0を置く。
- 既存のroot/Name/counter test名と期待値は、この文書の明示的supersessionに基づき
  causal semanticsを保つ名前へ更新する。F0/F1/F2 topology期待は変えない。

Public-path delta:

| class | disposition |
|---|---|
| `yu_types::ClosedPositiveValue` | added public enum |
| `yu_types::ClosedValueScheme` | added public struct/API above |
| `SolvedValue::Never` | appended public variant |
| `SolveAvailabilityError` | preserved exactly |
| existing `ProductionCounters` accessors | all preserved; obsolete finish-projector fields return 0 and are documented deprecated, never repurposed |
| new F4 counter accessors | added exactly as listed below |
| public scheme query | none |

Affected test contracts:

| old test | causal replacement |
|---|---|
| `binding_bodies_attach_only_to_unknown_definition_roots` | rename to state that pre-generalization body facts feed finalized `Int` roots; body occurrence remains exact |
| `f0_collects_definition_order_body_status_and_resolved_binding_uses` | retain F0 identity/topology assertions; update resolved-Name body fact range for new slots 1--3 |
| `names_errors_and_underconstrained_intervals_remain_unknown` | direct-root resolved Nameを含むため、その`(Unknown, Unknown)`とno-relationを保持。definition root assertionsだけを別testへ分離 |
| `duplicate_malformed_and_name_bodies_keep_distinct_roots_without_relations` | ambiguous NameはF0 useを持たないためno-relationを保持。各admitted rootのBottom/Int schemeだけを追加assert |
| `roots_and_components_reject_foreign_artifacts_without_name_relations` | direct-root Nameのno-relationとforeign rejectionをそのまま保持 |
| `binding_n_and_2n_counters_remain_linear` | integer-only 3N component/5N initial factを保持し、scheme/root resultとF4 execution counterだけを追加 |

resolved binding-body Name `(Unknown, Empty)`、slots 1--3、routed slot 0は新しい専用testで
検証し、direct-root/ambiguous/unresolved fixtureの期待へ混ぜない。

これらはuser approvalまでは変更しない。

## 13. Complexity と resource contract

Scheduler overhead:

```text
O(C + D + I + X)
```

Constraint propagation and positive coalescing:

```text
O(P + R)
```

`P`はcanonical constraint pairの処理数、`R`はgeneralizationで訪問するreachable
polar bound occurrence数である。pair cacheにより同一pairは高々一度処理する。
generalizationは各rootについてreachable lower-bound graphを展開する。F4実装前の
measurementでroot間の反復訪問がmaterialなら、意味を変えないmemoizationだけを別途
設計する。primitive instantiationはO(X)。

projectionとbounds伝播は一つのadmission-time resource modelを使う。各accepted factの
classifierがoccurrence value/effectのdense exact-bound bits、variable bounds、
canonical store/provenanceを同時に更新する。F3bのfinish-time `store.facts()`全走査、
旧`Bounds` temporary、`fanout` mapは削除する。finishはdense occurrence boundsとdense
scheme slotsだけからoutputを作る。

一度だけ確保するもの:

- D-entry final scheme table;
- per-variable lower/upper bound rows;
- canonical constraint-pair cache;
- `max_scc_members` draft scratch。
- occurrence exact-bound dense state と output projection storage;
- dense routed-use provenance。

initial admission前にchecked arithmeticで `B = initial batch occurrences`、
`U = definition uses` を得る。facts/canonical map、provenance、consumed receiptsは
worst-case `B + U`（全routeがInt factを作る場合）をreserveする。各containerの
requested/actual capacity、growth、rebuild、retained bytesを既存store counterへ追加する。
このreserve後のrouting phaseではこれらcontainerのgrowth/rebuildを0とする。
bounds owner tableはvalue variable数、route provenanceはU、occurrence bounds/outputは
occurrence数、draft scratchは`max_scc_members`、scheme slotsはDをexact reserveする。
bound rowsとpair cacheのgrowthは個別に数える。

production counters は少なくとも次を分離する。

- component/internal/draft/barrier/finalize/install/incoming counts;
- Int fact と Bottom-trivial instantiation counts;
- draft lookup/cross-draft visits;
- constraint pair admissions/duplicates、lower/upper bound insertions/replays;
- scheme table length/capacity/bytes/rebuilds;
- draft scratch length/capacity/bytes/growth;
- bounds table/pair cache capacity/retained/peak/rebuilds;
- F2 query/index probes と scheme probes;
- live F2 と semantic arena を含む total session retained/peak;
- total の subset としての semantic-arena retained/peak。
- initial/later fact classifications、accepted/duplicate constraint pairs、bound writes/reads、
  finish projection visits。

新しいpublic accessor名は次で固定する。

```text
scc_execution_component_visits
scc_execution_internal_use_connections
scc_execution_draft_members
scc_execution_drafts_visible_barriers
scc_execution_finalized_members
scc_execution_installed_members
scc_execution_incoming_instantiations
scc_execution_int_instantiation_facts
scc_execution_bottom_trivial_instantiations
scc_execution_draft_lookups
scc_execution_cross_draft_visits
constraint_pair_admissions
constraint_pair_duplicates
lower_bound_insertions
upper_bound_insertions
lower_bound_replays
upper_bound_replays
scheme_table_len
scheme_table_capacity
scheme_table_retained_bytes
scheme_table_rebuilds
scheme_root_query_probes
scheme_root_index_capacity
scheme_root_index_retained_bytes
scheme_root_index_growths
scheme_root_index_rebuilds
scheme_root_query_identity_hash_byte_incidences
scheme_root_query_logical_successful_equality_byte_incidences
draft_scratch_max_len
draft_scratch_capacity
draft_scratch_retained_bytes
draft_scratch_growths
bound_table_retained_bytes
bound_table_capacity
bound_table_growths
bound_table_rebuilds
bound_table_peak_bytes
constraint_pair_cache_retained_bytes
constraint_pair_cache_capacity
constraint_pair_cache_growths
constraint_pair_cache_rebuilds
constraint_pair_cache_peak_bytes
semantic_arena_retained_bytes
semantic_arena_peak_bytes
routed_use_provenance_retained_bytes
routed_use_provenance_len
routed_use_provenance_capacity
routed_use_provenance_growths
occurrence_bound_state_retained_bytes
occurrence_bound_state_len
occurrence_bound_state_capacity
occurrence_bound_state_growths
finish_projection_visits
inference_session_retained_bytes
inference_session_peak_bytes
constraint_store_requested_capacity
constraint_store_actual_capacity
constraint_store_growths
constraint_store_rebuilds
fact_store_requested_capacity
fact_store_actual_capacity
fact_store_growths
canonical_map_requested_capacity
canonical_map_actual_capacity
canonical_map_growths
canonical_map_rebuilds
provenance_requested_capacity
provenance_actual_capacity
provenance_growths
provenance_rebuilds
consumed_receipt_requested_capacity
consumed_receipt_actual_capacity
consumed_receipt_growths
consumed_receipt_rebuilds
```

`constraint_store_{requested_capacity,actual_capacity,growths,rebuilds}` は
fact/canonical/provenance/consumed-receipt各counterのchecked sumであり、別の物理allocation
を表さない。subsetをtotalへ二重加算しない。

既存`failed_component_workspace_*`、`adjacency_*`、`bounds_workspace_*`、
`fanout_index_*`、`solver_workspace_retained_bytes`、`solved_root_index_*`を含む全public
accessorは互換性のため残す。旧finish projector/storageが廃止されたfieldは0を返し、
deprecatedとして文書化する。同名を新しい意味へ再利用しない。既存admission/store/
F0--F2 counterの意味は保つ。

physical peakはallocation growth/ownership transferごとにsampleし、live F0/F2
batch+plan、ConstraintStore facts/canonical/provenance/receipts、bounds/pair cache、
final schemes、route provenance、draft scratch、errors/CrossKind set、occurrence bounds、
finish outputsをchecked-addする。semantic arenaはtotalのsubsetで二重加算しない。

1,000/2,000/4,000 のchain、diamond、bounded/unbounded cycle、wide internal
fan-out、artifact-validな複数use IDのsame-pair builderを使う。各familyで
`components=C`, `drafts=finalizes=installs=D`, `internal=I`, `incoming=X`,
`pair_admissions<=generated_pairs`, `pair_duplicates<=generated_pairs`、pre-sized storeの
component-routing-phase growth/rebuild 0をassertする。各builderは
`C,D,I,X,P,R`をfixture定義に明記し、上記counter listのcount/capacity/retained/peak/
probe fieldだけをlinear ratio対象として列挙する。明示したlinear fieldだけを
doublingごとに`<2.5x`とする。
sort/comparison は既存F1 budgetと分離する。production event trace は作らない。

## 14. Rollback conditions

次が必要になった場合は実装せず設計へ戻る。

- root result と finalized scheme の二重 authority;
- `Unknown` や error tag を scheme payload に保持すること;
- error-status-driven `Never`;
- rootへ偽のnegative bound、equality、reverse edgeを追加すること;
-全 member install 前の incoming instantiation;
- finalizerごとのdraft全走査、definitionごとのstore全走査;
- F2 member/use vector clone;
- retained draft/lifecycle table、新しい`SchemeId`;
- zero-binder primitiveのためだけのfresh predicate allocation;
- source-sized production trace;
- Function/fixture-specific logic;
- dynamic dependency admission、graph rebuild;
- public solve-error semanticsの追加。

## 15. Approval scope

この設計の承認対象は一体である。

- `Bottom | Int` closed positive scheme;
- lower/upper-bound propagation とpositive coalescing/polar-variable elimination;
- resolved binding-body Name の value/effect/body relation;
- internal/open と incoming/closed の経路;
- component draft barrier と per-member install;
- Bottom-trivial instantiation;
- finalized scheme を authority とする root result;
- provenance/error/resource/test contract。

これらを分割して open-use-only や fixture-only の中間実装を作らない。
