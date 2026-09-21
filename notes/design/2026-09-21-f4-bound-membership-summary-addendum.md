# F4 bound-membership summary addendum

Status: Authoritative

Date: 2026-09-21

Scope: F4のclosed integer sliceにおけるpositive coalescingの計算量と、それを証明する
value-only storage/resource/test contractだけを狭く補う。

Drafted-by: architect, recorded by primary agent

Reviewed-by: compiler referee, specification auditor, performance auditor

Approved-by: user

Approved-at: 2026-09-21

Supersedes/adds:

- F4 §6のper-root recursive positive expansionを、quiescence後のexact lower-membership
  summary readへ置き換える。
- F4 §13の`O(P + R)`、`P`、`R`の定義を、propagation後のdraft coalescing `O(D)`、
  propagation work `P`、total `O(C + D + I + X + P)`へ置き換える。scheduler式
  `O(C + D + I + X)`自体は保持する。
- F4 §12へ、この文書§5のprivate observationとsemantic/scale evidenceを追加する。
- F4 §14へ、この文書§6のrollback条件を追加する。
- F4 §7のlifecycle/order、§12の既存public/expected-output contract、§15のatomic gateは
  変更しない。§12への追加はprivate evidenceだけである。

## 1. 発見された問題

F4の意味どおり各definition rootからlower boundsを再帰展開すると、4,000 memberの
unbounded cycle witnessがdebug buildで80秒を超えた。F4 §13が定めた
「root間の反復訪問がmaterialなら別途設計する」という条件に該当する。

`Bottom | IntQueued | IntDrained`型の到達可能性エンジンへは戻らない。lower/upper
boundsとcanonical constraint pairが引き続き唯一のlive semantic authorityである。

## 2. 選択するsummary

各value `VariableBounds` rowにprivateな単調bitを一つ持つ。

```text
has_int_positive_lower(v) iff v.lower contains IntPositive
```

このbitは`InferenceSession::constrain`だけが更新する。canonical
`IntPositive <: Var(v)` pairが実際に新しいlower boundをinsertしたときだけ
`false -> true`にする。他variableのbitから直接伝播させない。通常のSimple-Sub
bound replayがcanonical leaf pairを生成し、既存のpair/bound/provenance counterを
通ることを必須とする。

## 3. 等価性とphase boundary

F4は同期的な`constrain`呼び出しが全recursive bound replayを完了してからreturnする。
全`constrain`がreturnし、propagation frameが残っていない境界では次が成り立つ。

```text
expand+(v)をcoalesce/eliminateした結果がInt
iff IntPositiveがv.lowerに直接存在する
iff has_int_positive_lower(v)
```

変数間pathを通る`Int`は、各upper edgeとのreplayにより最終的に
`IntPositive <: v`というcanonical pairとして各到達rowへ記録される。未seed cycleは
bitを持たず、seeded cycleは到達する全rowでbitを持つ。

summaryを読むのは次の区間だけである。

```text
全internal routeのadmissionとpair propagationがquiescent
→ 全member draftを作る
→ DraftsVisible
→ 全memberをinstall
→ incoming routeを開始
```

incoming `Int`は同じ`constrain`入口から未generalizeの後続componentを更新する。
install済みsource schemeは変更しない。boundsはF4ではinsert-onlyなのでinvalidationは
不要である。bound deletion/pruning/substitution、deferred propagation、generalize済み
rootの再open、新しいpositive value shapeやcoalescing resultが必要になった時点でこの
証明は失効し、設計へ戻る。

summaryはlive bound membershipのexact derived indexであり、別の型authority、別graph、
別worklist、persistent scheme payloadではない。

## 4. Complexityとresource contract

propagation quiescence後のdraft coalescingをper-root traversalから`O(D)`へ狭める。
scheduler式`O(C + D + I + X)`は保持し、gate全体を
`O(C + D + I + X + P)`とする。`P`はaccepted/duplicateを含むcanonical pair-cache probe、
successful pairのconstant expected-time bound insertion、opposite-row replay attemptを
含む全propagation workである。`D`はdraft member数である。これはunbounded-cycle
fixture全体をlinearと主張しない。fixtureの`P`がquadraticならtotalもquadraticのままである。

canonical pairはbound mutationより先にinsertする。一つのrow membership
`v.upper += upper`を生成できるpairは`(Var(v), upper)`だけであり、`v.lower += lower`を
生成できるpairは`(lower, Var(v))`だけである。したがってpair insertion成功は対応する
membershipが新しいことの証明になり、lower/upper rowのlinear `contains` scanを行わず
直接pushする。pair duplicateはbound mutationへ到達しない。

private canonical pair cacheはsource-bearing `Term`をkeyにしない。F4 value constraintを
admission classifierで次の固定長session-local keyへ変換してからprobeする。

```text
enum ValueEndpointKey {
    IntPositive,
    IntNegative,
    ValueRow(u32),
}

struct CanonicalValuePairKey {
    lower: ValueEndpointKey,
    upper: ValueEndpointKey,
}
```

`ValueRow`は下記dense value-row ordinalそのものであり、sessionが一artifactだけを所有する
ためartifact tokenをkeyへ重ねない。ordinalはcollection中にchecked `u32`へ変換し、overflow
はbatch publication前に既存`CollectionAvailabilityError::ComponentIdentityExhausted`を返す。
solve時の`SolveAvailabilityError`へ新しい経路を作らない。effect factsは
`OccurrenceExactBounds`だけを更新し、このvalue pair cacheへ入れない。`Term`、
`DefinitionRootId`、`DefId`、spelling、module pathのhash/equalityはpair probeから完全に
除外する。

source-bearing endpointからfixed keyへの変換はcollection/admission record構築時に一度だけ
行い、`constrain`より前で凍結する。public `ConstraintOccurrence`のfield、derived `Debug`、
`Eq`、`PartialEq`は変更しない。`ConstraintBatch`がoccurrenceと同じordinalでprivate parallel
`FrozenConstraintClass` tableを所有する。

```text
enum FrozenConstraintClass {
    Value(CanonicalValuePairKey),
    Effect,
    CrossKind,
}
```

- same-kind value relationは`Value(key)`となり、accepted admission後にvalue boundsへ渡す。
- same-kind effect relationは`Effect`となり、accepted admission後に
  `OccurrenceExactBounds`だけを更新する。
- cross-kind relationは`CrossKind`となり、value bounds/pair cache/exact-bound stateを一切
  更新せず、既存のlocal `CrossKind` diagnosticだけを保持する。
- 各`DefinitionUse`はslot-0に必要なuse value row、parent root row、target root rowをprivate
  fixed ordinalとして保持する。internal/incoming routeはこれらからkeyを直接組み立てる。
- bound rowのlower/upper endpointも`Term`ではなく`ValueEndpointKey`として保存する。
- `constrain`と全recursive replayはfixed key/endpointだけを受け取り、component/root mapや
  source identityをlookupしない。

collection時のsource-bearing lookupは既存のB/U collection/index probeとidentity-byte
incidenceへ帰属し、`P`には含めない。同一endpointをpropagationごとに再変換しない。
parallel class tableのcapacity/retained/growth/peakは既存initial fact/admission storageの
semantic-arena/session aggregateへ含めるが、public occurrence representationへ露出しない。

一つの`CanonicalValuePairKey`は一つのdirected value relationと一対一に対応する。
pair-cache capacity/retained/peak bytesは
`size_of::<CanonicalValuePairKey>()`で測り、pair probe一回をconstant expected workとして
`P`へ数える。source identity hash/equality byte incidenceを新設しない。

F4で新設する`constraint_pair_{admissions,duplicates}`、`constraint_pair_cache_*`、
`lower/upper_bound_{insertions,replays}`はvalue propagationだけを数える。effect-inclusiveな
現在の未コミットcandidateは実装欠陥であり、期待値authorityではない。一方、既存
ConstraintStoreのfact/canonical/provenance/receipt countersはvalue/effectを含む全accepted
factを従来どおり数え、意味も期待値も変えない。counter testの変更はこのvalue/store split
だけを因果として明示し、現在のcandidate出力へ合わせる変更を行わない。

`VariableBounds` tableはvalue componentだけをdenseに所有する。value row ordinalは新しい
containerにせず、既存position recordへ保持する。

- `ComponentPositions`は既存のmixed component position `value/effect`に加えて
  `occurrence_bound_row`と`value_bound_row`を持つ。
- root index valueは既存のcomponent positionだけの`usize`からprivate
  `RootComponentPositions { component, value_bound_row }`へ拡張する。
- occurrence valueとdefinition rootの`ComponentId`は、それぞれこの既存recordから
  dense value rowをO(1)で解決する。
- position mapの容量/growth/rebuild counter名と意味は保持し、retained byte counterは
  拡張後entryの`size_of`を使う。新しいindex/containerは作らない。

effect componentはvalue bounds tableへrowを持たない。F4が既に要求するdense
`OccurrenceExactBounds`をprojection order ordinalで一つ持ち、
`value_lower_int/value_upper_int/effect_lower_bottom/effect_upper_empty`の四bitをadmission
classifierだけが更新する。`ComponentPositions.occurrence_bound_row`がこのrowを指す。
これはcanonical factsからpublic occurrence projectionを作るderived cacheであり、schemeや
definition typeのauthorityではない。`occurrence_bound_state_{len,capacity,retained_bytes,growths}`
はこのcontainerだけを数える。

summary bitはvalue rowへ置き、実際の`size_of::<VariableBounds>()`増加を既存の
`bound_table_*`、`semantic_arena_*`、session retained/peak byte counterへ含める。既存public
accessorをrepurposeしない。

新しいpublic accessorは追加しない。`cfg(test)`限定のprivate observationとして
`summary_reads`と`summary_false_to_true_transitions`を持ち、実際のread/transition箇所だけで
incrementする。`summary_reads == D`を検証するが、既存のdraft/pair/bound counterへ混ぜない。

resource peakはfinal retainedの別名にしない。bounds row allocation/growth、pair-cache
growth、draft scratch growth、route provenance growth、scheme install/ownership transfer、
finish outputとのcoexistenceごとにchecked aggregateをsampleし、最大値を保持する。
initial reserve直後もsampleする。live `routed_use_positions`、`errors`、
`cross_kind_components`とreplay temporaryもsession peakへ含める。opposite row replayは
whole-row `Vec::clone`をせず、admission時のlengthを固定したindex snapshotから要素を一つずつ
cloneして処理する。各attemptを既存`lower_bound_replays` / `upper_bound_replays`へ数える。
lower-bound insertion、pair、draft counterの既存意味は変えない。

## 5. Required evidence

- seed-before-edgeとedge-before-seedの両方で、quiescence後のbitと実lower leaf membershipが一致する。
- self/mutual cycle、seedが一memberだけにあるcycle、unseeded cycle。
- incoming `Int`は後続componentのbitを更新し、incoming `Bottom`はfactもbit transitionも作らない。
- ordering observerは`internal -> all drafts -> DraftsVisible -> all installs -> incoming`を保持する。
- error rootとcomplete unconstrained rootはいずれも通常の`Never`を保つ。
- slot-0 provenance、route cardinality、pair/bound counterを変えない。
- cross-kind factはvalue pair/bound counterとexact-bound stateを一切変えず、従来のlocal
  diagnosticだけを生成する。
- 1k/2k/4kの全F4 scale matrixでprivate draft summary readがexactly `D`、既存linear/resource
  assertionが成立する。各rootの期待schemeをfixture定義からexactに検証し、`Int | Never`
  のどちらでもよいassertionにしない。
- unbounded cycleは1k/2k/4kを別process、single-threadで順に実行する。wall-time kill budgetは
  30秒/60秒/120秒、process countは各1 test binary（launcherを除く）とする。前段が完了し
  exact counter/resource assertionを満たした場合だけ次へ進む。各runのwall time、`P`、
  replay attempts、peak bytesを記録する。4kが120秒以内に完了しなければ原因にかかわらず
  gateを完了せず設計へ戻る。
- unbounded helperはsizeごとに独立したtest名を持つ。debug buildで
  `RUSTC_WRAPPER= RUST_TEST_THREADS=1 cargo test -p yu-solver --lib
  <exact-test-name> -- --exact --nocapture --test-threads=1`を外側の30/60/120秒process timeout
  から一度ずつ実行する。unfiltered suiteをperformance measurementには使わない。

## 6. Rollback conditions

次のどれかが必要なら実装せず設計へ戻る。

- reverse graph、別reachability worklist、第二のSCC pass;
- draft作成後のcache invalidation;
- lower-bound membershipと異なる経路でbitを更新すること;
- pair/provenanceの省略または意味変更;
- canonical value pair keyへsource identity、可変長payload、artifact外ordinalを入れること;
- 第二の型authority;
- value-only bounds tableを維持できずeffect rowへsummaryを配ること;
- peakをallocation/ownership-transfer境界で測れないこと;
- 4k unbounded-cycle witnessが120秒以内に完了しないこと、またはpropagation work/resource
  assertionを満たさないこと。
