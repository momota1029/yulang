# F4 direct-bound frontier addendum

Status: Reviewed

Date: 2026-09-21

Scope: F4のvalue propagation kernelをfull transitive Var-pair materializationから
direct Var adjacencyとnon-variable bound frontierへ置き換え、それに伴う六つのpublic
`ProductionCounters` accessor、pair-cache population、resource/test contractを更新する。

Drafted-by: architect, recorded by primary agent

Reviewed-by: compiler referee, specification auditor, performance auditor

Supersedes/adds:

- F4 §6の全Var-Var consequence materializationとopposite-row recursive replayを置き換える。
- summary addendum §4の`P`/replay counter定義と、§6のreverse graph、separate worklist、
  pair omission/meaning changeをrollbackする条項を、paired direct adjacency、synchronous
  source-free queue、non-materialized transitive Var pairに限って置き換える。
- F4 §12/§13へreference evidence、frontier counter、scale/resource contractを追加する。
- approval scopeはprivate kernelに加え、`constraint_pair_admissions/duplicates`、
  `lower/upper_bound_insertions`、`lower/upper_bound_replays`の意味と、pair cacheからの
  transitive Var-pair除外を含む。
- F4 §7 lifecycle、scheme/projection、ConstraintStore fact/provenance、recovery、fixed key、
  value-only bounds/summary authorityは変更しない。

## 1. Trigger and root cause

summaryとfixed keyを実装しても1,000-definition unbounded-cycleは30秒で完了しなかった。
`r=2n` value rowsのcycleで旧kernelは全reachable ordered pairをmaterializeし、次のworkを
生成する。

```text
accepted canonical pairs = r² + r
replay attempts           = r³ + r²
all pair probes           = r³ + r² + r + 1
```

`n=1000`では約80億replayとなる。ownerはtransitive Var relationのphysical enumerationである。

## 2. Semantic authority

- `ConstraintStore`はdirect source fact、receipt、cause、provenanceのauthority。
- value boundsとfixed endpoint keysはlive inference relationのauthority。
- transitive Var relationはdirect graph reachabilityとしてlosslessに表現し、ordered pairを
  全列挙しない。
- atomがrowへ到達したらrow mutation前にexact canonical atom-row pairをadmitする。
- `has_int_positive_lower`はsuccessful `IntPositive <: row` insertionだけが更新する。
- propagationは各`constrain`内で同期的にdrainし、return/phase boundaryへpendingを残さない。

queueはgeneric endpoint transmissionの一時execution stateであり、Int reachability label、
durable state、second authority、F2 SCCではない。

## 3. Direct-bound frontier kernel

```text
VariableBounds {
    direct_lower_rows,
    direct_upper_rows,
    exact_non_variable_lowers,
    exact_non_variable_uppers,
    has_int_positive_lower,
}
```

paired lower/upper rowsは一つのdirect subtype edgeのcanonical physical representationである。
別途rebuildするreverse graphやreachability indexではない。他のgraph/SCC/cacheは作らない。

sessionはsource-free fixed keyだけを持つprivate `VecDeque`を一つreuseする。route/public入口の
`constrain`だけがnon-recursive drainを開始し、drainから`constrain`を再帰callしない。

- `Var(a) <: Var(b)`: direct edgeだけをdeduplicate/installする。`a`のexact lowersを`b`へ、
  `b`のexact uppersを`a`へenqueueする。transitive Var pairは作らない。
- `atom <: Var(v)`: exact membershipをinstallし、`v`のexact uppersとのatom-atom pairと、
  全direct upper rowへのtransmissionをenqueueする。
- `Var(v) <: atom`: exact membershipをinstallし、`v`のexact lowersとのatom-atom pairと、
  全direct lower rowへのtransmissionをenqueueする。
- `atom <: atom`: 既存terminal ruleを使い、同じcanonical cacheを通る。

edge-before-seed/seed-before-edgeの両方を処理する。各`(atom, direct edge, direction)`は高々
一度transmission probeされ、0または1個のnew membershipになる。self edgeはduplicate probeに
なりうる。same-row atom intersectionも高々一度処理する。

resource accountingはadmission/drainから全table scanを呼ばない。各containerのinitial
reserve、capacity growth、clear/reuse、ownership transferでcapacity deltaとchecked aggregateを
O(1)更新し、peakを取る。queue bytesは`capacity * size_of::<CanonicalValuePairKey>()`。
private observerはpush/pop/max-live、capacity/growth/retained/peak、aggregate contributionを
保持し、production aggregateと一致させる。

## 4. Complexity and counters

`V`=value rows、`E`=unique direct Var edges、`L/U`=exact atom lower/upper memberships、
`T`=atom/direct-edge transmission attempts、`J`=same-row atom intersectionsとする。
propagation inputは次の非重複countで定義する。

- `I/X`: F4既存どおり全internal/all incoming route visits。Bottom-trivial incomingも`X`に含む。
- `M`: ordinary initial value pair probes。test-only synthetic seedを除く。
- `I_p = I`: internal route由来のvalue pair probes。
- `X_p <= X`: incoming Int route由来のvalue pair probes。
- `X_b = X - X_p`: Bottom-trivial incoming routes。pair probeはないがscheme lookup、route
  uniqueness、provenance record workを持つ。
- `S`: test-only synthetic seed pair probes。initial-fact loopを通ってもaccounting classは`M`と
  分離する。
- `A = M + I_p + X_p + S`: 各input pair-cache probeをduplicateを含め正確に一度数える。

```text
time  O(C + D + I + X + A + E + L + U + T + J)
space O(V + E + L + U + queue + direct facts)
```

`I/X`はscheduler、scheme lookup、route/provenance overheadを数え、`A`はそのうちvalue
pair-cache probe workを数える。これは同じrequest内の別operationであり、Bottom fanoutも
`X`によって必ずboundされる。

F4では`L+U<=2V`、`T<=2E`、`J<=V`。structured endpoint追加時は再設計する。

- `constraint_pair_admissions/duplicates`: direct input/frontier/intersectionがprobeしたdirect
  Var edgeまたはexact atom-row/atom-atom fixed keyのaccepted/duplicate数。
- `lower/upper_bound_insertions`: paired direct adjacencyまたはexact atom membershipのphysical
  insertion。
- `lower_bound_replays`: exact lower atom/direct upper edgeのtransmissionと、lower/upper atom
  intersection。intersectionはadmission orderにかかわらずlower側へ数える。
- `upper_bound_replays`: direct lower edge/exact upper atomのtransmission。
- pair cacheはdirect edgeとexact atom pairだけをretainする。
- queue resourceはsemantic/session aggregateへ含める。public accessorは増やさず、private
  observerでdirect-edge/exact-membership/transmission/queue resourceを検証する。

ConstraintStore counters、slot-0 provenance、distinct route cardinalityは不変。

## 5. Required evidence

- `V=0..3`についてself edgeを含む全`2^(V²)`graph、全lower/upper seed subsetを列挙する。
  edge-first、lower-first、upper-first、edge/seed反転の四orderで旧reference closureと、Var
  reachability、各rowのexact atom membership、terminal atom-pair集合、summary bit、empty queueを
  exact比較する。`E/L/U/J` exact、`T<=2E`、push=pop、全probe boundも比較する。
- `IntPositive <: v <: IntNegative`の両insertion orderと、seeded chain末尾upperを検証する。
- self/mutual/long cycle、chain、diamond、wide fanout、distinct-use provenanceを検証する。
- transitive Var-pair生成0、direct edge exact `E`、queue return時empty、CrossKind zero mutation、
  error/unconstrained `Never`、ordering、scheme/projectionを保持する。
- synthetic builderはper-edge linear `.position`を禁止し、owned row ordinalをO(1)で読む。
- size-selectable 1k/2k/4kを30/60/120秒capで順に実行し、wall time、E/L/U/T/J、queue peak、
  semantic/session peak bytesを記録する。

Scale fixtureのcausal expectations:

| family | M/I/X/S | E | L | T | J |
|---|---:|---:|---:|---:|---:|
| chain | `N-1 / 0 / N-1 / 1` | `N-1` | `2N-1` | `N-1` | `0` |
| diamond | `N / 0 / N / N/4` | `N` | `2N` | `N` | `0` |
| bounded cycle | `N / N / 0 / N/2` | `2N` | `2N` | `2N` | `0` |
| unbounded cycle | `N / N / 0 / 1` | `2N` | `2N` | `2N` | `0` |
| wide internal fanout | `2N-2 / 2N-2 / 0 / 1` | `4N-4` | `3N-2` | `4N-4` | `0` |
| distinct routes, one source scheme (`D=2`) | `N / 0 / N / 1` | `N` | `N+2` | `N` | `0` |

tableの`M`はinitial slot-3 value request数であり、effect factとsynthetic seedを含まない。
listed scale familyでは全incoming routeがIntなので`X_p=X`、`X_b=0`である。各familyで
`A=M+I_p+X_p+S`。pair admissionsは`E+L+U+terminal pairs`、全probeは`A+T+J`
以下、duplicatesは`all probes-admissions`として導出する。旧`generated_pairs`/
`reachable_positive_bounds`と`...keeps_pair_work_parameterized`を廃止し、direct edge/exact
membership/frontier名へ因果的にrenameする。旧same-pair testは実際にはdistinct use rowsなので
`distinct_use_routes_share_one_source_scheme`へrenameする。

## 6. Rejected alternatives

- union-find、第二のtype SCC、full transitive pair、Int専用reachability、timeout緩和。

## 7. Rollback conditions

- materialized transitive Var keyまたはderived-pair provenance;
- queueが`constrain` return/phase boundaryを越えること;
- bound deletion/pruning/substitution、finalized component reopen;
- generic frontierで運べないstructured endpoint;
- second SCC、union equality、source-bearing queue/key、second authority;
- exhaustive reference不一致;
- 1k/2k/4k resource/counter/timeout failure。
