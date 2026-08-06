# CPK-7 追補: incremental route endpoint / record identity 分離

日付: 2026-08-06

状態: **ユーザ承認済み（2026-08-06）**

著者: Codex gpt-5.6-sol（xhigh）が起案、Claude (Sonnet 5) が査読・確定

**査読についての注記**: Claude (Sonnet 5) がコード・既存正本文書との照合、
invariant / stop condition の査読を行い、独立したCodex gpt-5.6-terraによる
fact-check（§1・§2.1・§2.4が根拠とする現行コードの記述、matched/unmatched
constructorの分岐・CPK-7 queryの実際の条件・Legacyのgeneric coverage条件・
既存fixtureの裏付け）で不一致なしと確認済み。ユーザは要点確認の上で承認した
（2026-08-06）。

本書は、ユーザ承認済みの
`notes/design/2026-08-06-cpk-replay-routing-decision-addendum.md`
（以下「routing decision追補」）を直接編集せず、CPK-7 Slice C item 15で判明した
incremental routeの二つのupper identityに関する契約だけを訂正する追補である。

対象はrouting decision追補の§2.1、§3.2、§3.3、§5、§9に限る。
CPK-7のarchitecture、failure/rollback、index、performance、他consumerの契約は変更しない。
本書はSlice B query修正・Slice C oracle修正の正本であり、§6のslicingに従って実装する。

## 0. 決定の要約

1. `IncrementalRouteKey::upper: NegId`はincremental semantic actionが実際に使う
   replay endpointである。
2. `IncrementalRouteKey::upper_record: BoundRecordId`はclaim ownership、
   replay derivation、event-local groupingを担うrecord identityである。
3. 二つのidentityはunmatched row routeでは一致するが、matched row routeでは
   `upper = original_upper`、`upper_record = current materialization record`として
   正当に異なり得る。
4. generic pair replayがincremental routeを包含するのは、query upper recordが
   genericを要求し、かつそのcurrent endpointが`route.upper`と一致するときだけである。
5. `Generic`はgeneric pair workの存在を表し、residual incremental workの不存在を
   表さない。従って`Generic + non-empty incremental_replays`は正規形になり得る。
6. `IncrementalUpperMismatch`は`route.upper_record != query upper`だけを表す。
   `route.upper != current record endpoint`はfailureではない。

## 1. Stop conditionを発火させたground truth

Slice C item 15のfixtureは、test-only `TypeBounds` writeを使わず、次だけで構築された。

1. 二項を持つeffect rowを通常の`subtype`経路へ投入する。
2. 最初のfamily lowerでunweighted row reductionとlive root claimを生成する。
3. 二番目のfamily lowerでmatched incremental routeと新materializationを生成する。
4. production `move_upper_replay_claim`経路がroot claimを新recordへ移す。

この自然イベントでLegacyは正しく進むが、CPK queryは次を返した。

```text
ReplayRoutingInvariantViolation {
    lower: BoundRecordId(2),
    upper: BoundRecordId(3),
    kind: IncrementalUpperMismatch,
}
```

原因は`ProofOccurrenceStore::validate_incremental_route_target`が
`route.upper_record == query upper`に加えて、未決定だった
`route.upper == current upper-record endpoint`まで要求したことにある。

production constructorは二種類ある。

```text
unmatched route:
    upper        = snapshot.current_reduced_upper.endpoint
    upper_record = snapshot.current_reduced_upper.record

matched route:
    upper        = snapshot.original_upper
    upper_record = materialization.record
```

前者は`crates/infer/src/constraints/row_effect.rs`の
`unweighted_row_reduction_routes_for_new_lower`のunmatched arm、後者は同関数の
matched armで構築される。matched armはclaim moveの有無にかかわらず
`snapshot.original_upper`をsemantic actionへ使うため、この分離はitem 15固有の
例外ではなく、matched incremental row routeの一般形である。

Legacyの既存fixture
`unweighted_row_upper_incremental_route_registers_reduction_route_claim_parent`も、
late familyをcurrent reduced endpointだけでなくoriginal rowへrouteすることを固定している。

## 2. routing decision追補への5点の訂正

### 2.1 元§2.1: Legacy generic coverage条件

**訂正前**:

> 対応upperでgeneric replayが必要なら、そのincremental semantic actionをskipする。

この文はendpoint identityがrecord identityと常に一致するように読めるため不十分である。

**訂正後**:

```text
generic_covers(route, query_upper) :=
    current_record_endpoint(query_upper) == route.upper
    AND current_record_requires_generic_replay(query_upper)
```

`generic_covers`がtrueのrouteだけをincremental semantic action listから除外する。
query upper recordがgenericを要求していても、`route.upper`がそのrecordのcurrent endpointと
異なるrouteは包含されず、residual incremental actionとして実行する。

これは現行`ConstraintMachine::add_lower_bound`の次の処理をそのまま形式化する。

- record lookupとendpoint equality
- `upper_record_requires_generic_replay`
- `(route.upper, BinaryReplayDerivation)`のfirst-seen dedup
- `route.upper`を使ったsemantic replay admission

### 2.2 元§3.2: `upper`と`upper_record`のfield意味

**訂正前**:

> `upper/upper_record/provenance/claim`のどれも落としてはならない。

field保存は決めていたが、二つのupper identityの責務境界を明記していなかった。

**訂正後**:

```text
IncrementalRouteKey::upper:
    exact semantic replay endpoint
    - first-seen semantic action key
    - replay statistics / var-var classification
    - subtype replay admission target
    - row/reduction route provenance merge target

IncrementalRouteKey::upper_record:
    proof/frontier record identity
    - event-local `upper_record -> routes` grouping
    - BinaryReplayDerivation.upper
    - route claimのcurrent ownership validation
    - record-local coverage / generic decision
```

`upper_record`のsemantic endpointから`upper`を再導出してはならない。
prepared queryとcore adapterは両fieldをexactに保持する。

routeのoptional claimは`upper_record`に属する。claimがqualifyするsemantic actionの
endpointが`upper_record`のcurrent endpointと異なることは、matched row routeでは正当である。

### 2.3 元§3.3: routing/payload consistency

**訂正前**:

| routing | `pair_replay` | `incremental_replays` |
| --- | --- | --- |
| `Generic` | `Some` | empty |
| `IncrementalOnly` | `Some`または`None` | non-empty、または`pair_replay = Some` |
| `SkipAlreadyCovered` | `None` | empty |

**訂正後**:

| routing | `pair_replay` | `incremental_replays` | 意味 |
| --- | --- | --- | --- |
| `Generic` | `Some` | emptyまたはnon-empty residual routes | query upperのgeneric pairが必要。endpoint不一致によりgenericへ包含されないrouteは併存できる |
| `IncrementalOnly` | `Some`または`None` | non-empty、または`pair_replay = Some` | generic pair reasonはないがincremental/attachment workがある |
| `SkipAlreadyCovered` | `None` | empty | pairにもincrementalにもworkがない |

一pairのresidual route列は次で作る。

```text
residual_incremental_replays :=
    incremental_routes
        .filter(route => NOT generic_covers(route, query_upper))
        .dedup_first_seen(route.upper, BinaryReplayDerivation)
```

従って`ReplayRouting::Generic`の意味は「generic pair replayが必要」であり、
「他のsemantic actionが存在しない」ではない。

`RoutingPayloadMismatch` validatorもこの訂正版tableを使う。`Generic`かつ
`incremental_replays` non-emptyをfailureにしてはならない。

### 2.4 元§5: `IncrementalUpperMismatch`

**訂正前の決定table本文**:

> incremental routeの`upper_record`がquery upperと異なる
> → `ReplayRoutingInvariantViolation::IncrementalUpperMismatch`

この本文自体は正しい。しかしSlice B実装は条件を次へ拡張してしまった。

```text
route.upper_record != query_upper
OR route.upper != current_record_endpoint(query_upper)
```

**訂正後**:

```text
IncrementalUpperMismatch := route.upper_record != query_upper
```

`route.upper != current_record_endpoint(query_upper)`はfailureではない。
それは§2.1の`generic_covers`をfalseにし、routeをresidual incremental workへ残す。

claimがある場合の次のvalidationは変更しない。

- claim IDが存在する。
- claimの`current_record == route.upper_record`。
- route upper recordのcanonical representative relationとclaim/rootが一致する。
- side、lineage、coverage rootをexactに解決できる。

任意の`NegId` corruptionまで検出する新しいfailureは本書で追加しない。現行routeは
同一natural event内のproduction row-reduction constructorが生成するtyped inputである。
将来endpoint自体をproof stateから再検証するなら、matched/unmatched route kindと
row-reduction stateへのexact indexを別途設計しなければならず、current record endpointとの
equalityを代替checkにしてはならない。

### 2.5 元§9: strengthened Legacy adapter

**訂正前のnormalization**:

> routingが`Generic`なら`incremental_replays`をemptyにする。

**訂正後**:

Legacy expected `PreparedReplayRoute`は、各routeについてproduction Legacyと同じ
`generic_covers`を評価する。

```text
if generic_covers(route, query_upper):
    pair replayに包含されたrouteとしてprepared incremental listから除外
else:
    input order / first-seen exact-key orderでprepared incremental listへ残す
```

oracleは次を独立に比較する。

1. pair-level routing summary
2. generic pair presenceとexact parent payload
3. residual incremental route exact key / order / parent payload
4. 実際のincremental admission、row provenance merge、worklist trace

`Generic + non-empty incremental_replays`をLegacy adapter側で消してから比較してはならない。

## 3. 変更しないもの

本書は次を変更しない。

- CPK全体およびCPK-7のarchitecture
- `project_lower`、projection decision、projection consumer authority
- `PreparedReplayParent`のclaim/root/side/lineage identity
- `ProofFailure`、`ProofFactRef`、`MandatoryProofField`、
  `ReplayRoutingInvariantViolation`のvariant set
- §7のO(1)/O(log n) indexed-query performance contract
- §8のmachine-local terminal failure、whole-attempt discard、fresh LegacyRollback retry
- parent canonical order
- incremental input order / first-seen exact-key order
- Slice DまでLegacy routingをproduction authorityに保つ規律
- CPK-8 legacy removalおよびCPK-9 closeout

RCPFのexact parent、event-time snapshot、first-seen semantic order、failure atomicityとも
矛盾しない。むしろ、record identityからsemantic endpointを誤って再導出しないことで
exact action identityを保持する。

routing decision追補§11.1の「genericが同upper routeを包含する」と§12 invariant 20の
「generic routeが同upperのincremental semantic actionを包含する」にある「同upper」は、
本書の承認後は**同じ`upper_record`**ではなく、§2.1の
`current_record_endpoint(query_upper) == route.upper`を意味する。この二箇所は別の追加決定を
置いておらず、訂正版generic coverage ruleへのcross-referenceとしてのみ有効である。

## 4. 既存Slice B/C fixtureとのcross-check

### 4.1 Slice B fault-injection tests

`cpk_7_incremental_route` helperは意図的に
`upper == current record endpoint`のcoupled routeを作る。これは引き続き正規形である。

`cpk_7_slice_b_rejects_invalid_incremental_claims_and_upper_grouping`が壊すのは
`upper_record`であり、訂正後も`IncrementalUpperMismatch`である。既存期待値は変更しない。
`route.upper != current endpoint`をfailureとしてpinするfixtureは存在しない。

### 4.2 Slice C item 4 (`1e3694fb`)

`cpk_7_shadow_real_row_route_is_incremental_only_end_to_end`は、
`original_items = []`、`original_upper == current_reduced_upper.endpoint`のreduction stateへ
新lowerを入れる。実際に通るのはunmatched constructorであり、二つのidentityは一致する。
このfixtureと期待値はそのまま有効である。

### 4.3 Slice C item 9 (`cca8ca54`)

`cpk_7_shadow_routes_all_five_lineages_exactly`も同じCPK-3 fixtureをfresh machineとして使う。
Original lineageで生じ得るrow routeはunmatched/coupled形であり、他lineageのpairは
row-route endpoint decouplingを前提にしない。5 lineage exact attribution assertionは
そのまま有効である。

### 4.4 §9.4 matrix全体

既にcoveredのitems 1、3、4、5、6、8、9、12は期待値変更なしで有効である。
item 15だけが本書の新しい必須fixtureを担う。

追加fixtureは少なくとも二つ必要である。

1. all-covered matched route:
   `upper != current endpoint`、claim moveあり、`IncrementalOnly`、residual route一件。
2. generic current record + residual matched route:
   generic pairを実行しつつ、endpoint不一致routeも一件実行する
   `Generic + non-empty incremental_replays`。

## 5. 訂正後の追加invariant

1. `route.upper`と`route.upper_record`を同一identityとして比較・再導出しない。
2. event-local groupingは`route.upper_record`だけで行う。
3. generic coverageは§2.1の二条件ANDで決める。
4. genericに包含されないrouteをsummaryだけを理由に捨てない。
5. prepared adapterは`route.upper`をsemantic replayとrow provenance mergeへexactに渡す。
6. route claimは`upper_record`へ属し、semantic endpoint equalityをclaim validityに使わない。
7. Legacy oracleは実行されるresidual incremental actionを一件もnormalize-awayしない。

## 6. 承認後のimplementation slicing

### Slice B-correction 1: query core

一commitで次を行う。

- `validate_incremental_route_target`からcurrent endpoint equality条件を除く。
- `generic_covers`をLegacyと同じ二条件ANDとして実装する。
- `requires_generic`でもresidual incremental routesをprepareする。
- `RoutingPayloadMismatch` validatorを訂正版tableへ合わせる。
- all-covered decoupled routeとGeneric+residual routeのisolated query fixturesを追加する。

### Slice C-correction 2: strengthened oracle

別commitで次を行う。

- Legacy expected adapterの「Genericなら全routeをempty」を除く。
- routeごとに`generic_covers`を評価する。
- exact residual key/order/parentsとevent-level admission/mergeを比較する。
- item 15のproduction-only two-stage row-reduction fixtureを恒久化する。

### Slice C resume

targeted、full scoped、worklist/row/termination parityをgreenにした後、未完了の
§9.4 itemsへ戻る。Slice C completion gateを満たすまでSlice Dへ進まない。

## 7. Stop conditions

次のいずれかを観測したら実装を止め、再び設計レビューへ戻る。

1. production constructor以外から`IncrementalRouteKey`が入り、endpoint validityを
   proof stateから検証する必要がある。
2. `route.upper_record`とclaim current recordの不一致を正当化する実例が見つかる。
3. Legacyが§2.1以外の条件でincremental routeをgenericへ包含する。
4. `Generic + residual incremental`を現行3-way enum / prepared payloadでlosslessに
   実行できない。
5. corrected oracleで親identity、route order、admission、row merge、worklist、terminationの
   いずれかがLegacyとdivergeする。
6. 既存covered matrix itemの期待値変更が必要になる。
7. hot path queryへglobal scanまたはpairごとのroute全量再scanが戻る。

## 8. Review checklist

Claude (Sonnet 5) は特に次を査読する。

1. `route.upper`がoriginal semantic action endpointであるという説明が、
   matched/unmatched constructorとLegacy admissionの両方に一致するか。
2. `Generic + non-empty incremental_replays`が既存core adapterでlosslessに表現できるか。
3. revised consistency tableがno-claim Generic、covered attachment pair、
   IncrementalOnly、SkipAlreadyCoveredを壊さないか。
4. failure vocabularyを増やさず、`IncrementalUpperMismatch`の意味を狭く保つ判断が妥当か。
5. Slice B/C既存fixtureの影響分析に見落としがないか。
6. correction 1/2のcommit境界が独立にrevert可能か。

本書はユーザ承認済みであり、routing decision追補§2.1・§3.2・§3.3・§5・§9を
訂正する正本である。実装は§6のslicing（Slice B-correction 1: query core →
Slice C-correction 2: strengthened oracle）に従う。
