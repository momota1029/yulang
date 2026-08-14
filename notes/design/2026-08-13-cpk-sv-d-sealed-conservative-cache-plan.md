# CPK-SV-D 統合再設計: sealed structural gateway と conservative-default cache

日付: 2026-08-13〜2026-08-14

版: **rev.9（確定）**

状態: **確定 rev.9、Claude (Sonnet 5) 独立査読済み、ユーザ承認済み（2026-08-14）**

著者: Codex gpt-5.6-sol（xhigh）が起案、Claude (Sonnet 5) が独立査読・確定

> **Authority notice**
>
> 本書はCPK-SV-D実装のauthorityである。実装は本書の§7実装スライス計画（SS0〜SS9）の順序と、
> 各sliceのgate/stop conditionに従う。cache-relevant storageのownership移行、sealed gateway
> cutover、production cache read、`Unchanged` proof allowlistの追加は、対応するsliceのgateを
> 満たした場合にだけ行う。

rev.4は、rev.3のpseudocodeだけでは決着しなかったRust type-system上の問いを、repository外のstandalone
prototype `/tmp/cpk-sv-d-kernel-skeleton`（Rust 1.95.0）で実際にcompile/testして設計へ反映する。prototypeは
disposableな検証証拠であり、本repositoryへ統合せず、production実装をそこからcopyするauthorityにも
しない。rev.3の一部合格やprototypeの局所合格をrev.4全体の承認へ繰り上げず、rev.4を改めて全文査読する。

rev.5はround 10の`SOUND WITH GAPS`査読を反映し、HRTB query scopeを維持したままround-persistent owned stateと
scope-local facadeを分離する。また、scope typeのactual visibility、type-shape入力、owned evaluation result、
multi-container publication plan、prototype evidenceの限界を具体化する。rev.5も全文再査読とユーザ承認までは
implementation authorityではない。

rev.6はround 11後の専用meta-reviewを反映し、caller-owned lifetime-free round stateだけを
attempt identityへ明示bindする。これはcore architectureの再設計ではなく、現行production call graphで
已に成立するattempt-localityを型とruntime checkで固定するnarrow defense-in-depth revisionである。

rev.7はrev.6 deltaだけへ行われた限定査読を反映する。foreign roundのterminal stateより先に
attemptを認証する順序、publication round側の同一enforcement、`ForeignAttemptRoundState`のexact
public payload typeだけを具体化し、それ以外のrev.6/core designを変更しない。

rev.8はrev.6/rev.7 deltaだけへ行われた追加の限定査読を反映する。認証後のprojection/publication
scope構築失敗をcommon failure branchの外へ逃がさず、publication scope typeのexact visibility、
`ConstraintMachine`側production delegate、foreign-attempt error payloadの向きを確定する。それ以外の
rev.5以前の設計判断を変更しない。

rev.9はrev.8限定査読で残ったAPI visibility一点だけを閉じる最終draft revisionである。
`QueryCompletion<R>`をrestricted-visibleなopaque success receiptとしてexact surfaceへ加え、その生成を
scope-consuming completion methodへ限定する。それ以外の設計判断を変更しない。

本書は、ユーザ承認済みの
`notes/design/2026-08-12-cpk-preflight-structural-validity-addendum.md`
（以下 CPK-SV 追補）が定めた CPK-SV-D を、六回の不成立設計と2026-08-13の実測を踏まえて
全面的に再設計する文書である。また、ユーザ承認済みの
`notes/design/2026-08-13-cpk-sv-c-dynamic-dependency-synchronization-addendum.md`
（以下 CPK-SV-C redesign）を継承する。

本書はCPK-SV-A/B/Cのauthority、identity、late-binding、support-ledger closure、canonical
fallback、error precedence、cycle semanticsを変更しない。変更するのは、CPK-SV-Dのsnapshot
writer ownership、mutation finalization、successful structural-validity cacheだけである。

本書は、独立査読で`NOT SOUND`となった次の二案を実装authorityとして継承しない。

- 旧round 5: opaque structural state + sealed gateway単独案。
- 旧round 6:
  `notes/design/2026-08-13-cpk-sv-d-conservative-default-cache-plan.md`のscattered-writer案。

両案の有効だった機構だけを、相互の欠陥を閉じる形で統合する。

## 0. 決定の要約

### 0.1 Core decision

cache-relevant structural stateを変更できる入口を一つにする。

```text
external solver / lowering / row logic
        |
        | public data-only StructuralMutationIntent
        v
ProofStructuralState::prepare(...)
        |
        | opaque handle -> kernel-private PreparedStructuralCommand
        v
ProofStructuralState::commit(...)
        |
        +-- read-only no-op prover succeeds
        |       -> Applied(Unchanged(explicit proof), receipt)
        |
        `-- otherwise
                -> sealed write transaction
                -> exhaustive private PreparedPayload dispatch
                -> Applied(Changed, receipt)
        |
        v
single finalizer
        +-- Changed   -> completed snapshotを一回bump
        `-- Unchanged -> snapshotを維持
```

1. `ProofStructuralState`はcache-relevant dataの唯一のownerであり、外部moduleへraw `&mut`、
   mutable field、`DerefMut`、mutation callbackを公開しない。
2. callerが構築するdata-only `StructuralMutationIntent`と、private reservation tokenを持つkernel-only
   `PreparedStructuralCommand`を分離する。public intentとprivate `PreparedPayload`がそれぞれclosed enumであり、
   private-field command structが後者とticketを所有する。prepare mappingとchanged dispatchは両enumを
   wildcardなしのexhaustive matchで扱う。
3. gatewayがmutation intentを受理したsuccessful commitは必ずsingle finalizerへ戻る。外部writerのearly returnがstructural
   mutation後にfinalizerを迂回する第三経路を持たない。
4. gatewayのclassification defaultは`Changed`である。proofが無い限り、実際のwrite件数がzeroでも
   snapshotを進める。
5. `Unchanged`は、小さなprivate allowlistのread-only exact comparisonが作るcommand-specific
   proof tokenでだけ選べる。arbitrary command handlerはtokenを構築できない。
6. `Unchanged` proofが成立した場合、gatewayはmutating handlerを呼ばない。従って「proof成立後、
   handlerへ新write branchが追加されたのに古い`changed`式が残る」というround 5のfailureを避ける。
7. proofが無い場合、handler内部のbranch、early return、実write件数に関係なくfinalizerは`Changed`を
   publishする。従ってround 6の`commit_upper_claim_move`型early return omissionを避ける。
8. cache readはstorage sealing、HRTB query-scope cutover、evaluator fallibility、failure-latch reconciliationが
   全部landingした後にだけ有効化する。partial sealing中はproduction cache authorityを持たない。
9. `ProofStructuralSnapshotId`はcache invalidation identityだけに使う。prepared commit conflictやcapacity
   reservationのbaseには使わない。
10. prepare/commitはtarget-local semantic baseとshared-resource reservation ticketを別々に持つ。これにより
    CPK-SV-Cが許可した異種writer interleavingを維持しつつ、同一containerのcapacityをoutstanding prepare間で
    二重予約しない。
11. command/query/cache portはmachine-owned active-attempt capabilityなしに到達できない。caller conventionでは
    なく、terminal latchとsealed gatewayを同じcontrol ownerの下へ置く。
12. reservation ticket IDはattempt-global non-wrapping allocatorが一意に発行する。domain-local generationを
    global registry keyへ使わない。
13. per-record/per-root child containerはoutstanding reservation中にemptyでもpinし、reserved physical capacityを
    remove/recreateで失わない。
14. prepared mutationはkernel-owned bounded scopeに置く。arena内ではscope `Drop`が、arenaからtakeした後は
    `InFlightCommitGuard::Drop`がticketを所有し、handle drop/`?`/panic/terminal unwindでもreleaseする。
15. production structural readはHRTB exclusive query scope内でだけ行う。raw storage referenceをscope外へ返せず、
    scope中に同じkernelをterminal transitionへ進められないことをborrow checkerで保証する。per-getter
    `RefCell`/`Cell` recheckをauthorityにしない。
16. cross-target checked/memo sharingはborrowを持たない`ProjectionEvaluationRoundState` /
    `CpkPublicationEvaluationRoundState`へ置く。`ProjectionPreflightFacade`と`CpkProjectionEvaluatorFacade`はtargetごとの
    query scope内でfreshに作り、round stateへstore/view referenceを保存しない。
17. multi-container changed commandは、全lookup/hash/equality/assertをwrite前に終えるclosed
    `PreparedPublicationPlan`へ変換し、audited panic-free typed primitivesだけを順次publishする。family handlerへraw
    `HashMap::insert`やopen callbackを渡さない。
18. caller-owned round stateはkernel factoryが生成し、`(ProofAttemptNonce, ProofStructuralSnapshotId)`へbindする。
    foreign attemptのroundをcache missとして再利用せず、query/cache lookup前にtyped errorで拒否する。

### 0.2 相補性の理論

round 5とround 6は相補的な理由で失敗した。

| 設計 | 成立した部分 | fatal gap |
|---|---|---|
| round 5 sealed gateway | raw mutationを一つのgatewayへ閉じ込める構造 | command内部の手書き`changed`判定をcompilerが正しく保てない |
| round 6 conservative default | `Changed`を安全なzero-proof defaultにする原理 | scattered writerのearly returnがclassification/finalizer自体を迂回する |

本統合案では、sealed gatewayが「classificationへ到達しない経路」を除去し、conservative defaultが
「classification内部を完全証明できない問題」をsafe over-invalidationへ倒す。

ただし、この相補性は全semantic correctnessを型で証明するものではない。次はtrusted kernelに残る。

- prepared base checkがmutation前に完了すること。
- changed handlerのtransaction atomicity。
- allowlistされたno-op comparatorがpreflightの全relevant fieldを比較すること。
- new mandatory readをsealed state/query view/comparatorへ同時に追加すること。

本書は「trusted kernelがzeroになる」と主張しない。mechanically閉じるのは、外部raw mutation、
successful commit finalizer bypass、arbitrary handlerによる`Unchanged` token構築である。

## 1. 本設計が必要になった経緯

### 1.1 六回の設計・gate failure

#### Round 1: self-referential source census

`include_str!("mod.rs")`でproduction writer名とsnapshot bump文字列を探した。test自身にwriter名と
label文字列が含まれるため、production writerを削除してもself-matchし得た。runtime behaviorを証明
しないvacuous gateだった。

#### Round 2: mutation-class aggregate counter

`Bound`、`UpperClaim`、`ProofDependency`等のclass合計が正ならcoveredとした。同classの一writerが
発火すれば、別writerのbump欠落をmaskできた。

#### Round 3: per-writer-site counter

syntactic writerごとにsiteを分けたが、`ProofOccurrence`一siteへordinary bound、row definition/
reduction、root/subtract/scheme-instantiation identity、structural/row/replay/reduction-route dependency等が
集中した。shared sinkの一経路が別経路をmaskした。

#### Round 4: atomic-boundary + shared-sink二軸案

independently-triggerable atomic boundaryをreviewed inventory rowにし、shared sinkをtyped cause matrixで
補った。独立査読は`NOT SOUND`と判定した。新writer、新changed branch、new mandatory readをinventoryへ
登録し忘れてもcompiler/testが必ず失敗するmechanismがなかった。

具体的には、`commit_projection_index_admission`のtarget/edge branch masking、
`ConstraintDisposition` / `SchemeInstantiationRecord` / `ReplayDrop`と§5.4分類のずれ、
`BoundPromotion` / `BoundWithoutOccurrence` / replay-evidenceのgranularity gapが挙がった。

#### Round 5: opaque state + sealed gateway単独案

`ProofStructuralState`へstateを集約し、closed `StructuralMutation`とexhaustive dispatchだけをmutation
入口にするmechanical closureを提案した。raw writer omissionをcompile-time visibility failureへ変える
方向は正しかった。

しかし、command内部の`changed` expressionはsemantic logicだった。たとえば既存commandの
`commit_projection_index_admission`へ新write branchを追加しても、手書き`changed` boolを更新し忘れれば
commandは`Unchanged`を返せた。compilerはnew enum variantのmatch追加を強制できても、既存variant内部の
change detection correctnessを証明できない。独立査読は`NOT SOUND`と判定した。

#### Round 6: conservative-default + scattered writers

`Changed`をzero-proof default、`Unchanged`をexplicit equality proofにする非対称原理を採った。この原理
自体とCPK-SV-C late-bindingとの整合は独立査読で成立した。claim move/live coverage transitionはcurrent
authority変更ごとにsnapshotを進めるため、same-snapshot validity reuseと両立する。

fatal gapは、既存scattered writerを残したことだった。current HEAD `9ce43039`の
`ProofOccurrenceStore::commit_upper_claim_move`
（`crates/infer/src/constraints/proof/mod.rs:7393`付近）は、`old_record == current_record`でearly returnし、
末尾のsnapshot-bump epilogueへ到達しない。この現行branchは実際にはno-opだが、同じfunctionへ将来
cache-relevant writeを追加してearly returnを残せば、`Changed`/`Unchanged` classification自体を通らず
silent under-invalidationを再導入できる。

さらに独立査読は次を指摘した。

1. evaluatorのfallible pre-reservationは
   `checked_records.len() + checked_constraints.len()`を上限としている。cache hitがclosure expansionを
   skipするとchecked数が過小になり、その後の`states.insert`がinfallible reallocationを起こし得る。
2. 「Changed-only Slice 1」という表現は、既存のsame-record/no-op early returnsをclassificationへ
   取り込んでいないため不正確だった。
3. `ProjectionEvaluationRound::terminal_failure`と`ConstraintMachine`のattempt-terminal latchを、
   「failureをcacheしない」契約と明示的に調停していなかった。

### 1.2 Complementary failure

round 5は**closureは強いがdefaultが弱い**。round 6は**defaultは強いがclosureが無い**。
本書は次を同時に要求する。

- storage privacyとwrite capabilityにより、mutation-capable codeがgateway外でstateを書けない。
- gateway finalizerへ戻らないsuccessful commitを型・call structure上作れない。
- mutating handlerのclassificationは常に`Changed`であり、handler自身は`Unchanged`を選べない。
- `Unchanged`はmutation handlerと分離したread-only proverだけが作る。

これにより、設計の安全性を「全writerを人手で列挙したか」や「全branchでboolを更新したか」へ依存させない。

### 1.3 rev.1 independent reviewとrev.2の焦点

rev.1への独立査読は、`commit_upper_claim_move`のmutation後early-return escapeがsealed gatewayで閉じるという
統合理論の中心を、current code walkで確認した。一方、次の新しいgapを指摘した。

- global snapshot baseではCPK-SV-C-approved interleavingをspurious conflictにし、target-local baseだけでは
  shared container capacityをoutstanding prepare間で二重予約する。
- machine terminal latchとgateway/cache portがcaller conventionでしか結ばれていない。
- fallible evaluator designがinfallible publication-time pathとrecord/root override insertを覆っていない。
- caller-side pure no-intent returnまでmandatory disposition対象に見せる過剰主張がある。
- Rustのparent/child privacyを踏まえたactual module layoutが無い。

rev.2は§3.1.1、§3.5〜§3.8でこれらを設計contractへ変える。rev.1査読の一部合格をrev.2全体の承認へ
繰り上げず、resource/capability/evaluatorを含む全文を再査読する。

### 1.4 rev.2 independent reviewとrev.3の焦点

rev.2への独立査読は、同じshared containerに対するoutstanding reservationの算術、特に
`physical_spare >= outstanding_units`と「不足差分ではなくrequired spare総数を`try_reserve`へ渡す」規則を
成立と確認した。一方、次を新たに指摘した。

- ticket ID allocatorがdomain-localにしかなく、global `active_tickets` keyを一意化できない。
- per-record/per-root child containerがoutstanding reservation中にempty removalされ、reserved capacityを失い得る。
- callerがprepared handleをdropした時のticket cleanupを`#[must_use]`とexplicit cancelへ依存している。
- read viewがmint後にactive-attempt capabilityを再checkしない。
- sibling modulesが相互に型をnameするためのexact restricted visibilityが書かれていない。
- fixtureがold raw-store testを参照し、new gateway/ticket pathとactual claim-first production orderを実行しない。

rev.3は§3.1.1、§3.5.3〜§3.5.6、§3.7、§7、§10.10を更新する。CPK-SV-A/B/Cのsemantic decisionは
変更しない。

### 1.5 Round 9 method changeとrev.4のcompiler evidence

rev.3へのround 9独立査読は、sealed gateway + conservative defaultのcore architectureには三回連続で新しい
counterexampleが無い一方、pseudocode reviewだけでは次のRust-level propertyを確定できないと判断した。

- caller-facing intentとprivate reservation-bearing prepared commandを同一型にできるか。
- arenaからprepared entryをtakeした後のpanic/early `?`でticket ownerが消えないか。
- latch check後に返したraw `&T`がterminal transitionを越えてescapeしないか。
- per-getter `RefCell::try_borrow` costがhot pathを圧迫しないか。
- richer type setでもrev.3のsibling-module visibilityが成立するか。

そこでverification methodを変更し、standalone crate `/tmp/cpk-sv-d-kernel-skeleton`でactual Rust code、unit test、
compile-fail probe、release microbenchmarkを実行した。結果は次である。

1. `StructuralMutationIntent` / private `PreparedStructuralCommand` splitはcompileした。external accessはE0603、
   sibling struct literalはE0451で拒否された。
2. arena take直後からticketを所有する`InFlightCommitGuard`は、deliberate panicとearly errorの双方で
   active ticket / outstanding unitをzeroへ戻した。
3. `RefCell` check後のraw `&T` escapeはsafe Rustで再現した。`Cell<Generation>` per-getter recheckへ替えても
   raw `&T`を返す限り同じescapeが残った。
4. HRTB exclusive query scopeからraw referenceを返すprobeはE0515、scope中に同じkernelをterminalへ進める
   probeはE0500/E0501でcompile-failとなった。scope内でowned valueへ変換して返すpathはcompileした。
5. rev.3のrestricted sibling visibilityはtwo-type split、write port、RAII guardを含むpositive buildでcompileした。
   external gateway accessはE0603、outer `PreparedStructuralCommand` / `ProofWritePort` field constructionはE0451で
   拒否された。kernel-visible `PreparedPayload` variant constructionはこのprobe対象外だった。

このprototypeはproof-system semantics、real storage capacity、full call graphを検証していない。rev.4が採用するのは
compilerで確認したownership/lifetime/privacy patternであり、prototype artifact自体ではない。

検証時のartifactと結果:

- crate: `/tmp/cpk-sv-d-kernel-skeleton`。
- positive unit tests: 9 passed / 0 failed。
- external prepared-command `compile_fail` doctest: 1 passed。
- sibling privacy negative probe: outer command/write-port field E0451、private ticket type rejection。
- external gateway negative probe: E0603。
- query-scope negative probes: E0515およびE0500/E0501。
- release capability microbenchmark: 75,000,000 checks/sample × 5 samples。結果は§3.7.2。

prototypeはrepository外に置いたまま変更・commit・production integrationしない。production sliceでは同じpatternを
fresh implementationし、production自身のcompile-fail/runtime gateを改めて通す。

### 1.6 Round 10 `SOUND WITH GAPS`とrev.5の焦点

round 10独立査読は、本arcで初めて`NOT SOUND`ではなく`SOUND WITH GAPS`と判定した。sealed gateway、
conservative Changed default、HRTB exclusive query scopeのcore architectureに新counterexampleは無く、recursive
`validate_record` / `validate_constraint`とCPK-SV-C late bindingが一つのscope内で完結し、nested/re-entrant scopeを
要求しないこともcurrent call graphで確認された。

一方、次の実装契約はrev.4だけでは不足していた。

1. current `ProjectionEvaluationRound<'a>` / `CpkPublicationEvaluationRound<'a>`はstore/machineを長期borrowする
   facadeを所有する。HRTB scopeへそのまま入れるとscopeを開始できないか、cross-target checked/memo sharingを失う。
2. `ScopedProjectionQuery`のrestricted visibilityが、その型をclosure boundに露出するcaller breadthより狭い。
3. formula shadow、live coverage、projection indexのようなmulti-container commandは、単純な一field swapへ
   一律変換できず、post-write panic pointを閉じるstanding publication patternが必要である。
4. prototypeがE0451で確認したのは`PreparedStructuralCommand` / `ProofWritePort` field constructionであり、
   kernel-wide visibleだった`PreparedPayload::MoveClaim` variantのsibling constructionまでは拒否していなかった。
5. scope構築に必要なimmutable `TypeArena` inputと、scope外へ返せないborrowed
   `SchemeProjectableLower<'a>::bound`の移行形が未指定だった。

rev.5は§3.1〜§3.2、§3.5.7、§3.7〜§3.8、§4、§7〜§11を更新する。round 10で成立確認されたrecursive validationと
late binding semanticsは変更せず、lifetime-free round stateとscope-local facadeの間へ分離する。

### 1.7 Round 11 meta-reviewとrev.6の限定的対応

round 11査読は、rev.5のlifetime-free round stateが`ProofStructuralSnapshotId`だけでchecked/memo stateを
bindしているため、同じ数値のsnapshotを持つ別attemptへround valueを渡せばfalse reuseを起こし得ると
指摘した。専用meta-reviewでactual lifecycleを追った結果、現行productionでは`AnalysisSession` / `InferArena` /
`ConstraintMachine`がcompilation attemptごとにfreshに生成され、current borrowed roundもsame machineのlocal traversalから
逃げない。retry、prefix compilation、incremental pathのいずれにもround/machineを別attemptへ渡すreachable
production pathは確認されなかった。

従ってこの指摘は、現在到達可能なproduction bugではない。一方でrev.5がborrow lifetimeを意図的に外した
owned typeは、safe Rustでforeign machineへ渡すmisuseを拒否しない。rev.6はこのtype-theoretic gapを
defense in depthとして閉じ、実際に成立しているattempt-localityをAPI上も強制する。この限定修正をcore
architectureの新たな破綻、またはactive production riskの修正とは表現しない。

## 2. 実測データ

### 2.1 Measurement contract

2026-08-13、current HEAD `9ce43039`へtemporary instrumentationを入れ、測定後に完全revertした。
commitは作成していない。keyは次だった。

```text
(ProofOccurrenceStore instance,
 ProofStructuralSnapshotId,
 BoundRecordId | ConstraintRecordId)
```

`ProjectionPreflight::validate_record` / `validate_constraint`の全entryを数え、同一round内の既存
`checked_records` / `checked_constraints` hitと、別preflight roundからのsame-snapshot success repeatを
分離した。failureとactive-path cycleはpersistent success candidateへ含めていない。

これはretrospective opportunity censusである。ancestor cache hitでrecursive entriesが消えるため、raw
entry比率をwall-time改善率へ直接換算しない。

### 2.2 RMW N=6

| class | entries | total比 |
|---|---:|---:|
| total record/constraint validation entries | 50,309,515 | 100% |
| existing round-local guard | 39,886,843 | 79.28% |
| cross-round same-snapshot repeat | 10,140,837 | 20.16% |
| cold/non-repeat | 281,835 | 0.56% |

round-local guard外は`10,422,672`件であり、そのうち`10,140,837`件、**97.30%**がcross-round
same-snapshot repeatだった。original complaintであるRMW-shaped superlinearityには強いreuse opportunityが
ある。

### 2.3 Cold `std::text::parse`

| class | entries | total比 |
|---|---:|---:|
| total record/constraint validation entries | 144,192,658 | 100% |
| existing round-local guard | 114,092,543 | 79.13% |
| cross-round same-snapshot repeat | 8,013,718 | 5.56% |
| cold/non-repeat | 22,086,397 | 15.32% |

round-local guard外は`30,100,115`件であり、そのうち`8,013,718`件、**26.63%**がcross-round
same-snapshot repeatだった。cold `std::text::parse`は実在するが二次的なbenefitであり、broad speedupを
約束しない。

### 2.4 Interpretation after round 6 review

sealed conservative baselineでは、gatewayへmutation intentとして発行されたsame-record/no-write commandは、
explicit proofが無ければ`Changed`としてsnapshotを進める。一方、callerがactive read-only precheckだけで
mutation intentを発行しないpure no-opはcommandではなくsnapshotを進めない。両者の実頻度次第で、round 6測定時の
D0 snapshotよりgenerationが細かく進み、production hit率が§2.2/§2.3より低くなる可能性がある。

この数字はprojectを試す理由であり、landing保証ではない。sealed migration完了後のChanged-only cacheで
RMW A/Bを再測定し、価値が無ければ`Unchanged` allowlistを増やす前に停止する。

## 3. 設計

### 3.1 Sealed ownership boundary

`ConstraintMachine`に散在するcache-relevant storageとmachine attempt-terminal latchを、opaqueな
attempt-local control ownerへ集約する。latchの意味とfirst-failure telemetryは変更せず、structural portへ
到達するcapabilityの発行元と同じownerへ物理的に置く。

```rust
use std::num::NonZeroU64;
use std::sync::atomic::{AtomicU64, Ordering};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(in crate::constraints) struct ProofAttemptNonce(NonZeroU64);

// Process内の全ConstraintMachine / ProofAttemptKernelで共有する。Relaxedで十分なのは、
// このcounterがuniquenessだけを与え、structural publicationのmemory orderingを担わないためである。
static NEXT_PROOF_ATTEMPT_NONCE: AtomicU64 = AtomicU64::new(1);

fn mint_proof_attempt_nonce() -> Option<ProofAttemptNonce> {
    NEXT_PROOF_ATTEMPT_NONCE
        .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |next| next.checked_add(1))
        .ok()
        .and_then(NonZeroU64::new)
        .map(ProofAttemptNonce)
}

pub(in crate::constraints) struct ProofAttemptKernel {
    // `None`はprocess-wide counter枯渇後のreuse-disabled mode。再利用可能なnonceで代用しない。
    attempt_nonce: Option<ProofAttemptNonce>,
    reuse_disabled: bool,
    terminal_failure: RefCell<Option<ProofFailure>>,
    structural: gateway::ProofStructuralState,
}

// gateway module内だけに定義し、structural_kernel::mod.rsからre-exportしない。
pub(in crate::constraints::structural_kernel) struct ProofStructuralState {
    data: StructuralData,
    snapshot: ProofStructuralSnapshotState,
    validity_cache: StructuralValidityCache,
    reservations: StructuralReservationLedger,
    prepared: PreparedMutationArena,
}

pub(in crate::constraints::structural_kernel) struct StructuralData {
    proof: ProofRelations,
    bounds: BoundRelations,
    constraints: ConstraintRelations,
    rows: RowRelations,
    identities: IdentityRelations,
}

pub(in crate::constraints) struct ScopedQueryView<'query> {
    data: &'query StructuralData,
    snapshot: ProofStructuralSnapshotId,
    type_shapes: ImmutableTypeShapeView<'query>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ProjectionRoundBinding {
    attempt: ProofAttemptNonce,
    snapshot: ProofStructuralSnapshotId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum AuthenticatedRoundAccess {
    Reusable,
    ReuseDisabled,
}

// Scopeを越えて保持するstateはID/value/mapだけを所有し、StructuralData/TypeArenaへのborrowを持たない。
pub(in crate::constraints) struct ProjectionEvaluationRoundState {
    binding: Option<ProjectionRoundBinding>,
    reuse_disabled: bool,
    preflight: ProjectionPreflightRoundState,
    evaluator: CpkProjectionEvaluationRoundState,
    terminal_failure: Option<ProofFailure>,
}

struct ProjectionPreflightRoundState {
    visiting_records: FxHashSet<BoundRecordId>,
    checked_records: FxHashSet<BoundRecordId>,
    visiting_constraints: FxHashSet<ConstraintRecordId>,
    checked_constraints: FxHashSet<ConstraintRecordId>,
    // cfg(test) traceもowned ID/valueだけを保持する。
}

struct CpkProjectionEvaluationRoundState {
    states: FxHashMap<ProofEvalNode, ProofEvalState>,
    memo_sharing_disabled: bool,
    cycle_cuts: usize,
}

pub(in crate::constraints) struct CpkPublicationEvaluationRoundState {
    binding: Option<ProjectionRoundBinding>,
    reuse_disabled: bool,
    evaluator: CpkProjectionEvaluationRoundState,
    record_overrides: FxHashMap<BoundRecordId, bool>,
    root_overrides: FxHashMap<UpperReplayClaimId, bool>,
}
```

`ProjectionEvaluationRoundState`と`CpkPublicationEvaluationRoundState`はlifetime parameterを持たず、複数top-level
targetの間でintentional checked/memo sharingを保持する。現行`ProjectionEvaluationRound<'a>::preflight:
Option<ProjectionPreflight<'a>>`、`CpkPublicationEvaluationRound<'a>::machine/shared`、
`CpkProjectionEvaluator<'a>::view/store`をそのまま保存しない。borrowを持つ実行objectは§3.7.1の
`ProjectionPreflightFacade<'query>` / `CpkProjectionEvaluatorFacade<'query>`として各target scope内だけでfreshに
構築する。

round stateの`binding`はmemo/checked identityでありwriter-conflict baseではない。normal modeではkernel factoryが
`ProjectionRoundBinding { attempt: current_nonce, snapshot: current_completed_snapshot }`を設定した状態でroundを
生成する。same attempt / same snapshotの次targetだけstateをreuseする。same attemptでscope間にChanged
commitが入りsnapshotが変わった場合、次scope entryはterminal failureをclearせず、success-only
visiting/checked/evaluator memoを全clearしてnew snapshotへrebindする。

bindingの`attempt`がcurrent kernelの`ProofAttemptNonce`と異なる場合は、cache missへ畳み込んでroundを
clear/repopulateしない。cache lookupやsemantic getterより前に
`ProofAccessError::ForeignAttemptRoundState { expected, actual }`を返し、roundとkernel/cacheの両方を不変に保つ。
payloadの向きは`expected = current kernelが要求するnonce`、`actual = 渡されたroundが保持するnonce`で固定する。
従ってK1 roundをK2 kernelへ渡すfixtureでは`expected == Some(K2 nonce)`、`actual == Some(K1 nonce)`である。
この認証より前に読んでよいround fieldは`binding`だけである。foreign roundの`terminal_failure`、
checked/memo、record/root override、cycle stateを読み、clearし、またはerror selectionに使ってはならない。
`ProjectionEvaluationRoundState` / `CpkPublicationEvaluationRoundState`のfieldとconstructorはprivateとし、`Default`や
standalone `new()`を実装しない。callerは`ConstraintMachine::{new_projection_evaluation_round,
new_publication_evaluation_round}`だけから生成する。これらはkernel factoryへdelegateし、生成時点の
attempt/snapshotへbindする。

`mint_proof_attempt_nonce()`はnew `ConstraintMachine` / kernel構築時に一度だけ呼ぶ。counterはprocess内で
wrap/reuseしない。`fetch_update` failure後はprocess永続で`None`とし、fallback/sentinel nonceを発行しない。
そのkernelと後続kernelは`reuse_disabled = true`とし、structural validity cache hit/publicationとcross-scope
checked/memo reuseを行わない。factoryは`binding = None, reuse_disabled = true`のroundを作り、各queryを
private scope-local fresh stateでcanonical実行する。wrapperはcaller-owned reuse-disabled roundの
`terminal_failure`、memo/checked、override/cycle stateを読まず、書かず、error precedenceに使わない。query failureは
current kernel latchの既存ruleに従って扱い、unauthenticated persistent roundへimport/exportしない。nonce枯渇時に
同じ`None`同士をsame attemptとみなさない。これは
`ProofStructuralSnapshotId`飽和時と同じsafe-side reuse disableである。

#### 3.1.1 Rust module / visibility layout

parent-private itemがchildから見えるRustの規則を考慮し、family implementationをgatewayのchildに置かない。
採るlayoutは次で固定する。

```text
constraints/
  structural_kernel/
    mod.rs                 # opaque facadeだけをre-export
    access.rs              # ProofAttemptKernel、active capabilityの唯一のconstructor
    commands.rs            # data-only public intent / closed command vocabulary
    read_view.rs           # getter/cursorだけ。mutation/cache portなし
    gateway/
      mod.rs               # ProofStructuralState、prepare/commit/finalizer
      storage.rs           # StructuralData。gateway parentへだけpub(super)
      reservation.rs       # reservation ledger/ticket/one-shot reserved operation
      unchanged.rs         # private proof token/comparator
      write_ports.rs       # family別scoped write port。constructorはgateway private
    families/              # gatewayとはsibling
      proof.rs
      bounds.rs
      constraints.rs
      rows.rs
      identities.rs
```

`structural_kernel/mod.rs`のmodule declaration/re-exportは次で固定する。`gateway`、`families`、raw storageを
`crate::constraints`へre-exportしない。

```rust
mod access;
mod commands;
mod gateway;
mod read_view;
mod families;

pub(in crate::constraints) use access::{
    CpkPublicationEvaluationRoundState,
    PreparedStructuralMutationHandle,
    ProofAccessError,
    ProofAttemptNonce,
    ProofAttemptKernel,
    ProjectionEvaluationRoundState,
    QueryCompletion,
    ScopedPublicationProjectionQuery,
    ScopedProjectionQuery,
    StructuralPreparationScope,
};
pub(in crate::constraints) use commands::{
    CommittedStructuralMutation,
    StructuralMutationIntent,
};
pub(in crate::constraints) use read_view::ScopedQueryView;
```

`gateway/mod.rs`はprivate child moduleを外へ公開せず、cross-siblingで型名だけが必要な二型をrestricted
re-exportする。

```rust
mod reservation;
mod storage;
mod unchanged;
mod write_ports;

pub(in crate::constraints::structural_kernel) use storage::StructuralData;
pub(in crate::constraints::structural_kernel) use write_ports::{
    BoundsPublishPort,
    FormulaPublishPort,
};
```

従って`read_view.rs`は`super::gateway::StructuralData`、`families::*`は
`super::gateway::{FormulaPublishPort, BoundsPublishPort}`等をnameできるが、`storage` / `write_ports` module自体やそのprivate field/
constructorをnameできない。

visibility ruleは次の**exact declaration**で固定する。`pub(crate)`へ広げて代用しない。

```rust
// access.rs
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(in crate::constraints) struct ProofAttemptNonce(NonZeroU64);
// tuple fieldはaccess.rs private。`crate::constraints`のcallerは型名/値のcopyはできるがmintできない。
pub(in crate::constraints) struct ProofAttemptKernel { /* fields are private to access */ }
pub(in crate::constraints) struct StructuralPreparationScope<'scope> {
    /* fields and Drop cleanup are private to access */
}
pub(in crate::constraints) struct PreparedStructuralMutationHandle<'scope> {
    /* fields are private to access; non-Clone/non-Copy */
}
pub(in crate::constraints) struct ProjectionEvaluationRoundState {
    /* owned checked/memo/terminal/attempt+snapshot binding fields; no structural borrow */
}
pub(in crate::constraints) struct CpkPublicationEvaluationRoundState {
    /* owned memo/override/attempt+snapshot binding fields; no machine/evaluator borrow */
}
pub(in crate::constraints::structural_kernel) struct ActiveProofAttempt<'a> {
    /* fields and constructor are private to access */
}
pub(in crate::constraints) struct ScopedProjectionQuery<'query> {
    /* query view + private cache port + round-local state。constructor private、scope外へescape不能 */
}
pub(in crate::constraints) struct ScopedPublicationProjectionQuery<'query> {
    /* publication query view + private cache port + publication round-local facade。
       constructor/fields private、scope外へescape不能 */
}
pub(in crate::constraints) struct QueryCompletion<R> {
    // fields are access.rs private。callerはstruct literalでsuccess candidateを偽造できない。
    value: R,
    candidates: SuccessfulValidationCandidates,
}
pub(in crate::constraints) enum ProofAccessError {
    Terminal(ProofFailure),
    TerminalLatchBusy,
    ForeignAttemptRoundState {
        // `None`はreuse-disabled identity。None == Noneは認証成功と見なさない。
        // expectedはcurrent kernel、actualはcaller-supplied roundのidentity。
        expected: Option<ProofAttemptNonce>,
        actual: Option<ProofAttemptNonce>,
    },
}
impl ScopedProjectionQuery<'_> {
    // Successful validationの最後にscopeをconsumeし、scope内で蓄積したcandidateをopaque receiptへ移す。
    pub(in crate::constraints) fn complete<R>(
        mut self,
        value: R,
    ) -> QueryCompletion<R> {
        let candidates = self.take_success_candidates(); // access.rs private
        QueryCompletion { value, candidates }
    }
}
impl ScopedPublicationProjectionQuery<'_> {
    pub(in crate::constraints) fn complete<R>(
        mut self,
        value: R,
    ) -> QueryCompletion<R> {
        let candidates = self.take_success_candidates(); // access.rs private
        QueryCompletion { value, candidates }
    }
}
impl ActiveProofAttempt<'_> {
    pub(in crate::constraints::structural_kernel) fn ensure_active(
        &self,
    ) -> Result<(), ProofAccessError>;
}

// gateway/mod.rs
pub(in crate::constraints::structural_kernel) struct ProofStructuralState {
    /* fields are private to gateway */
}
pub(in crate::constraints::structural_kernel) struct PreparedStructuralCommand {
    // fields are private to gateway。private PreparedPayloadとreservation authorityを所有する。
}
impl ProofStructuralState {
    pub(in crate::constraints::structural_kernel) fn prepare(...);
    pub(in crate::constraints::structural_kernel) fn commit(...);
    // arbitrary callerへpersistent read viewを返すmethodは置かない。
}

// gateway/storage.rs
pub(in crate::constraints::structural_kernel) struct StructuralData {
    // proof/bounds/constraints/rows/identities fields are private to storage.rs.
}
impl StructuralData {
    // gateway childrenだけが使うraw mutation primitive。
    pub(super) fn ...;
    // read_view.rsが使うimmutable field-level getterだけ。
    pub(in crate::constraints::structural_kernel) fn read_...(&self, ...) -> ...;
}

// read_view.rs
pub(in crate::constraints) struct ScopedQueryView<'query> {
    // fields and constructor are private to read_view.rs.
}
impl ScopedQueryView<'_> {
    pub(in crate::constraints::structural_kernel) fn new<'a>(
        data: &'a StructuralData,
        type_shapes: ImmutableTypeShapeView<'a>,
        snapshot: ProofStructuralSnapshotId,
    ) -> ScopedQueryView<'a>;
    pub(in crate::constraints) fn bound(...) -> Option<&BoundRecord>;
    pub(in crate::constraints) fn constraint(...) -> Option<&ConstraintRecord>;
    // referenceはquery closure内だけで使用できる。viewをscope外へ返せない。
}

// gateway/write_ports.rs
pub(in crate::constraints::structural_kernel) struct FormulaPublishPort<'a> {
    /* private fields + one-shot operations */
}
impl FormulaPublishPort<'_> {
    pub(super) fn new(...); // gateway parent/children only
    pub(in crate::constraints::structural_kernel) fn publish(self, staged: StagedFormulaDelta);
}
```

`QueryCompletion<R>`はsuccessful scope exit専用のopaque receiptである。`new`、`Default`、`From`、public/restricted
field、candidate accessorを持たない。callerが作れる唯一の経路は、validationを終えた
`ScopedProjectionQuery`または`ScopedPublicationProjectionQuery`を`complete(value)`へconsumeすることだけである。
このmethodはscope内のprivate success candidateをreceiptへmoveする。query closureが`Err`を返す場合やscopeを
`complete`せずdropする場合はreceiptもcandidate publicationも生じない。wrapperだけが同じ`access.rs`内でprivate
`value` / `candidates`を取り出し、§3.7のterminal再check後にpublishする。

`access.rs`はsibling `gateway`の`ProofStructuralState`をnameでき、`gateway`は
`ActiveProofAttempt`をport signatureでnameできる。`read_view.rs`は`StructuralData`をnameできる。一方、
それぞれのfield/constructorはdefinition module privateなので、
siblingは値を偽造できない。

このlayoutの一部はstandalone prototypeのfuller type setで再検証済みである。positive buildは
`StructuralMutationIntent`、private-field `PreparedStructuralCommand`、`PreparedPayload`、`ReservedInsert`、
prototypeのgeneric `ProofWritePort`、`InFlightCommitGuard`を同時に含んでcompileした。external crateからprivate
`gateway`へ入るprobeはE0603、family siblingから`PreparedStructuralCommand` / prototype `ProofWritePort` fieldを
構築するprobeはE0451、private
`ReservationTicketId`利用もcompile failureになった。

ただしprototypeの`PreparedPayload`自体は`pub(in crate::structural_kernel)`であり、token-free
`MoveClaim { claim, target }` variantをsiblingが直接constructするnegative probeは無かった。またprototypeのquery
viewは単純な`pub`であり、rev.4のnarrow `ScopedProjectionQuery` signatureも検証していなかった。従ってprototypeが
証明したのは上記field/privacy probeだけであり、「全payload variantをsiblingがconstruct不能」「rev.4のexact
private boundがcompileする」とは主張しない。rev.5 production designはこの不足を、`PreparedPayload`をgateway
module完全privateにし、`ScopedProjectionQuery`を正確に`pub(in crate::constraints)`とすることで閉じる。

追加rule:

1. `gateway::storage`のraw fieldはprivate、raw mutatorは`pub(super)`以下とする。sibling
   `families::*`からは到達できない。
2. family handlerは裸の`&mut StructuralData`ではなく、gatewayがprivate payloadをdestructureして構築した
   command-specific `FormulaPublishPort<'_>` / `BoundsPublishPort<'_>`等とdata-only staged valueだけを受け取る。
3. port自身が対応するone-shot reserved operation/existing-key witnessをprivate fieldとして所有・consumeする。
   family handlerはport/tokenを構築、extract、clone、保存、再利用できない。
4. `families::*`を`gateway`のchildに移さない。`storage`をcommon parentへ置きraw mutatorを
   `pub(in crate::constraints::structural_kernel)`にするlayoutも採らない。
5. `structural_kernel::mod.rs`は`ProofAttemptKernel`、data-only typed intent、opaque scope-bound handle、committed
   mutation receipt、scope-bound query view、opaque `QueryCompletion<R>`だけを`pub(in crate::constraints)`でre-exportする。
   `ProofStructuralState`、`StructuralData`、success candidate internals、active capability、reservation ledger、write port、
   proof tokenはre-exportしない。
6. projection/publication両query wrapperは`pub(in crate::constraints)`であり、そのclosure boundへ現れる
   `ScopedProjectionQuery`、`ScopedPublicationProjectionQuery`、`ProjectionEvaluationRoundState`、
   `CpkPublicationEvaluationRoundState`、`QueryCompletion<R>`もexactly `pub(in crate::constraints)`として
   `structural_kernel/mod.rs`から同範囲へre-exportする。fields/constructor/cache portは`access.rs` privateのままにする。
   より狭い`pub(in crate::constraints::structural_kernel)`をscope typeへ使って`private_bounds` / private-type
   compile errorを起こさない。

compile-fail/UI gateはfilesystem上の配置だけでなく、family siblingからのraw storage access、write-port
constructor、reserved-operation constructor、`ExplicitNoOpProof` constructorが全て不可であることを固定する。

外部へ公開してよいもの:

- opaque IDs。
- data-only `StructuralMutationIntent` / opaque prepared handle / committed receipt。
- `ProofAttemptKernel::with_projection_query`のHRTB closure内だけに存在する`ScopedQueryView<'query>`。
- `ProofAttemptKernel`がterminal latch確認後にだけ呼ぶquery/cache operation。

公開してはならないもの:

- `&mut StructuralData`、各family storeへの`&mut`。
- `DerefMut`、`AsMut`、raw field visibility。
- caller closureへwrite capabilityを渡すgeneric callback。
- `StructuralWriteTxn` constructor。
- arbitrary codeが実装できるopen mutation trait。
- `ConstraintMachine`自身を`SemanticFactView`としてproduction preflightへ渡す経路。
- `ScopedQueryView`からvalidity cache、terminal latch、reservation ledger、kernel mutation portへ触るmethod。

`ProjectionPreflight`と`CpkProjectionEvaluator`は、migration完了後はconcreteな
`ScopedQueryView<'query>`だけをHRTB query closure内で受け取る。現行`SemanticFactView for ConstraintMachine`を
production authorityから外す。test adapterも`ProofAttemptKernel::with_projection_query`からclosureを実行する形に
限定し、view/referenceをcallerへ返さない。

`TypeArena`は既存IDのpayloadが不変なappend-only type-shape storeであることをSS0で再確認する。
`is_var_pos(PosId)`だけをimmutable side viewとして借用できる。既存Pos/Neg payloadのin-place mutationが
一件でも見つかれば、この例外を採らず該当type-shape factもsealed stateへ吸収する。

### 3.2 Public intent / private prepared command splitとmandatory disposition

callerが構築するrequestと、prepare後にreservation authorityを持つcommandを同じ型にしない。前者は
`commands.rs`のdata-only closed enum、後者はprivate `gateway`内だけで生まれる別のclosed enumである。

```rust
// commands.rs: caller-constructible。private token/prepared storage typeを含めない。
pub(in crate::constraints) enum StructuralMutationIntent {
    AdmitBound(BoundAdmissionIntent),
    PromoteBound(BoundPromotionIntent),
    TombstoneBound(BoundTombstoneIntent),
    AdmitConstraint(ConstraintAdmissionIntent),
    ExtendConstraintProof(ConstraintProofExtensionIntent),
    RecordProofOccurrence(ProofOccurrenceIntent),
    AdmitProjectionSupport(ProjectionSupportIntent),
    AdmitProjectionFormula(ProjectionClauseBatchIntent),
    AdmitUpperClaim(UpperClaimAdmissionIntent),
    MoveUpperClaim(UpperClaimMoveIntent),
    ChangeLiveCoverage(LiveCoverageChangeIntent),
    UpdateRowReduction(RowReductionChangeIntent),
    AdmitRowDerivation(RowDerivationIntent),
    AdmitReplayRelation(ReplayRelationIntent),
    AdmitQualifiedParent(QualifiedParentIntent),
    AdmitProjectionIndex(ProjectionIndexAdmissionIntent),
    AdmitOriginIdentity(OriginIdentityIntent),
    AdmitWitnessIdentity(WitnessIdentityIntent),
    AdmitSchemeInstantiation(SchemeInstantiationIntent),
    // SS0でcurrent production vocabularyを確定する。wildcard dispatchは禁止。
}

// gateway/mod.rs完全private。family siblingへpub(in ...)しない。
enum PreparedPayload {
    AdmitBound(PreparedBoundAdmission),
    PromoteBound(PreparedBoundPromotion),
    TombstoneBound(PreparedBoundTombstone),
    AdmitConstraint(PreparedConstraintAdmission),
    ExtendConstraintProof(PreparedConstraintProofExtension),
    RecordProofOccurrence(PreparedProofOccurrence),
    AdmitProjectionSupport(PreparedProjectionSupport),
    AdmitProjectionFormula(PreparedProjectionClauseBatch),
    AdmitUpperClaim(PreparedUpperClaimAdmission),
    MoveUpperClaim(PreparedUpperClaimMove),
    ChangeLiveCoverage(PreparedLiveCoverageChange),
    UpdateRowReduction(PreparedRowReductionChange),
    AdmitRowDerivation(PreparedRowDerivation),
    AdmitReplayRelation(PreparedReplayRelation),
    AdmitQualifiedParent(PreparedQualifiedParent),
    AdmitProjectionIndex(PreparedProjectionIndexAdmission),
    AdmitOriginIdentity(PreparedOriginIdentity),
    AdmitWitnessIdentity(PreparedWitnessIdentity),
    AdmitSchemeInstantiation(PreparedSchemeInstantiation),
}

// kernel siblingはouter typeをport signatureでnameできるだけで、private field/payloadを構築・抽出できない。
pub(in crate::constraints::structural_kernel) struct PreparedStructuralCommand {
    ticket: ReservationTicketId,
    payload: Option<PreparedPayload>,
}

// Prepared payload内部だけがprivate one-shot authorityを所有する。
struct PreparedProjectionClauseBatch {
    normalized_delta: FrozenProjectionDelta,
    formula_map_insert: Option<ReservedInsert<ProjectionFormulaByRecordDomain>>,
    entry_inserts: PreparedReservedOperations<ProjectionFormulaEntryDomain>,
}

enum StructuralMutationDisposition {
    Changed,
    Unchanged(ExplicitNoOpProof),
}

struct AppliedStructuralMutation {
    receipt: StructuralMutationReceipt,
    disposition: StructuralMutationDisposition,
}
```

`prepare(intent)`はpublic intentをexhaustive matchし、全fallible normalization/base capture/reservation後にprivate
`PreparedPayload`をprivate-field `PreparedStructuralCommand`へ包み、kernel arenaへ保存してopaque handleだけを返す。
external callerはprepared commandをnameできず、kernel siblingはrestricted-visibleな型名をport signatureへ使えても
struct field、`PreparedPayload`、`ReservedInsert`をconstruct/extractできない。prototypeではexternal accessがE0603、
kernel siblingからのouter struct literalがE0451、`compile_fail` doctestも成功した。ただしprototype自身の
`PreparedPayload`はkernel-wide visibleでtoken-free variant constructionを拒否していなかったため、その点を
prototype evidenceには数えない。production rev.5では`PreparedPayload`を`gateway/mod.rs`完全privateにする。

`prepare_intent`、`reservation_plan`、`try_prove_unchanged`、`dispatch_changed`は対応するclosed enumをwildcardなしで
matchする。intentへnew variantを加えればprepare mappingがcompile errorとなり、private `PreparedPayload`へnew
variantを加えればproof/dispatchがcompile errorとなる。二型のvariant correspondenceはSS0で一対一tableにし、
generic `PreparedPayload::Custom`、optional untyped side payload、caller-provided tokenを置かない。

mutating family handlerへ`StructuralMutationDisposition`を決めさせない。gatewayは§3.5.6の
`InFlightCommitGuard`が所有するprivate commandに対し、次の二択だけを実行する。

1. private allowlist proverが`Unchanged` proofを返したらwrite capabilityを作らず、ticketをreleaseして
   unchanged receiptをfinalizeする。
2. proofが無ければprepared payload内のone-shot operationsからwrite portを構築し、private commandを
   `dispatch_changed`してChanged receiptをfinalizeする。

本書でmandatory dispositionとは、gatewayが受理したmutation intentのsuccessful commitが必ず
`AppliedStructuralMutation { receipt, disposition }`を返すことを指す。family helperへclassificationを委ねない。
handlerが実write zeroで戻ってもproofが無ければChangedである。

`StructuralWriteTxn`はgatewayだけが構築できるscoped capabilityである。family handlerへbare prepared tokenを渡さない。
family siblingは`PreparedPayload`をmatchせず、
gatewayのexhaustive matchがvariantをdestructureした後にだけ、data-only staged valueとprivate-field
command-specific publish portを受ける。

```rust
// gateway/mod.rs private dispatch
match payload {
    PreparedPayload::MoveUpperClaim(prepared) => {
        let port = UpperClaimMovePublishPort::new(data, prepared.witnesses);
        families::proof::publish_upper_claim_move(port, prepared.staged)
    }
    // wildcard禁止
}
```

`UpperClaimMovePublishPort`は必要なticket/witnessを内部所有し、familyからconstruct/extractできない。token-freeな
logical no-op候補もprivate `PreparedPayload` variantとしてprepareだけが作るため、familyが直接variantを偽造して
gateway dispatchを迂回できない。`ProofStructuralState.data`はgateway moduleにprivateで、family moduleへ裸の
`&mut StructuralData`を渡さない。

### 3.3 Command-specific `Unchanged` proof

```rust
enum ExplicitNoOpProof {
    UpperClaimMove(UpperClaimMoveNoOpProof),
    ExactDuplicateBound(ExactDuplicateBoundNoOpProof),
    // 一件ずつ独立review後にだけ追加する。
}
```

token fieldとconstructorはprivate `unchanged_proofs` moduleだけが所有する。同moduleのproverは
read-only `StructuralData`と一つのtyped prepared commandだけを受ける。

```rust
fn prove_upper_claim_move_noop(
    data: &StructuralData,
    command: &PreparedUpperClaimMove,
) -> Option<(UpperClaimMoveNoOpProof, StructuralMutationReceipt)>;
```

proverはcommit-time allocation-free/infallibleでなければならない。集合のmaterialize/sort等が必要な比較は
allowlistへ入れない。prepareでfallibly構築したcanonical fingerprintを使う場合も、commitでcurrent baseと
fingerprint対象を再確認し、prover自身はbounded comparisonだけを行う。proof/receiptのためのheap allocationを
commitへ持ち込まない。

proofは少なくとも次を含む。

- prepared payload variant/kind。
- prepared target/relationship-local semantic base revision。global snapshotをproof baseにしない。
- target identity。
- comparisonしたauthoritative old/new projectionのfingerprintまたはtyped equality witness。

gatewayはproof variantとprepared payload variantをexhaustive matchで対応させ、別commandのproofを流用しない。
arbitrary handlerからgeneric `ExplicitNoOpProof::new()`を呼べるAPIを作らない。

重要なのは、proof成功時にmutating handlerを呼ばないことである。allowlisted commandへ将来new write branchを
追加しても、そのbranchはchanged handler側にしか存在できない。no-op semantics自体を変更する場合はprover/
proof variant/fixtureの変更が必要になる。compilerはそのsemantic更新を完全には強制しないため、allowlistは
小さく保ち、§10で独立査読する。

### 3.4 `commit_upper_claim_move`の具体的変換

current codeの次の形を禁止する。

```rust
fn commit_upper_claim_move(&mut self, mutation: &mut PreparedUpperClaimMove) {
    ...
    if old_record == mutation.current_record {
        return; // snapshot finalizer前
    }
    ... raw writes ...
    publish_structural_mutation_at(...);
}
```

移行後、mutation intentを発行した外部call siteはtyped move intentをprepareし、handleをgatewayのcommitまたは
cancelへ必ず返す。

```text
MoveUpperClaim prepared command
    |
    +-- SS8でsame-record no-op proofがallowlist済み
    |      -> read-onlyにclaim occurrence/current-record/index closureを比較
    |      -> mutating handlerを呼ばずUnchanged finalizer
    |
    `-- proofなし（SS1〜SS7のbaselineを含む）
           -> changed handler
           -> same-recordでwrite zeroでもChanged finalizer
```

外部functionが`with_structural_inspection` query scopeだけを使い、gatewayへmutation intentを渡す前に「何もしない」
と決めてowned decisionをreturnすることは許される。そのpathはstructural commandの成功ではなく、disposition/
finalizerを要求しない。raw stateもreceiptも変更できないため、cache under-invalidationは起こさない。

一方、prepareへintentを渡した後はopaque handleをcommit/cancelせずreturnしてはならず、commitが
`Applied`を返す全pathはsingle finalizerを通る。gateway call後にcallerがreturnしてもfinalizerは既に完了して
いる。changed handler内部のearly returnはreceiptとしてgatewayへ戻り、`Applied::changed`がfinalizeされる。
これがround 6のfatal gapを構造的に閉じる。

従って本書のmandatory-disposition guaranteeの正確な範囲は、**gatewayへmutation intentが到達し、successful
commitとして受理されたoperation**である。caller-side precheckだけでcommandを発行しないpure no-opを
「successful operation」と数えない。precheck前後にcache-relevant write、prepared receipt、secondary
publicationが一件でもあるならpure no-opではなく、この例外を使えない。

### 3.5 Semantic baseとshared-resource reservationを分離するprepare/commit protocol

#### 3.5.1 Global snapshotをwriter conflictへ使わない

`ProofStructuralSnapshotId`の唯一の役割は**completed structural stateのcache invalidation identity**である。
次のいずれにも使ってはならない。

- prepared commandのsemantic conflict base。
- capacity reservation ticketのvalidity判定。
- unrelated writerがcommitしたことを理由にprepared commandをrejectするglobal epoch。

これはactual production coordinatorとCPK-SV-C redesignが許可する次のinterleavingを維持するための必須条件で
ある。old raw-store fixtureをgateway gateの代用にはしないが、semantic compatibility baselineとして残す。

1. **actual production order**: claim prepare → formula prepare → claim commit → formula commit。
2. existing compatibility order: formula prepare → claim initial publication/move commit → formula commit。
3. move prepare → new formula commit → move commit。

formula commandのsemantic baseへcurrent claim/live authorityを入れない。frozen `expected_root`を持つformulaと
current claim/live authorityの関係はquery-time late bindingで検証する。move commandのsemantic baseへformula
bucket revisionを入れない。従って上の異種writer commitはglobal snapshotを進めても互いをconflictさせない。

#### 3.5.2 二種類のprepare artifact

opaque prepared objectは、semantic dependencyとphysical capacityを別々に保持する。

```rust
struct PreparedStructuralMutation {
    command: PreparedStructuralCommand,
    semantic_bases: Vec<StructuralBaseStamp>,
    reservation: StructuralReservationTicket,
    // normal modeではSome。reuse-disabled modeのNoneをcross-attempt equality keyとして使わない。
    attempt_nonce: Option<ProofAttemptNonce>,
}

enum StructuralBaseStamp {
    FormulaRecord { record: BoundRecordId, expected: ExpectedSlot<FormulaRevision> },
    UpperClaim { claim: UpperReplayClaimId, expected: ExpectedSlot<ClaimRevision> },
    BoundRecord { record: BoundRecordId, expected: ExpectedSlot<BoundRevision> },
    ConstraintRecord { constraint: ConstraintRecordId, expected: ExpectedSlot<ConstraintRevision> },
    RowState { state: RowReductionStateId, expected: ExpectedSlot<RowStateRevision> },
    IdentitySlot { key: StructuralIdentityKey, expected: ExpectedSlot<IdentityRevision> },
    // SS0でactual read-setに沿ってclosed vocabularyを確定する。global snapshot variantは禁止。
}

enum ExpectedSlot<R> {
    Absent,
    Present(R),
}

enum StructuralResourceDomainKey {
    ProjectionFormulaByRecordMap,
    ProjectionFormulaBucketEntries(BoundRecordId),
    ProjectionFormulaExactLinks(BoundRecordId),
    UpperClaimByRecordMap,
    UpperClaimsInRecord(BoundRecordId),
    LiveStatesByCoverageRootMap,
    LiveStatesInCoverageRoot(UpperReplayClaimId),
    BoundRecords,
    ConstraintRecords,
    RowReductionRecords,
    IdentityRecords(IdentityFamily),
    // SS0でcommit-time new-key insertionを行うshared containerを全件closed enum化する。
}

struct ReservationClaim {
    domain: StructuralResourceDomainKey,
    units: usize,
}

struct StructuralReservationTicket {
    ticket_id: ReservationTicketId,
    claims: Vec<ReservationClaim>,
    attempt_nonce: Option<ProofAttemptNonce>,
}
```

`StructuralBaseStamp`は「prepareがdeltaを作るために読んだauthoritative targetがcommit時にも同じか」を
判定する。target-local/relationship-localであり、無関係なstate changeをrejectしない。

missing targetも`ExpectedSlot::Absent`としてbaseに含める。同じmissing targetへ二commandをprepareした場合、
一方のinsert後に他方は`Absent -> Present` mismatchとなる。distinct missing A/Bは互いをinvalidateしない。
present revisionはnon-wrapping/non-reusedとし、delete/recreateを許すfamilyはslot generation/tombstoneを保持して
ABAを防ぐ。revision/generation saturation時は次のchanged prepareをwrite前にtyped `ResourceExhausted`として
拒否し、wrapして古いprepared baseと再一致させない。

上の`Vec`はprepareが必要件数を数え、`try_reserve_exact`後に構築してfreezeする。commitでpush/cloneせず、
opaque prepared objectからmoveして消費する。実装時にinline storageを選ぶ場合も、overflow growthをinfallible
fallbackへしない。

このwrapperと`PreparedStructuralCommand`はgateway privateである。`PreparedStructuralMutationHandle<'scope>`は
arena slot identityしか持たず、command/payload/ticketをcallerへ露出しない。public
`StructuralMutationIntent`からこのwrapperへの変換は`prepare()`だけが行う。intent typeへprivate tokenをoptional
fieldとして混ぜる設計、またはprepared commandからtokenを別side tableへ切り離してfamily handlerへ再結合させる
設計は採らない。

`StructuralReservationTicket`は「shared containerのcommit-time capacityを、同時にoutstandingな別prepared
commandと二重計上していないか」を保証する。ticketはsemantic conflictを表さず、別target A/Bをrejectしない。

#### 3.5.3 Reservation ledgerとcapacity invariant

sealed gatewayはresource domainごとに次のcontrol metadataを持つ。

```rust
struct ReservationDomainState {
    outstanding_units: usize,
    pending_empty_prune: bool,
}

struct StructuralReservationLedger {
    // attempt-global。domainごとではない。Some(1)から開始し、発行済み値を再利用しない。
    next_ticket_id: Option<NonZeroU64>,
    domains: FxHashMap<StructuralResourceDomainKey, ReservationDomainState>,
    active_tickets: FxHashMap<ReservationTicketId, ActiveReservationTicket>,
}

#[repr(transparent)]
struct ReservationTicketId(NonZeroU64);
```

`StructuralReservationLedger`は`ProofStructuralState`に一つだけ存在するattempt-local ownerである。
`next_ticket_id`をresource domain stateへ置かない。ticketが一domainでも複数domainでも、ledgerからIDを一回だけ
取得し、その一IDの`ActiveReservationTicket`が全`ReservationClaim`を所有する。

ID allocationは次で固定する。

```rust
fn take_next_ticket_id(
    ledger: &mut StructuralReservationLedger,
) -> Result<ReservationTicketId, ProofFailure> {
    let raw = ledger.next_ticket_id.take().ok_or(ProofFailure::ResourceExhausted {
        operation: ProofOperation::PrepareStructuralMutation,
    })?;
    ledger.next_ticket_id = raw.get().checked_add(1).and_then(NonZeroU64::new);
    Ok(ReservationTicketId(raw))
}
```

`Some(NonZeroU64::new(1).unwrap())`から開始する。`u64::MAX`を最後の一IDとして発行した後は`None`となり、以後の
prepareをwrite/ticket publication前にtyped `ResourceExhausted`で拒否する。wrap/reuseしない。同一attempt内の
formula-domain first ticketとclaim-domain first ticketはdomain-local ordinalに関係なく異なるIDになる。
normal modeの`Some(attempt_nonce)`はcross-attempt stale handle検出用であり、same-attempt ticket uniquenessの
代用品にしない。reuse-disabled modeの`None`同士を同一attemptの証拠として比較してはならない。このmodeでは
scope-bound handleとkernel-owned arena slotの直接ownershipだけをcommit/cancel authorityとし、round/cacheを含む
cross-call reuseを全て禁止する。new `ProofAttemptKernel`構築時だけledgerを`Some(1)`へ初期化する。同一attemptの
terminal latch clear/recovery/test hookでcounterをresetしない。

global fixed containerのdomain stateはstate生成時に持つ。per-record/per-root containerのdomain stateが必要な
場合、そのledger entryの作成もprepareのfallible phaseで行う。missing target用にnew child containerが必要なら、
child container自体はprepared objectがowned candidateとして持ち、shared parent mapへの一slotだけをticketで
予約する。

各domainで常に次を維持する。

```text
physical_spare_capacity(domain) >= outstanding_units(domain)
```

prepareはintent/prepared-payload variantをexhaustive matchする`reservation_plan(command, current_data)`でdomain別unitsを
集約し、各domainについて次を行う。

```text
required_spare = outstanding_units + requested_units
if physical_spare_capacity < required_spare:
    resource_adapter.try_ensure_spare(required_spare)?
all domain reserves succeeded:
    reserve active_tickets capacity for exactly one new global entry
    verify next_ticket_id is Some and all outstanding additions do not overflow
    allocate exactly one attempt-global ticket ID
    add every domain's outstanding_units
    publish one active ticket carrying the whole multi-domain claim vector
```

複数domainの途中までcapacity growthして後続`try_reserve`が失敗しても、authoritative semantic dataはまだ
変わっていない。余ったcapacityは害のないreserveとして残し、ticket/outstanding countは全domain成功後にだけ
publishする。ledger自身のmap/claim buffer capacityもこのfallible phaseで確保する。

ID発行とticket publicationの直前までに、shared containers、domain entries、claim buffer、prepared arena、
`active_tickets`、current preparation scopeの`live_slots`の全fallible reserveと全checked arithmeticを完了する。
`live_slots`へ一slot追加できないprepareはID発行前にtyped `ResourceExhausted`を返す。その後はsingle-threaded
gateway内のallocation-free sequenceとして、(1) attempt-global IDを一回取得、(2) `active_tickets.entry(id)`と
prepared arena slotがvacantであることを確認、(3) one active ticket/one arena entryをinsert、(4) arena slotを
scope `live_slots`へpush、(5) domain outstandingを全件加算する。vacant check failureはdomain counter変更前のtyped
invariant failureとし、別ticketをoverwriteしない。ID counterが進むだけでsemantic/ticket stateは変わらない。
vacant確認後は途中return/`?`を置かず、一exclusive method return時にactive entry、arena entry、scope ownership、
domain countersを同時に可視化する。

multi-domain ticketをdomainごとのsub-ticketへ分割せず、release/cancel/commitはglobal IDで一つのactive entryを
takeした後、そのentry内の全claimをexactly once処理する。これにより異domain ticket collision、multi-domain
partial alias、wrong-domain double releaseを防ぐ。

`try_ensure_spare(required_spare)`はstandard `HashMap::try_reserve` / `Vec::try_reserve`のargumentが
「現在の`len`に加えて収容する件数」であることを踏まえ、`container.try_reserve(required_spare)`を呼んでから
`capacity - len >= required_spare`を確認するdomain adapterである。**不足差分**
`required_spare - current_spare`を`try_reserve`へ渡してはならない。free slotが既に一つある場合、差分一件の
`try_reserve(1)`はno-opになり、同じslotの二重計上を再導入するためである。

後発prepareの`try_reserve`はshared containerをrehash/reallocateし得る。従ってoutstanding prepared objectは
shared container内へのreference、pointer、iterator、`RawEntry` handleを保持しない。owned candidate、stable ID、
numeric index（index stabilityが別invariantで保証される場合だけ）、semantic base stampだけを持ち、commit時に
current containerから再resolveする。これを守れないprepared representationはticket protocolへ移行できない。

重要な例は、同じ`by_record` mapに対するdistinct missing formula target A/Bである。free slotが一つの時、Aの
prepare後は`outstanding=1`になる。B prepareは同じfree slotを再利用可能と数えず、二件分のspareになるまで
fallibly reserveしてからticketを発行する。A commitは`len += 1`と同時にAのoutstanding unitをconsumeするため、
B分の`physical_spare >= outstanding` invariantが残る。従ってA/Bはどちらの順でもallocation-freeにcommitできる。

#### 3.5.4 Outstanding reservationによるchild-container pinning

per-record/per-root child containerは、そのchild domainの`outstanding_units > 0`である間、emptyになってもparent
mapからremoveしない。rev.3で採った**pin empty containers while units are outstanding**をrev.5も維持する。

current codeでempty childをremoveする次のpathは、sealed移行時にgateway write portへ置換する。

- `claims_by_upper_record`のlast claim removal
  （current `crates/infer/src/constraints/proof/mod.rs:7505`付近）。
- `live_states_by_coverage_root`のlast state removal
  （current `crates/infer/src/constraints/proof/mod.rs:13013`付近）。

```rust
fn prune_claim_record_if_empty(
    txn: &mut StructuralWriteTxn<'_>,
    record: BoundRecordId,
) {
    if !txn.data.claims_in_record(record).is_empty() {
        return;
    }
    let domain = StructuralResourceDomainKey::UpperClaimsInRecord(record);
    if txn.reservations.outstanding_units(domain) != 0 {
        txn.reservations.mark_pending_empty_prune(domain);
        // parent map entryとempty Vec capacityを保持する。
        return;
    }
    txn.remove_empty_claim_record_container(record);
}
```

live-state setも同じruleを使う。pinned empty childはsemantic read上`Absent`と同じであり、canonical cursor、support
closure、dependent fanoutへempty categoryを露出しない。ただしphysical parent slotとchild capacityは保持する。
従ってoutstanding ticketが予約したcapacityは、別commitのlast-element removalで消えない。

ticket consume/release後にそのdomainの`outstanding_units`がzeroになった時、ledgerは
`pending_empty_prune`を確認する。childが依然emptyならgatewayのcontrol cleanupがparent mapからremoveする。
途中で別commitがentryを追加してnonemptyになったならflagだけclearする。pruneはremove-onlyでallocation-free、
semantic setを変えないrepresentation cleanupなのでsnapshotをbumpしない。query viewはpin有無を観測しない。

prepared ticketが存在する間はcontainer generationを変えず、remove/recreate conflictへ倒さない。このpin ruleに
よりapproved異種writer interleavingをspurious conflictにしない。outstanding zero後にpruneされ、後のprepareが
recreateする場合は、通常どおりparent-map slotとowned child candidate capacityの両方を新ticketで予約する。

child domain ticket発行時にはparent map entryが存在すること、child capacityがrequired spareを満たすこと、
`outstanding_units` incrementがpin acquisitionになることを一つのallocation-free publication sequenceで行う。
ticket release、semantic conflict、explicit cancel、scope drop、terminal cleanupの全pathが同じunpin/prune helperを
使い、別々のmanual cleanupを持たない。

#### 3.5.5 Ticketを要求するwrite port

family handlerへnormal `HashMap::insert` / `Vec::push`を直接公開しない。prepareはticketの各unitから、payload/
targetへ結び付いたone-shot `ReservedInsert`を構築してprivate prepared commandへ格納する。constructorは
gateway-private、`Clone`/`Copy`不可であり、gatewayがprivate payloadをdestructureしてcommand-specific publish portへ
移した後、そのport operationがvalueとしてconsumeする。

```rust
struct FormulaBucketPublishPort<'write> {
    data: &'write mut ProofRelations,
    reserved: ReservedInsert<
        ProjectionFormulaByRecordDomain,
        (BoundRecordId, ProjectionFormulaBucket),
    >,
}

impl FormulaBucketPublishPort<'_> {
    // callerはkey/valueだけを渡す。reserved authorityはport内部から一回だけconsumeされる。
    fn publish(self, key: BoundRecordId, value: ProjectionFormulaBucket)
        -> InsertedFormulaBucket;
}
```

dynamic N件ならprepareがfallibly reserveした`Vec<ReservedInsert<...>>`をgateway-private multi-insert portへmoveし、
portのclosed publish methodが`into_iter()`でone-shot tokenを消費する。operationはtokenの
ticket-unit/domain/target bindingをfirst write前に確認し、
`physical_spare > 0`をdebug/test assertionする。existing-key replacement/remove後のsame-commit reinsertionを
capacity creditとして使う場合も、prepareがbaseに結び付けたone-shot `ExistingSlotWitness`を発行し、write portが
consumeする。

handlerがexisting semantic pathへnew insert branchを追加しても、family moduleは`ReservedInsert`を構築できず、
既存tokenはvalue consume後に再利用できない。従って対応するprepare delta/token/reservation planを追加しない
new insertionはcompileしない。単なる「runtime units counterを減らしてzeroならpanic」という設計は採らない。
raw container insertをfamily siblingへ公開しない。

write portにgeneric `entry().or_insert*`、`upsert`、raw mutation closureを置かない。existing-key updateは
prepare/base-checkが発行したtyped `ExistingKeyWitness`を要求し、missingならwrite前semantic conflictになる。
insertとupdateを一つのruntime branch APIへ畳まない。

`reservation_plan`はclosed `StructuralMutationIntent`、`dispatch_changed`はclosed private
`PreparedPayload`をwildcardなしでmatchする。intent→prepared mapping tableと両matchの更新をcompilerが
要求する。既存prepared variant内部のnew insert branchもprivate one-shot tokenを必要とする。
これはdispositionのconservative defaultとは別の、commit-time allocation safetyのclosureである。

#### 3.5.6 Commit、conflict、cancel

prepareはfallibleであり、ID conversion、candidate delta、semantic bases、全resource ticketをkernel-owned
`PreparedMutationArena`へ保存する。callerへticket ownershipを渡さない。rev.3で採った
**exclusive kernel ownership of all live prepared mutations**をrev.5も維持し、arena take後だけ専用guardへ移す。

```rust
impl ProofAttemptKernel {
    pub(in crate::constraints) fn try_with_structural_preparation_scope<R>(
        &mut self,
        f: impl for<'scope> FnOnce(
            &mut StructuralPreparationScope<'scope>,
        ) -> Result<R, ProofFailure>,
    ) -> Result<R, ProofFailure>;
}

pub(in crate::constraints) struct PreparedStructuralMutationHandle<'scope> {
    slot: PreparedMutationSlotId,
    scope_nonce: PreparationScopeNonce,
    _invariant: PhantomData<&'scope mut ()>,
    // ticket/command/data ownershipは持たない。
}

struct StructuralPreparationScope<'scope> {
    active: ActiveProofAttempt<'scope>,
    structural: &'scope mut ProofStructuralState,
    scope_nonce: PreparationScopeNonce,
    live_slots: Vec<PreparedMutationSlotId>, // entry capacityはscope開始/prepareでfallibly確保
}
```

HRTBの`'scope`とinvariant markerによりhandleをclosure return value、machine field、queueへescapeさせない。
handleはnon-`Clone`/non-`Copy`でcommit/cancelがconsumeする。ただしhandleを単に`drop(handle)`してもticketは
handle内にない。kernel arenaのslotとscopeの`live_slots`がownershipを保持し、scope終了時に必ずcleanupする。

`StructuralPreparationScope`はreal `Drop`を持つ。

```rust
impl Drop for StructuralPreparationScope<'_> {
    fn drop(&mut self) {
        self.structural.cancel_scope_slots_and_release_tickets(
            self.scope_nonce,
            &mut self.live_slots,
        );
    }
}
```

`?`、ordinary handle drop、early return、panic unwindはいずれもscope `Drop`へ到達し、**arena内に残る**
uncommitted entryをtake、global active ticketをtake、全domain unitsをrelease、§3.5.4のpending empty childを
pruneする。Drop pathはallocation-free/infallibleであり、borrow conflictを起こす`RefCell` control registryを
使わない。abort時はprocess state自体を再利用しないためcleanupを要求しない。

ただしscope `Drop`だけでは、commitがarena entryをtakeした後からfinishまでを所有できない。rev.5はこのwindowを
専用RAII guardで閉じる。

```rust
struct InFlightCommitGuard<'state> {
    state: &'state mut ProofStructuralState,
    prepared: Option<PreparedStructuralMutation>,
}

impl<'state> InFlightCommitGuard<'state> {
    fn take(
        state: &'state mut ProofStructuralState,
        slot: PreparedMutationSlotId,
    ) -> Result<Self, StructuralCommitError> {
        let prepared = state.prepared.take(slot)?;
        // `prepared`のmoveからguard constructionまでfallible/panicking callを挟まない。
        Ok(Self { state, prepared: Some(prepared) })
    }

    fn finish(mut self) -> PreparedCommitParts {
        let prepared = self.prepared.take().expect("in-flight ownership");
        self.state.release_ticket_and_collect_parts(prepared)
    }
}

impl Drop for InFlightCommitGuard<'_> {
    fn drop(&mut self) {
        if let Some(prepared) = self.prepared.take() {
            self.state.release_taken_prepared_infallibly(prepared);
        }
    }
}
```

`take_prepared()`を単独で外へ公開せず、arena removalとguard constructionを一つのprivate functionへ閉じる。以後の
semantic-base error、ticket error、no-op prover errorを`?`で返してもguard `Drop`がreleaseする。prototypeはarena
take直後のdeliberate panicとearly errorを実行し、unwind後に`active_tickets == 0`、
`outstanding_units == 0`を確認した。

actual claim/formula coordinatorは一つのscope内でclaim prepare、formula prepare、claim commit、formula commitを
行う。move/formula等、複数outstanding prepareを必要とするtransactionも同じscopeへ入れる。scopeは一つの
coordinator operationを越えて保存せず、nested/parallel scopeを許さない。explicit `scope.cancel(handle)`は早期に
releaseできるがcorrectnessはcallerがcancelを忘れないことへ依存しない。

commitは次を厳守する。

1. §3.7のactive-attempt capabilityを再確認する。
2. `InFlightCommitGuard::take`でarena entryとticket ownershipを同時にguardへ移す。
3. handle/ticketが同一attemptでactiveか確認する。以後のearly return/panicはguardがcleanupする。
4. `StructuralBaseStamp`だけを**write capability構築前**に比較する。global snapshotは比較しない。
5. base mismatchはtyped conflictを返し、guardがticketをreleaseする。data、snapshot、cache、receiptを変更しない。
6. no-op proofをcurrent semantic basesに対して再評価する。prepare時proofをblindに再利用しない。
7. proof成立ならguardから全ticket unitsをreleaseし、`Unchanged` finalizerへ進む。
8. proof不成立ならprepared commandとtokenから**authoritative storageへ触れないstaged replacement/delta**を完全構築する。
9. 全comparison、ID conversion、capacity check、debug assertion、receipt constructionを最初のauthoritative write前に
   終える。その後、private non-panicking publication primitiveだけでstaged valueをmove/swapする。
10. handlerがconsumeしなかったreserved operations/余剰unitをguardのfinishへ返す。全token accountingをwrite前に
    検証し、write後にpanicし得るassertを置かない。
11. publication完了後、guardをfinishしてsingle finalizerがsnapshotを一回bumpし、old-snapshot cache entriesを
    clearする。

#### 3.5.7 Changed handlerのpanic atomicity: build fully, then publish

`InFlightCommitGuard`が機械的に保証するのはreservation ownershipであり、partial authoritative writeのsemantic
rollbackではない。rev.5はrollback journalを一般化せず、**build fully, then non-panicking move/swap**を全changed
handlerのmandatory patternにする。

1. handlerはまずowned staged output、receipt、index delta、replacement aggregateをfallibly構築する。このphaseは
   `StructuralData`へwriteしないためpanic/`Err`でもsemantic stateは不変である。
2. publication phaseへ入る前にbase/token/unit/targetを全検証する。
3. publication phaseはpre-reserved storageへのtyped move、existing-slot replacement、または一つのowner aggregateの
   `mem::replace`だけで構成し、allocation、hash/equality callback、user `Drop`、closure、formatting、assert、`?`を
   呼ばない。old valuesのdropがpanicし得る型はその場でdropせずguard-owned retire listへmoveし、finalizer後の
   non-authoritative cleanupで処理する。
4. 複数field/containerを一logical commandとして変える場合、transient intermediate stateはexclusive borrowで外から
   観測不能であるだけでなく、各publication primitive自体がpanic-freeでなければならない。rev.5のstanding patternは
   **closed prepared publication plan + audited panic-free typed primitives**である。一般rollback journalやwhole-family
   clone/swapをdefaultにはしない。

```rust
// familyごとにclosed enumを定義する。open trait/object/callbackは禁止。
enum PreparedProofPublicationOp {
    InsertFormulaRecord(ReservedFormulaRecordInsert),
    ReplaceFormulaBucket(PreparedFormulaBucketReplace),
    InsertExactLink(ReservedExactLinkInsert),
    RemoveLiveFlat(ExistingLiveFlatWitness),
    RemoveLiveRootChild(ExistingLiveRootChildWitness),
    InsertProjectionTarget(ReservedProjectionTargetInsert),
    InsertProjectionPremise(ReservedProjectionPremiseInsert),
    // SS0でactual multi-container write primitiveを全件closed化する。
}

struct PreparedProofPublicationPlan {
    operations: Vec<PreparedProofPublicationOp>, // prepareでfallibly容量確保済み
    receipt: StructuralMutationReceipt,
    retired: PreReservedRetireList,
}
```

prepare/staging phaseは全key hash、key equality、presence/absence lookup、tree path、index conversion、assertion条件、
receipt、operation順序をauthoritative first write前に解決する。publish phaseが扱えるkeyは`BoundRecordId`等の
audited `Copy` ID/newtypeに限定し、その`Eq`/`Hash`とselected hasherがpanic-freeであることをSS0 tableへ記録する。
arbitrary user key、trait-object hasher/equality、closure、formatting、`assert!`/`expect`をprimitiveへ渡さない。

各primitiveはpre-reserved one-shot tokenまたはexisting-slot witnessをconsumeし、new allocationを伴わないinsert、
remove、slot replacementだけを行う。replacementで生じたold valueはその場でdropせずpre-reserved retire listへmoveする。
`Prepared*PublicationPlan::publish`はclosed enumをwildcardなしで順にconsumeし、first write後にbranch failure、`?`、
assertion、hash/equality callback failure、user `Drop`を持たない。この条件により、複数containerへのsequential
publicationでも途中unwind point自体をzeroにし、general rollbackを不要にする。

SS0は少なくとも次をこのpatternへ割り当てる。

- `commit_projection_formula_shadow_delta`: formula record/bucket、exact-link、support/index treeの全lookupと比較を
  staged planへ移し、raw `HashMap::insert` / `assert!` / `expect`をpublication phaseから除く。
- `record_prepared_live_coverage`: flat live setとroot→states childのinsert/remove、last-child pin/prune decisionを
  一つのclosed live publication planへする。
- `commit_projection_index_admission`: target map、premise map、child setsのtarget-only/edge-only/both branchをprepareで
  固定し、対応するreserved operationをplanへ全て持たせる。

あるfamilyがこのclosed primitive setへ落とせない場合、whole-family clone/swapへ自動fallbackしない。そのfamilyの
cache-relevant migrationを停止し、より小さなco-owned replaceable aggregateへstate ownershipを再分割する設計変更を
先に独立査読する。command-specific rollbackは本書のbaseline mechanismではなく、別途signed addendumなしに導入しない。

whole proof-family aggregateのclone/swapをbaselineにしない理由は、巨大map cloneのcostだけではない。同じshared mapの
distinct formula A/Bを同時prepareする§3.5 interleavingで、whole aggregate revisionをsemantic baseにするとA commitが
Bをspurious conflictにし、baseを粗くするとB swapがAをlost-updateし得る。closed primitive planはtarget-local baseと
resource ticketを維持したまま、panic-capable workだけをpre-write phaseへ移せるため、本書のapproved interleavingと
両立する。

従って「changed handlerはinfallible」という既存文言は、単に`Result`を返さないことではない。最初のauthoritative
write後にRust unwindを開始し得るoperationがzeroであることを、familyごとのclosed operation table、concrete
`Eq`/`Hash`/drop audit、static review、deliberate panic injection fixtureで示す契約である。prototypeのRAII testは
このsemantic atomicityまでは証明していない。

explicit cancelはscope-owned arena entryを即座にtakeする。prepare後のcaller failure/handle dropはscope `Drop`、
attempt-terminal transitionはactive scopeをterminal-marking callのreturn時にunwind、attempt teardownは最後の
defensive `cancel_all_prepared(attempt_nonce)`でticketをreleaseする。terminal latch後はcommitを許さないが、ticket
cleanupだけはcache-relevant mutationではないcontrol operationとして許す。quiescent/scope-exit/teardown gateは
prepared arena entry、active ticket、全domain outstanding unitsがzeroであることを要求する。

attempt-global ticket IDは同一attempt内で再利用しない。counter exhaustion時はnew prepareをtyped
`ResourceExhausted`として拒否し、wrapしたIDでold ticketを再活性化しない。

同一attemptでsibling mutationが既にcommit済みの後に**semantic conflict**した場合は、CPK-SV-C-R0の
terminal-failure/whole-attempt discard規則を維持する。gatewayがlocal retryを勝手に開始しない。一方、異種
writerがglobal snapshotを進めただけ、またはdistinct targetが同じshared container ticketを持つだけでは
conflictにしない。

failed prepare、commit conflict、cancel、whole-attempt discardはsuccessful commitではなくsnapshotをbumpしない。
reservation ledgerのticket publish/releaseもsemantic mutationではないためsnapshotをbumpしない。

### 3.6 Evaluator capacity contract

current `project_lower_inner`（`crates/infer/src/constraints/proof/mod.rs:10007`付近）はpreflight後に次で
evaluator mapをreserveする。

```text
evaluation_nodes = checked_records.len() + checked_constraints.len()
states.try_reserve(evaluation_nodes - states.len())
```

same-snapshot cache hitはclosure expansionをskipするため、checked setはevaluatorが訪れるnode数の上限では
なくなる。この値をallocation safetyの根拠に使わない。

採る設計は**全production evaluator entrypointの`Result`化と、every insertion-site fallibility**である。

```rust
fn try_enter(
    &mut self,
    node: ProofEvalNode,
) -> Result<Option<ProofEvalMemo>, ProofFailure> {
    match self.states.get(&node).copied() {
        Some(Done(memo)) => Ok(Some(memo)),
        Some(Visiting) => { self.cycle_cuts += 1; Ok(Some(cycle_cut_memo())) }
        None => {
            self.states.try_reserve(1).map_err(|_| ProofFailure::ResourceExhausted {
                operation: ProofOperation::ProjectLowerEvaluation,
            })?;
            self.states.insert(node, Visiting);
            Ok(None)
        }
    }
}
```

`eval_record_memo`、constraint/root recursion等を`Result`伝播へ変える。`finish`は既存`Visiting` keyのvalueを
`Done`へ置換するだけなので新allocationを要求しない。将来別mapへnew keyをinsertする場合も同じ
insertion-site fallibilityを要求する。

旧checked-count bulk reserveは削除するか、miss pathのpure optimization hintとしてだけ残す。残す場合も
`try_enter`を必須backstopとし、hintの正確性をcorrectness/fallibility contractに使わない。

この方法はper-new-node `try_reserve(1)` costを追加する。SS6/SS7でcache-heavy RMWとcold stdを測り、必要なら
fallible geometric chunk reserveへ最適化してよい。ただしinfallible `insert`前にcapacityが保証される契約を
弱めない。

#### 3.6.1 Publication-time evaluatorも同じ契約へ入れる

current productionには、fallible `project_lower`だけでなく
`CpkPublicationEvaluationRound::eval_record() -> bool`
（`crates/infer/src/constraints/mod.rs:1212`付近）もある。このpathを例外にしない。SS6で次へ変更する。

```rust
impl ProofAttemptKernel {
    fn eval_publication_record(
        &mut self,
        type_shapes: &TypeArena,
        round: &mut CpkPublicationEvaluationRoundState,
        record: BoundRecordId,
    ) -> Result<bool, ProofFailure>;
}

impl CpkProjectionEvaluatorFacade<'_> {
    fn eval_record(&mut self, record: BoundRecordId) -> Result<bool, ProofFailure>;
    fn eval_record_memo(&mut self, record: BoundRecordId) -> Result<ProofEvalMemo, ProofFailure>;
    fn eval_root_memo(
        &mut self,
        root: UpperReplayClaimId,
    ) -> Result<ProofEvalMemo, ProofFailure>;
}
```

publication-time evaluatorを呼ぶ全production chainも`Result`を返す。allocation failure時は、対象decisionと
それに続くsemantic publication/fanoutを開始せず、`ProofOperation::ProjectLowerEvaluation`のtyped failureを
`ProofAttemptKernel::mark_terminal_once`へ渡してwhole attemptを停止する。既にsibling core/proof mutationが
commit済みなら既存ruleどおりattempt全体をdiscardし、local fallbackでpublicationを続けない。attempt outputは
terminal attemptから外部commitされないため、allocation failureを`false`へ変換したpartial successとして
観測させない。

current `constraints/mod.rs`の少なくとも次のchainを同じsliceで`ProofKernelResult`へ変える。

- `record_scheme_projection_liveness_mutation`。
- `apply_scheme_projection_mutation` / `evaluate_cpk_scheme_projection_mutation`。
- `evaluate_record_inclusion_publication`。
- `try_evaluate_projection_inclusion_snapshot`内のafter evaluation。
- `scheme_projection_record_is_included`。
- `projection_inclusion_snapshot` / `publish_projection_inclusion_snapshot`。

`projection_inclusion_snapshot`のresult mapも、既知record件数に対して`try_reserve`した後にloop insertし、
infallible `collect::<FxHashMap<...>>()`を残さない。各callerはsuccessful `Result`を得るまで
`publish_scheme_projection_intent`やowner fanoutを呼ばない。failureを`None`/empty/unchanged/`false`へ変換する
convenience wrapperをproductionへ置かない。

#### 3.6.2 Override storageもfallibleにする

current `record_overrides` / `root_overrides`のbuilder insert
（`proof/mod.rs:11538` / `11547`付近）も例外にしない。次のfallible setterへ置換する。

```rust
fn try_set_record_override(
    &mut self,
    record: BoundRecordId,
    result: bool,
) -> Result<(), ProofFailure> {
    if !self.record_overrides.contains_key(&record) {
        self.record_overrides.try_reserve(1).map_err(project_lower_exhausted)?;
    }
    self.record_overrides.insert(record, result);
    Ok(())
}

fn try_set_root_override(
    &mut self,
    root: UpperReplayClaimId,
    result: bool,
) -> Result<(), ProofFailure>;
```

`CpkPublicationEvaluationRound::{new_with_overrides, with_record_result_override,
with_root_result_override}`とtest round constructorは`Result`を返し、override reservation failureをcallerへ
伝播する。test-only convenienceで`unwrap`する場合もproduction constructorと同じfallible setterを通す。
`states`、`record_overrides`、`root_overrides`、および将来追加するevaluator map/setのnew-key insertをSS6の
static/runtime inventoryで全件列挙し、allocator-failure fixtureを各storageで持つ。

### 3.7 Active-attempt capabilityとterminal latchの調停

本書の「failureをcacheしない」はsuccessful structural-validity mapの値域を制限する規則である。既存の
`ProjectionEvaluationRound::terminal_failure`とmachine attempt-terminal semanticsを変更しない。ただし
rev.1の「callerが先にcheckする」というconventionは廃止し、machine latchとstructural stateを§3.1の
`ProofAttemptKernel`へ同居させ、active capabilityなしにmutation/query/cache portへ到達できない構造にする。

```rust
// mutation/preparation port用。restricted-visibleだがfield/constructor private。Clone/Copy不可。
pub(in crate::constraints::structural_kernel) struct ActiveProofAttempt<'a> {
    // Noneはreuse-disabled mode。None同士の比較でforeign objectを認証しない。
    attempt_nonce: Option<ProofAttemptNonce>,
    terminal: &'a RefCell<Option<ProofFailure>>,
    _private: ActiveCapabilitySeal,
}

impl ActiveProofAttempt<'_> {
    pub(in crate::constraints::structural_kernel) fn ensure_active(
        &self,
    ) -> Result<(), ProofAccessError> {
        let terminal = self
            .terminal
            .try_borrow()
            .map_err(|_| ProofAccessError::TerminalLatchBusy)?;
        match terminal.as_ref() {
            None => Ok(()),
            Some(failure) => Err(ProofAccessError::Terminal(failure.clone())),
        }
    }
}

impl ProofAttemptKernel {
    fn try_with_structural_preparation_scope<R>(
        &mut self,
        f: impl for<'scope> FnOnce(
            &mut StructuralPreparationScope<'scope>,
        ) -> Result<R, ProofFailure>,
    ) -> Result<R, ProofFailure> {
        let active = ActiveProofAttempt::try_new(
            self.attempt_nonce,
            &self.terminal_failure,
        ).map_err(ProofFailure::from)?;
        let mut scope = StructuralPreparationScope::new(active, &mut self.structural);
        f(&mut scope)
        // scope Drop cancels every unconsumed arena slot.
    }

    pub(in crate::constraints) fn with_projection_query<R>(
        &mut self,
        type_shapes: &TypeArena,
        round: &mut ProjectionEvaluationRoundState,
        query: impl for<'query> FnOnce(
            ScopedProjectionQuery<'query>,
        ) -> Result<QueryCompletion<R>, ProofFailure>,
    ) -> Result<R, ProofFailure> {
        // 1. current kernel authorityだけを先に読む。foreign roundのfieldはまだ読まない。
        self.ensure_kernel_active()?;
        // 2. bindingだけを読み、attemptを認証する。
        let access = self.authenticate_projection_round_binding(round)?;
        // attempt認証後に起きるround check、scope construction、queryの全failureを
        // common failure branchへ渡す。ここから先で`?`をwrapper外へescapeさせない。
        let result: Result<QueryCompletion<R>, ProofFailure> = match access {
            AuthenticatedRoundAccess::Reusable => (|| {
                // 3. nonce match後にだけround-local terminalを読む。
                self.ensure_projection_round_active(round)?;
                // 4. その後snapshot/memo/cacheへ到達する。
                let snapshot = self.structural.snapshot.completed();
                round.bind_or_clear_for_authenticated_snapshot(snapshot);
                let scope = ScopedProjectionQuery::new(
                    &self.structural.data,
                    &mut self.structural.validity_cache,
                    snapshot,
                    ImmutableTypeShapeView::new(type_shapes),
                    round,
                )?;
                query(scope)
            })(),
            AuthenticatedRoundAccess::ReuseDisabled => (|| {
                // Persistent roundのterminal/memo/overrideは読まない。scope-local stateだけを使う。
                let snapshot = self.structural.snapshot.completed();
                let mut ephemeral = ProjectionEvaluationRoundState::new_ephemeral_uncached();
                let scope = ScopedProjectionQuery::new_uncached(
                    &self.structural.data,
                    snapshot,
                    ImmutableTypeShapeView::new(type_shapes),
                    &mut ephemeral,
                )?;
                query(scope)
            })(),
        }; // view/cursor/raw referenceはここで全てdeadになる。

        match result {
            Ok(completion) => {
                self.ensure_kernel_active()?;
                if access == AuthenticatedRoundAccess::Reusable {
                    // Publish前も同じ順序で再認証し、match後にround latchを読む。
                    self.authenticate_projection_round_binding(round)?;
                    self.ensure_projection_round_active(round)?;
                    self.structural.try_publish_success_candidates_or_disable_reuse(
                        completion.candidates,
                    );
                }
                Ok(completion.value)
            }
            Err(failure) => {
                if access == AuthenticatedRoundAccess::Reusable {
                    // accessはentryで認証済み。reuse-disabled/foreign roundへfailureをimportしない。
                    round.mark_terminal_once(failure.clone());
                }
                if failure.requires_attempt_terminal() {
                    self.mark_terminal_once(failure.clone());
                }
                Err(failure)
            }
        }
    }
}

impl ConstraintMachine {
    // round fields/constructors are private。normal modeでは生成時点のattempt/snapshotへbindする。
    pub(in crate::constraints) fn new_projection_evaluation_round(
        &self,
    ) -> ProjectionEvaluationRoundState {
        self.proof_attempt.new_projection_evaluation_round()
    }

    pub(in crate::constraints) fn new_publication_evaluation_round(
        &self,
    ) -> CpkPublicationEvaluationRoundState {
        self.proof_attempt.new_publication_evaluation_round()
    }

    // production caller breadthはcrate::constraints。TypeArenaをkernelへ移さずfield split-borrowする。
    pub(in crate::constraints) fn with_projection_query<R>(
        &mut self,
        round: &mut ProjectionEvaluationRoundState,
        query: impl for<'query> FnOnce(
            ScopedProjectionQuery<'query>,
        ) -> Result<QueryCompletion<R>, ProofFailure>,
    ) -> Result<R, ProofFailure> {
        let types = &self.types;
        let kernel = &mut self.proof_attempt;
        kernel.with_projection_query(types, round, query)
    }

    // Publication evaluatorのproduction/migration entrypointも必ずmachine delegateに統一する。
    // callerがbare kernel wrapperを直接選ぶ別経路は公開しない。
    pub(in crate::constraints) fn with_publication_projection_query<R>(
        &mut self,
        round: &mut CpkPublicationEvaluationRoundState,
        query: impl for<'query> FnOnce(
            ScopedPublicationProjectionQuery<'query>,
        ) -> Result<QueryCompletion<R>, ProofFailure>,
    ) -> Result<R, ProofFailure> {
        let types = &self.types;
        let kernel = &mut self.proof_attempt;
        kernel.with_publication_projection_query(types, round, query)
    }
}

impl StructuralPreparationScope<'_> {
    fn commit(
        &mut self,
        prepared: PreparedStructuralMutationHandle<'_>,
    ) -> Result<CommittedStructuralMutation, StructuralCommitError> {
        self.active.ensure_active()?;
        let slot = prepared.slot;
        let result = self.structural.commit(&self.active, prepared);
        self.remove_consumed_slot_from_drop_set(slot); // swap_remove; allocation-free
        result
    }
}
```

`ensure_kernel_active` / attempt binding authenticationの失敗は、foreign/terminal authorityを認証できなかった
access denialなのでquery failure finalizerへ入れず、structural read/cache lookup前に返す。一方、`access`確定後の
round-terminal check、ephemeral round生成、`ScopedProjectionQuery::{new,new_uncached}`、query closureの
`ProofFailure`はすべて上のtyped `result`へ格納し、共通`Err` branchを通す。constructor内部で`?`を使っても
即時closureからだけreturnし、wrapperを抜けない。従ってauthenticated scope constructionのallocation failureも、
reusable projection roundならround first-failureを記録し、`requires_attempt_terminal()`ならmachine latchを一回だけ
markする。reuse-disabled時はunauthenticated persistent roundへfailureをimportせず、machine latch規則だけを適用する。

`ProofAttemptKernel::{new_projection_evaluation_round, new_publication_evaluation_round}`はprivate round fieldを
初期化する唯一のfactoryである。normal modeではcurrent nonce/snapshotを`ProjectionRoundBinding`へ入れ、
reuse-disabled modeでは`binding = None, reuse_disabled = true`とする。projection/publicationの両wrapperは
次の順序を共通contractとして固定する。

1. **current kernel terminal latchだけ**を確認する。round terminal/memo/overrideは読まない。
2. current nonceとround binding nonceを比較する。両方`Some`で不一致、またはnormal/reuse-disabled
   modeが不整合なら
   `ProofAccessError::ForeignAttemptRoundState { expected, actual }`を返す。round clear、cache lookup、canonical readは
   一件も行わない。
3. nonce match後にだけround-local terminal latchを確認する。foreign roundのsticky failureをcurrent errorとして
   return/importしない。
4. same nonce / same snapshotならowned checked/memoをreuseする。same nonce / changed snapshotならterminal failureを
   除くsuccess-only stateをclearし、current snapshotへrebindする。
5. current kernelがreuse-disabledなら、`None == None`をidentity matchとせず、persistent roundのterminal/
   memo/overrideを読まずscope-local fresh stateでcanonical validationを実行し、cache hit/publishを行わない。

このfactory restrictionはtype visibilityだけに依存しない。`ProjectionEvaluationRoundState` /
`CpkPublicationEvaluationRoundState`へ`Default`、public/restricted `new`、deserializer、clone-from-fields test helperを
追加しないcompile-fail/API gateをSS6に置く。

`TypeArena`は§3.1のappend-only検証条件を満たす限り`ConstraintMachine::types`に残す。
`ConstraintMachine::with_projection_query(&mut self, ...)`が`&self.types`と`&mut self.proof_attempt`をfield
split-borrowし、exact `&TypeArena` parameterをkernel wrapperへ渡す。kernelはscope内でだけ
`ImmutableTypeShapeView::new(type_shapes)`を作る。`ProofAttemptKernel`、round state、cacheへ`&TypeArena` /
`ImmutableTypeShapeView`を保存しない。append-only premiseがSS0で反証された場合はこのsignatureを採らず、type-shape
stateもsealed ownerへ吸収する。

`ActiveProofAttempt::try_new`は`access.rs` privateであり、`ProofAttemptKernel`のnarrow methodだけが呼べる。
`ProofStructuralState::{prepare, commit}`は`&ActiveProofAttempt`をrequired parameterに持ち、各port入口で
`ensure_active()`を再実行する。mutation tokenはattempt nonceを持ち、別attemptのprepared handleへ使えない。
terminal latch borrow conflictを「active」と見なして先へ進めず、typed access denialとしてdata/cacheを触らず返す。

`ProjectionEvaluationRound::terminal_failure`はround-local authorityとして残す。production query/cacheは
`ProofAttemptKernel::with_projection_query`だけから入り、次を一つのmandatory wrapperで行う。

1. machine latch、attempt binding、nonce match後のround latchの順で、cache lookup前にcheckする。
   unauthenticated roundのterminal failureを読み、returnし、current attemptへimportしない。
2. `&mut ProofAttemptKernel`とlifetime-free `&mut ProjectionEvaluationRoundState`をHRTB closure全体でexclusive
   reborrowする。
3. cache miss validation/evaluator failure時、owned candidateを破棄する。scopeをdropした後にround first failureを
   stickyにし、必要なら`ProofAttemptKernel::mark_terminal_once`を通す。
4. success時はscope終了後にmachine/round双方を再checkしてからowned candidateをpublishする。

`ConstraintMachine::proof_terminal_failure()`と`mark_proof_terminal_failure()`という外形APIを移行期間に残す
場合も、実体は`ProofAttemptKernel`へdelegateする。外部moduleへlatchの`RefCell`、active-token constructor、
`ProofStructuralState`を公開しない。従って「callerがcheckを忘れたままgateway/cacheへ直接入る」経路は無い。

prepared handleが存在する間にattemptがterminalになった場合、commitはactive capabilityを発行せず、§3.5.6の
kernel cleanupだけがticketをreleaseする。terminal latch後に新prepare、commit、query、cache lookup、cache
publicationを開始しない。diagnostic formattingのためのread-only snapshot dumpを残す場合、それはcache portと
`ProjectionPreflight`を持たない別APIとし、mutation/query authorityにはならない。

caller-side pure no-intent precheckも、production semantic getterを使う限り
`ProofAttemptKernel::with_structural_inspection`の同じHRTB exclusive-scope patternを通す。precheck closureはowned
intent/no-op decisionだけを返し、raw reference/view/cursorを返さない。precheck後のprepare/commitは改めてactive
checkを要求する。diagnostic dumpをmutation decisionへ使わない。

publication pathは同じprivate scope constructorを使う別のnarrow wrapperを持つ。

```rust
pub(in crate::constraints) fn with_publication_projection_query<R>(
    &mut self,
    type_shapes: &TypeArena,
    round: &mut CpkPublicationEvaluationRoundState,
    query: impl for<'query> FnOnce(
        ScopedPublicationProjectionQuery<'query>,
    ) -> Result<QueryCompletion<R>, ProofFailure>,
) -> Result<R, ProofFailure> {
    // Projection wrapperと同じく、foreign roundのsticky stateよりcurrent kernelを先に確認する。
    self.ensure_kernel_active()?;
    // binding以外のmemo/override/cycle fieldを読む前にattemptを認証する。
    let access = self.authenticate_publication_round_binding(round)?;
    let snapshot = self.structural.snapshot.completed();

    // attempt認証後のscope construction/query failureをcommon failure branchへ畳み込む。
    // branch内の`?`はこの即時closureからだけreturnし、wrapperを抜けない。
    let result: Result<QueryCompletion<R>, ProofFailure> = match access {
        AuthenticatedRoundAccess::Reusable => (|| {
            // Publication roundにはround-local terminal latchを持たせない。認証後のstep 3はno-op。
            round.bind_or_clear_for_authenticated_snapshot(snapshot);
            let scope = ScopedPublicationProjectionQuery::new(
                &self.structural.data,
                &mut self.structural.validity_cache,
                snapshot,
                ImmutableTypeShapeView::new(type_shapes),
                round,
            )?;
            query(scope)
        })(),
        AuthenticatedRoundAccess::ReuseDisabled => (|| {
            // caller-owned roundのterminal/memo/record override/root overrideには触れない。
            let mut ephemeral = CpkPublicationEvaluationRoundState::new_ephemeral_uncached();
            let scope = ScopedPublicationProjectionQuery::new_uncached(
                &self.structural.data,
                snapshot,
                ImmutableTypeShapeView::new(type_shapes),
                &mut ephemeral,
            )?;
            query(scope)
        })(),
    };

    match result {
        Ok(completion) => {
            self.ensure_kernel_active()?;
            if access == AuthenticatedRoundAccess::Reusable {
                self.authenticate_publication_round_binding(round)?;
                self.structural.try_publish_success_candidates_or_disable_reuse(
                    completion.candidates,
                );
            }
            Ok(completion.value)
        }
        Err(failure) => {
            if failure.requires_attempt_terminal() {
                self.mark_terminal_once(failure.clone());
            }
            Err(failure)
        }
    }
}
```

publication側も、attempt認証前のaccess denialだけをearly returnできる。認証後のephemeral state生成、
`ScopedPublicationProjectionQuery::{new,new_uncached}`、query closureの`ProofFailure`はtyped `result`へ入り、必ず
共通`Err` branchで`requires_attempt_terminal()`を判定して`mark_terminal_once`へ到達する。constructorの`?`が
このbranchを迂回する実装を禁止する。production callerとmigration fixtureの入口は、上で定義した
`ConstraintMachine::with_publication_projection_query`だけである。bare
`ProofAttemptKernel::with_publication_projection_query`はmachine field-splitting delegateの内部実装であり、
SS6 migration censusはそのproduction callerが当該delegate一件だけであることを固定する。publication evaluator、
test、fixtureからbare kernel methodを直接呼ぶ経路を認めない。

`CpkPublicationEvaluationRoundState`は`&ConstraintMachine`も`CpkProjectionEvaluator<'a>`も保存しない。
record/root overrides、memo map、cycle-sharing-disabled bit、attempt+snapshot bindingだけをownedで保持する。各top-level
`eval_record`はwrapperを一回呼び、scope内でfresh `CpkProjectionEvaluatorFacade`を作り、scope終了時にowned memo/
cycle countersをround stateへ戻す。cycle cut後にsharingをdisableしfresh memoを使う現行semanticsを維持する。

`authenticate_publication_round_binding` はprojection用helperと同じ`ProjectionRoundBinding`比較を行い、
facade構築、record/root override read、evaluator memo/cycle read、cache lookupのすべてより前に完了する。
publication wrapperだけをbinding checkから外すtest/convenience pathを作らない。
publication roundはround-local terminal latchを所有せず、failureはcurrent kernelのexisting terminal ruleへだけ渡す。
従ってこのpathでは「round attempt認証後にround-local latchを読む」stepはno-opであり、foreign
publication roundのerror/control stateをimportする別経路は無い。

`ProjectionEvaluationRoundState`も同様に、scopeごとにfresh `ProjectionPreflightFacade`と
`CpkProjectionEvaluatorFacade`を作る。facadeは次の形であり、roundへ保存できない。

```rust
struct ProjectionPreflightFacade<'query> {
    view: &'query ScopedQueryView<'query>,
    state: &'query mut ProjectionPreflightRoundState,
    target_record: BoundRecordId,
}

struct CpkProjectionEvaluatorFacade<'query> {
    view: &'query ScopedQueryView<'query>,
    state: &'query mut CpkProjectionEvaluationRoundState,
}
```

top-level target Aのscope終了後も`checked_records` / `checked_constraints` / acyclic `Done` memoはowned round stateに
残り、target Bのfresh facadeがsame attempt / same snapshotなら再利用する。recursive `validate_record` /
`validate_constraint`、claim/
live late-bound read、record/root recursionは一targetのfacadeから直接再帰し、nested `with_projection_query`を呼ばない。
visiting set/stateは各top-level return時にemptyをassertし、borrowed store/view/cursorをroundへ書き戻さない。

#### 3.7.1 HRTB exclusive query scope

rev.3の「viewがcapabilityを保持し、every getter/cursor stepで`RefCell::try_borrow`または
`Cell<Generation>`を再checkする」案は採らない。check後にgetterがraw `&T`を返すと、そのreferenceはcheck用borrowが
dropした後も生きられる。standalone prototypeはRefCell版とCell版の双方で、safe Rustが次をcompile/runできることを
確認した。

```rust
let escaped: &Fact = view.fact(id)?;
kernel_or_view_marks_terminal();
use_fact(escaped); // check済みreferenceは依然usable
```

per-getter recheckは**次のgetter call**を拒否できるだけで、既にescapeしたreferenceをrevokeできない。そこでread
authorityを次のHRTB scopeへ変える。

```rust
pub(in crate::constraints) struct ScopedQueryView<'query> {
    data: &'query StructuralData,
    snapshot: ProofStructuralSnapshotId,
    type_shapes: ImmutableTypeShapeView<'query>,
    // terminal-latch setter、kernel/cache publication portは持たない。
}

impl ScopedQueryView<'_> {
    pub(in crate::constraints) fn bound(
        &self,
        record: BoundRecordId,
    ) -> Option<&BoundRecord> {
        self.data.read_bound(record)
    }

    pub(in crate::constraints) fn formula_cursor(
        &self,
        record: BoundRecordId,
    ) -> FormulaCursor<'_> {
        self.data.formula_cursor(record)
    }
}
```

`for<'query>`によりclosure return type `R`は特定`'query`を含められない。prototypeでraw referenceをreturnするprobeは
E0515/lifetime errorとなった。また`with_projection_query(&mut kernel, ...)`中に同じkernelのterminal setterを呼ぶ
probeはexclusive borrow conflict E0500/E0501となった。scope内でreferenceをdereference/normalizeしてowned valueを
返すpathはcompile/runした。従って「terminal transitionを呼ばない」というconventionではなく、raw reference escapeと
same-kernel terminal transitionをborrow checkerが拒否する。

query中のvalidation/evaluator failureはscope内でlatchを直接setせず、owned `ProofFailure`としてwrapperへ返す。
wrapperはscope/drop後に既存round/machine terminal semanticsを適用する。cursorも`'query`へboundされ、cursor/referenceを
round object、cache candidate、receiptへ保存できない。cache candidateはID/snapshot/outcome等のowned dataだけである。

non-Copy factをquery API境界の外へ渡す必要がある場合はscope内でowned/canonical descriptorへ変換する。巨大値のcloneを
常態化させず、validation自体はscope内のborrowを使う。HRTBへ移せない個別APIだけはowned descriptor getterを使い、
raw `&T`を返すper-getter generation-check adapterをproductionへ置かない。

#### 3.7.2 Capability check cost

prototypeのrelease microbenchmarkは75,000,000 checks/sample、5 samplesで、
`RefCell::try_borrow()`が約`0.88 ns/check`、`Cell<u64>` generation compareが約`0.42 ns/check`、Cellが
約`2.02〜2.13x`高速だった。synthetic lower-boundでありreal wall-timeを直接予測しないが、§2のRMW
`50,309,515` entries、cold std `144,192,658` entriesにgetter/cursor-step数を掛けるvolumeでは無視できない。

rev.5の比較は「Cellをper-getterで安くする」ではなく、**旧: N getter calls × 0.42〜0.88 ns以上** 対
**新: query-scope entryで一回check + N gettersの追加check zero**である。scope entryでは既存machine/round latchを
一度checkし、scope中のexclusivityをcompilerが維持する。SS6はscope count、getter count、entry-check wall costを
別counterで測り、HRTB closure/owned candidate conversionのcostを含むreal RMW/std A/Bで判断する。

#### 3.7.3 Borrowed evaluation resultのowned migration

current `SchemeProjectableLower<'a>`は`bound: &'a WeightedLowerBound`を返す。このreferenceはsealed storageから
query scope外へescapeできないため、rev.5ではresult自体をownedへ変える。

```rust
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SchemeProjectableLower {
    pub(crate) record: BoundRecordId,
    pub(crate) bound: WeightedLowerBound,
    pub(crate) reason: SchemeProjectableLowerReason,
    pub(crate) projection_evidence: Option<ProjectionEvidence>,
}
```

`WeightedLowerBound`は既に`Clone`であり、selected lowerをresultへpushする時だけscope内でcloneする。不採用lowerや
recursive validation nodeはcloneしない。`scheme_projectable_lowers_in_round`は
`Vec<SchemeProjectableLower>`を返し、outer iteratorもowned itemをyieldする。opaque bound IDをscope外へ返して別scopeで
re-resolveする方式は、terminal/snapshot checkを二重化しconsumerを複雑にするため採らない。

```rust
pub(crate) fn scheme_projectable_lowers_in_round(
    &mut self,
    var: TypeVar,
    round: &mut ProjectionEvaluationRoundState,
) -> Result<Vec<SchemeProjectableLower>, ProofFailure>;
```

cache portとkernel scopeをexclusive borrowするため、このproduction entrypointはcurrent `&self`から`&mut self`へ移す。
failureをempty iteratorへ畳まずexisting terminal wrapperへ伝える。全callerをSS6で移行し、interior-mutabilityのraw
read-view escapeを使って旧`&self` signatureだけを温存しない。

SS6はselected lower count、cloned `ConstraintWeights`容量、wall/RSSを測る。clone costがgross regressionなら
`WeightedLowerBound`のimmutable owned payloadを`Arc`等へ変える案を別設計として検討し、raw reference escapeへ戻さない。
同じくscope外へborrowed structural fieldを返すresult typeをSS0で列挙し、owned descriptor/valueへ変換する。

structural validation success後にprojectability evaluatorがfailureになった場合、そのsuccess candidateは
publish前なら破棄する。既に同snapshotで以前publish済みのsuccess markerはfalseではないが、active capabilityが
発行されないためterminal attemptで再利用されない。terminal attemptはdiscardされcacheはattemptを跨がない。
latchをclearして同じattempt cacheを再利用するproduction APIを作らない。

従って許されるfailure retentionはterminal control stateだけであり、次は禁止する。

- `StructuralValidityCache`へ`Err`、owner、error precedenceを保存する。
- snapshot-keyed failure hitでcanonical re-attemptをskipする。
- cache hitで既存terminal latchをclear/overrideする。
- cache allocation failureをattempt-terminal semantic failureへ変える。
- active capabilityなしにgateway/cache/queryを直接呼べるtest-only以外のAPI。

### 3.8 Cache read/write contract

```text
StructuralValidityCache {
    records: BoundRecordId -> ValidatedAt,
    constraints: ConstraintRecordId -> ValidatedAt,
}

ValidatedAt {
    snapshot: ProofStructuralSnapshotId,
    outcome: FullyResolvedStructuralSuccess,
}
```

cacheはattempt-local、lazy、non-serializedである。compiled prefix、portable output、global cache、evaluation
memoへ入れない。

read順序:

1. `ConstraintMachine::with_projection_query(&mut self, &mut round_state, ...)`が`types`と`proof_attempt`を
   split-borrowし、kernel wrapperだけがmachine/round terminal latchを確認する。
2. wrapperがkernelのattempt nonce、sealed stateのcompleted snapshot、reuse-disabled bitを読む。foreign attempt
   bindingはtyped rejectionし、same attemptではsame snapshotをreuseまたはchanged snapshotへclear/rebindしてから、
   `&TypeArena`からscope-local immutable type-shape viewを作る。
3. HRTB `ScopedProjectionQuery<'query>`内でfresh preflight/evaluator facadeをmintする。owned checked/memo stateだけを
   roundからreborrowし、store/viewをroundへ保存しない。
4. scope内のprivate cache portがsame identity / same snapshotのfully-resolved successを見れば`Ok(())`。
5. missなら同じscope-bound `ScopedQueryView`でrefined canonical validationを実行する。
6. visiting stacksが完全unwindしたtop-level successはowned candidateへ変換され、scope終了後にwrapperが両latchを
   再確認してpublishする。
7. failure、cycle-local `Ok`、partial unwind、allocation failureではpublishしない。scope lifetimeそのものを
   capability失効/revocationの代用にする。

cache storageは`ProofStructuralState`内のprivate auxiliary fieldに置く。exclusive `&mut ProofAttemptKernel` query
scopeが`StructuralData`のimmutable borrowとcacheのmutable borrowをfield分割して所有できるため、hot recursive
lookup用`RefCell`は不要である。cache portをviewのpublic methodにせず、`ScopedProjectionQuery`内部だけが触る。
cache reservation failureはuncached canonical validationへ戻し、panicするborrow/growth pathを置かない。

gatewayが`Changed`をfinalizeするとcompleted snapshotを進め、cache mapsをclearする。clearはcapacityを保持して
よい。saturation時はreuseをdisableし、cacheをclearして以後hit/publishしない。

### 3.9 CPK-SV-C late bindingとの整合

独立査読が確認したとおり、claim admission/moveとlive coverage activation/deactivationはcurrent authority変更ごとに
structural snapshotを進める。本設計ではそれらもsealed commandへ移行し、Changed finalizerを通る。

従ってcache hitは、`ValidateClaimBinding { representative, expected_root }`と
`ValidateCoverageRootState { expected_root }`が読んだclaim/live stateが変わっていないcompleted snapshotにだけ
成立する。claim/live current leafをformula adjacencyへmaterializeしないCPK-SV-C decisionを変更しない。

## 4. Storage family migration mapping

### 4.1 Mapping table

| current owner / storage | sealed destination | production read | mutation command family | disposition rule |
|---|---|---|---|---|
| `ProofOccurrenceStore`のoccurrence/formula/certificate/adjacency/replay/qualified-parent/projection-index relation | `StructuralData::proof` / `ProofRelations` | HRTB `ScopedQueryView<'query>`内のproof getter/cursor | proof occurrence、formula/support、replay、qualified parent、projection index | default Changed。exact duplicateを将来allowlist可能 |
| upper claim、claim indices、reduction claim、live coverage/root→state | `ProofRelations::claims_live` | late-bound claim/live getter | claim admit/move、live activate/deactivate | default Changed。intent発行済みsame-record moveもproofなしならChanged |
| `TypeBounds::{vars, canonical, records}` | `StructuralData::bounds` / `BoundRelations` | bound/owner/endpoint/state/derivation getter | bound admit/promote/tombstone/derivation extend | default Changed。exact duplicateだけ個別proof候補 |
| `BoundRecord::disposition`と`bound_dispositions` | non-structural diagnostic sidecarへ分離 | diagnosticsのみ。preflight viewへ公開しない | structural command外 | `Unchanged`ではなくsnapshot boundary外 |
| `canonical_constraints`、`constraint_records`、constraint→lower relation、replay-drop structural identity | `StructuralData::constraints` / `ConstraintRelations` | constraint semantic/proof getter | canonical admit、proof extension、replay relation/drop | default Changed |
| row residual identity、row derivation/index、unweighted row reduction state/owner/processed-lower relation、cache-relevant lower-filter relation | `StructuralData::rows` / `RowRelations` | row reduction/derivation getter | row admit/update/match/reduction | default Changed |
| origins、source-boundary identity、generalized scheme/witness、scheme-instantiation identity/index | `StructuralData::identities` / `IdentityRelations` | carrier/witness/origin getter | identity admission/extension | default Changed |
| source location recorded、timing、telemetry、queue、events、outbox、diagnostic formatting metadata | `ConstraintMachine`のnon-structural sidecar | preflight viewへ公開しない | gateway外 | snapshot boundary外 |
| `ProofStructuralSnapshotState` | `ProofStructuralState::snapshot` | snapshot getterのみ | gateway finalizerだけ | changedでbump、proof付きunchangedで維持 |
| shared `HashMap`/`Vec`/bucketのcommit-time capacity | `ProofStructuralState::reservations` + `prepared` arena + container別write port | production semantic readへ公開しない | attempt-global ticket / one-shot reserved operation / scope cleanup | snapshotとは独立。global ID一意、child empty pin、global snapshotをbaseにしない |
| new successful-validity map | `ProofStructuralState::validity_cache` | bounded cache port | query success publicationのみ | structural stateを変えずsnapshotもbumpしない |
| `TypeArena`のexisting Pos/Neg shape | external immutable `ImmutableTypeShapeView`（SS0検証条件付き） | `is_var_pos`等のread-only query | existing payload mutationなし | append-only new IDはold validationをinvalidateしない |
| machine attempt-terminal latch | `ProofAttemptKernel::terminal_failure`へcontrol ownershipを移す | active capability発行時/port入口のsticky check | `mark_terminal_once` | structural cacheとは別authorityだがaccess capabilityを支配 |
| current `ProjectionEvaluationRound<'a>` / stored `ProjectionPreflight<'a>` | lifetime-free `ProjectionEvaluationRoundState` + scope-local facades | targetごとのHRTB scope | structural mutationなし | checked/memo/terminal/attempt+snapshot bindingだけround-persistent。store/view borrowは保存しない |
| current `CpkPublicationEvaluationRound<'a>` / stored `CpkProjectionEvaluator<'a>` | lifetime-free `CpkPublicationEvaluationRoundState` + scope-local evaluator facade | publication targetごとのHRTB scope | structural mutationなし | overrides/memo/cycle bit/attempt+snapshot bindingだけround-persistent。`&ConstraintMachine`を保存しない |
| `ProjectionEvaluationRound::terminal_failure` | owned round stateに保持 | `with_projection_query`がscope entry/publish前にcheck | existing round failure control | scope内failureはowned errorで返し、scope drop後にsticky化 |
| `SchemeProjectableLower<'a>::bound: &'a WeightedLowerBound` | owned `SchemeProjectableLower::bound: WeightedLowerBound` | selected resultをscope内clone | structural mutationなし | raw bound borrowをscope外へ返さない。clone costをSS6測定 |

### 4.2 Absorbとview化の境界

`ProofOccurrenceStore`と`TypeBounds`を単にprivate fieldとして`ConstraintMachine`へ残すだけでは足りない。
外部writer methodが`&mut ProofOccurrenceStore` / `&mut TypeBounds`を取れるならround 6のescapeを残す。
両者のmutation methodはkernel child module内の`StructuralWriteTxn` operationへ移す。

`ConstraintMachine`から次のraw fieldsを除き、`proof_attempt: ProofAttemptKernel`へ置換する。

- `proof_store`。
- `bounds`。
- `canonical_constraints` / `constraint_records`とcache-relevant indices。
- row derivation/reduction/residual/lower-filterのcache-relevant部分。
- origin/source-boundary/witness/scheme-instantiationのidentity部分。
- machine `proof_terminal_failure`の直接field。外形getter/markerはkernel delegationにする。

solver orchestration、queue、type arena、timing、events、round-local terminal latch、diagnostic sidecarsは外に残す。
外部orchestrationはtyped intentを作り、receiptからqueue/event/diagnostic publicationを続ける。prepared intentから
secondary outputをpublishせず、CPK-SV-C-R0のcommitted-receipt authorityを維持する。

round stateはkernel storageへ吸収せず、caller-owned lifetime-free valueとして外に残す。ただし中身はID/value/map/
terminal stateだけであり、`ProofStructuralState`、`TypeArena`、`ConstraintMachine`へのreferenceを持たない。各targetは
同じowned round stateを`with_projection_query`へ順番に渡し、scope-local facadeだけがそのtarget中にborrowする。

### 4.3 Trusted kernelの正直な範囲

visibility/capability boundaryは小さくできる。

- `ProofAttemptKernel`のactive-check付きnarrow facade。
- `ProofStructuralState::{prepare, commit}`とprivate cache/query port。
- closed command/receipt enum。
- private `StructuralWriteTxn` constructor。
- private reservation ledger/ticket/reserved-operation constructor。
- private no-op prover allowlist。
- snapshot/cache finalizer。
- HRTB exclusive query wrapperとscope-bound read view。

しかしfamily handler実装の総LOCは小さくない。proof、bounds、constraint、row、identityのcommit logicは
数千行規模のsemantic trusted codeであり続ける。本書が「small trusted kernel」と呼べるのはescape-capability
surfaceと`Unchanged` allowlistであり、全handler LOCではない。

family moduleは§3.1.1どおりgatewayとsiblingにし、raw storageだけをgateway childへ置く。単に
`constraints/structural_kernel/`配下へ集めただけでprivacyが成立したとは数えない。compile-fail/UI testで次を
固定する。

- raw field access不可。
- `StructuralWriteTxn`構築不可。
- reservation ticket/one-shot reserved operationの構築・偽造不可。
- `ExplicitNoOpProof`構築不可。
- custom/open mutation command注入不可。
- `ScopedQueryView`から`&mut`取得不可、raw referenceのscope外escape不可。
- active-attempt capabilityなしのcommit/query/cache port呼出し不可。

compile-fail testはsemantic comparator correctnessを証明しない。allowlist fixtureと独立査読が別途必要である。

## 5. CPK-SV-A/B/C/D0との関係

### 5.1 CPK-SV-A: structural certificate

admission-time structural certificate、bucket-local `formula_revision`、atomic certificate publication、
missing/dirty fallbackを変更しない。certificateはformula bucket内部のfrozen structureだけを証明する。

移行後、formula bucket/certificate/revisionは`StructuralData::proof`に吸収し、formula admission commandが
同じsealed transactionで更新する。certificate current/dirty判断をsnapshot `Unchanged` proofへ転用しない。
formula structureが変わればChangedであり、certificateがvalidでもglobal snapshotを進める。

### 5.2 CPK-SV-B: order authority

valid certificateによるorder-only pass省略と、missing/dirty/corruption時のlegacy order-first fallbackを
維持する。`NonCanonicalProjectionOrder`のprecedenceをcache hitのために変更しない。

same-snapshot `Valid` entryは、そのsnapshotでcertificate/order contractを含むrefined canonical structural
validationが成功した結果だけである。test corruption commandもsealed Changed commandとしてsnapshotを進め、
pre-corruption entryをhitさせない。

### 5.3 CPK-SV-C: stable obligationとlate binding

次をすべて維持する。

- `ValidateClaimBinding { representative, expected_root }`。
- `ValidateCoverageRootState { expected_root }`。
- query-time current claim/live authority read。
- record-local support-ledger closure。
- refined canonical `RepresentativeRootMismatch`。
- indexed live state/flat occurrence divergenceのtyped failure。
- claim/live writerからformula adjacencyへのfanout禁止。
- committed receipt authorityとsilent-loss barrier。
- `projection_lower_records_by_root` / `projection_lower_record_memberships`の保存。

claim/live authorityはsealed `ProofRelations::claims_live`へ移る。move/activation/deactivationはChanged command
としてsingle finalizerを通る。従って旧snapshotのstructural successは必ずmissする。dynamic leafをformula
adjacencyへ再materializeしない。

writer conflictには§3.5のtarget/relationship-local baseだけを使う。global snapshot advanceを理由にactual
claim prepare→formula prepare→claim commit→formula commit、formula-first compatibility、
move prepare→formula commit→move commitをrejectしない。
shared-container ticketもsemantic conflictではなくcapacity ownershipだけを表す。これによりCPK-SV-C redesignの
approved orderingを弱めず、rev.1のcapacity gapを閉じる。

### 5.4 CPK-SV-D0: type reuse、writer mechanism supersession

commit `251e64a8`、`a88b0257`、`9ce43039`でlandingしたD0から再利用するもの:

- `ProofStructuralSnapshotId`の型。
- attempt-local completed generationという意味。
- saturating/non-wrapping semantics。
- saturation後`reuse_disabled`とする安全規則。
- mutation class、corruption、boundary fixtureから得たcurrent migration census。

再利用するsnapshot typeはcache identityに限る。D0 snapshot値をprepared commandのbase、writer conflict、
reservation ticket epochとして再利用しない。

そのまま再利用しないもの:

- scattered writer末尾の`publish_structural_mutation_at`。
- `ProofStructuralMutationSite`をcorrectness authorityにするwriter tagging。
- `PRODUCTION_WRITERS` inventory/counterをexhaustiveness proofにするgate。
- raw ownerを残したままsiteごとにbumpする構造。

SS2〜SS5で各familyをgatewayへ移す間、D0 notificationをshadow comparisonとして一時保持してよい。しかし
production cache readは無効のままとし、migration完了後はgateway finalizerが唯一のsnapshot writerになる。
D0 site enum/counterは最終closeoutでtest-only diagnosisとして限定するか、不要なら除去する。

D0の19+ siteはSS0 migration checklistのinputにはなるが、future closureのproofではない。final closureは、
raw storageがopaque state内部にあり外部writerがcompileできないこと、closed command dispatch、single
finalizerで成立させる。

## 6. Blast radius / 影響範囲

### 6.1 Production ownership migration

これは小さなcache追加ではない。少なくとも次を変更する。

1. `crates/infer/src/constraints/mod.rs`
   - `ConstraintMachine`からbounds/constraint/row/identity/proof fieldsとmachine terminal latchを
     `ProofAttemptKernel`へ移す。
   - read helperを`with_projection_query` / `with_structural_inspection` HRTB scopeへ切り替える。
   - claim move/live coverage等のtransaction callerをtyped intent/receiptへ変える。
   - `CpkPublicationEvaluationRound<'a>`をowned state + scope-local evaluator facadeへ分け、全callerをHRTB scope/
     `Result`伝播へ変える。
   - `SchemeProjectableLower<'a>`をowned resultへ変える。
2. `crates/infer/src/constraints/proof/mod.rs`
   - `ProofOccurrenceStore` ownershipと多数のprepare/commit methodをkernel familyへ移す。
   - `ProjectionPreflight` / `CpkProjectionEvaluator`をscope-bound `ScopedQueryView`へ切り替える。
   - borrowed `ProjectionEvaluationRound<'a>`をowned round state + scope-local facadeへ分ける。
   - evaluator state/record override/root override insertionをfallibleにする。
   - successful validity cacheとoracleを追加する。
3. `crates/infer/src/constraints/machine/bounds.rs`
   - bound/replay/formula/support/qualified-parent等のmulti-family writeをtyped command/receiptへ変える。
   - prepared intent由来のsecondary publicationを禁止する既存規則を維持する。
4. `crates/infer/src/constraints/machine/entry.rs`
   - constraint/origin/source-boundary/witness/scheme-instantiation admissionをgatewayへ移す。
5. `crates/infer/src/constraints/row_effect.rs`
   - row derivation/reduction/live transitionをgateway commandへ移す。
6. `crates/infer/src/constraints/machine/propagate.rs`等
   - direct mutation/readが見つかればtyped facadeへ置換する。
7. new `crates/infer/src/constraints/structural_kernel/` module family
   - attempt access owner、gateway-private data、commands、reservation ledger/write ports、
     sibling proof/bounds/constraints/rows/identity handlers、closed family publication plans、HRTB query view、owned
     round-state adapters、cacheを配置する。
8. `crates/infer/src/constraints/proof_inventory.rs`とtest modules
   - migration inventory、compile-fail/UI visibility、forced-uncached parity、allocation/cycle fixtureを更新する。

### 6.2 規模見積り

現時点のrealistic estimate:

- production/test files: **8〜15 files以上**。
- new kernel submodules: **8〜12 files**。
- semantic edit: **5,000〜10,000 lines程度**。
- ownership移動・module splitを含むvisible diff: **9,000〜18,000 lines超**になり得る。
- implementation slices: **少なくとも9段階**、`Unchanged` family追加ごとにさらに増える。

`proof/mod.rs`の物理分割を同時に行うとpure-move churnだけで上限を超え得る。reviewabilityを優先し、
semantic cutoverとpure file moveを可能な限り別commitにする。

### 6.3 性能・memory risk

- sealed facade自体のfunction-call overhead。
- typed command/prepared receiptのtemporary storage。
- shared-resource reservation ledger/ticketとaggregate `try_reserve` overhead。
- changed-by-defaultによるsnapshot over-invalidation。
- validity-cache lookupとcandidate publication。
- evaluator per-node fallible capacity check。
- publication evaluator/override `Result` propagationとfallible capacity check。
- mutation portのactive-attempt capability再checkと、query scope entry一回のmachine/round latch check。
- HRTB closure、owned cache candidate/descriptor conversionのcost。per-getter latch `try_borrow`は採らない。
- selected `WeightedLowerBound` cloneとowned round-state/facade handoff cost。
- multi-container prepared publication plan/retire listのtemporary capacity。
- validity cache hash map footprint。
- dual-write/shadow期間の一時RSS増加。

これらは全てRMW benefitを相殺し得る。§2のopportunityだけでperformance successを宣言しない。

### 6.4 Correctness risk

- large ownership moveで既存transaction atomicityを壊す。
- receipt/output orderingを変える。
- diagnostic-only stateを誤ってstructural stateへ混ぜる、または逆にmandatory inputを外へ残す。
- partial migration中にold/new ownerを二重authority化する。
- no-op comparatorがsecondary relationを比較し忘れる。
- generic read traitが残り、sealed view外のinputをpreflightが読む。

従ってcache authorityは全migration/query-scope/evaluator/latch gate完了後まで有効化しない。

## 7. 実装スライス計画

各sliceは独立commit、独立rollback、独立adversarial review単位とする。authority cutoverと大量ownership moveを
同じcommitへ混ぜない。

### CPK-SV-D-SS0: read-only ownership / command census

Authority: current production code。変更なし。

- current cache-relevant storage field、all raw writer、prepare/commit boundary、readerを列挙する。
- D0 19+ siteをmigration inputとして照合するが、それだけを正本にしない。
- production `ProjectionPreflight` / evaluatorの全readをactual call-site traceとcode readingで確定する。
- `TypeArena` existing payloadがappend-only immutableか確認する。
- diagnostic sidecarへ分離するfieldを確定する。
- multi-family transactionとreceipt orderingを確定する。
- command vocabularyと各prepared **semantic base read-set**を確定する。global snapshotをbaseに含めない。
- commit-time new-key/new-element insertionを行うshared containerをresource domainへ全件割り当て、command別
  reservation planとtyped write-port operationを確定する。
- per-record/per-root child containerのcreate/last-entry-remove/recreate siteを列挙し、pin/prune adapterを割り当てる。
- familyごとに§3.5.7のclosed `Prepared*PublicationPlan`とpanic-free typed primitiveを列挙する。key型、concrete
  `Eq`/`Hash`/hasher、drop、lookup/compare/assertのpre-write移動、retire-list容量を一rowずつ記録する。
- `commit_projection_formula_shadow_delta`、`record_prepared_live_coverage`、
  `commit_projection_index_admission`をmandatory multi-container rowsとし、raw post-write insert/assert/expect zeroの
  conversion planを確定する。closed primitiveへ落とせなければそのfamilyをstopし、co-owned aggregate再分割を
  別設計として査読する。general rollbackへ暗黙fallbackしない。
- current `ProjectionEvaluationRound<'a>` / `ProjectionPreflight<'a>`と
  `CpkPublicationEvaluationRound<'a>` / `CpkProjectionEvaluator<'a>`のborrowed fieldを、owned round stateか
  target-local facadeへ全件分類する。
- scope外へborrowed structural valueを返すresultを列挙し、少なくとも
  `SchemeProjectableLower<'a>::bound`をowned `WeightedLowerBound`へ移すplanを確定する。
- CPK-SV-Cが許可するformula/claim/move interleavingをsemantic-conflict matrixに明示する。

Gate:

- owner/writer/readerのunassigned row zero。
- preflight mandatory readのsealed destinationが全件決まる。
- true in-place type-shape mutationが無い、または吸収planがある。
- one commandへまとめるatomic boundaryと、sequential sibling commitを維持するboundaryが説明できる。
- shared container insertのunassigned resource domain zero。
- child-container removalのunassigned pin/prune path zero。
- authoritative first-write後にpanic/`?`/allocation/user callbackを持つcommand row zero。
- multi-container commandのunassigned publication op、unaudited key `Eq`/`Hash`、post-write assertion/drop row zero。
- round-persistent fieldにstore/view/machine/type-arena borrowを残すrow zero。
- query scope外へborrowed structural resultを返すunassigned row zero。
- each commandのsemantic baseとreservation domainを混同したrow zero。
- formula/claim/moveのapproved interleavingをglobal snapshot conflictにするrow zero。

Stop:

- cache-relevant writerかmandatory readのownerを一意に決められない。
- diagnostic/structural境界が設計文書だけでは決められない。

### CPK-SV-D-SS1: sealed shell + mandatory disposition shadow

Authority: current production storage/read。cache readなし。

- `structural_kernel` module、opaque state shell、public data-only closed `StructuralMutationIntent`、private closed
  `PreparedPayload`を持つprivate-field `PreparedStructuralCommand`、closed receipt enumを追加する。
- §3.1.1のsibling family/gateway-child storage layoutを追加する。
- machine attempt-terminal latchを`ProofAttemptKernel`へ移し、existing getter/markerをdelegateする。first-failure
  telemetry/sticky resultはbyte parityを維持する。
- private active capability、mandatory active-check付きport signatureを追加する。shadow gatewayもcapabilityなしに
  呼べない。
- reservation domain enum、attempt-global non-wrapping ticket allocator、ledger、prepared arena、opaque
  ticket/one-shot reserved operation、scope `Drop` cleanup、arena-take後の`InFlightCommitGuard`、child pin/prune
  protocolをshadowで追加する。
- `StructuralMutationDisposition`、private proof token、single finalizerの型を追加する。
- `dispatch_changed`と`try_prove_unchanged`をexhaustive matchにする。
- initial allowlistはempty。全commandのprover armはexplicit `None`。
- representative commandsをshadow replayし、receipt/dispositionを記録する。
- compile-fail/UI testでraw mutation capability/proof-token/private `PreparedStructuralCommand`構築不能を固定する。
- family siblingからprivate `PreparedPayload`をname/match/variant-constructできないcompile-failを固定する。prototypeの
  E0451 outer-struct probeで代用しない。
- compile-fail/UI testでactive capability/ticket/reserved-operation構築不能とfamily siblingからraw storageへ
  到達不能を固定する。

Gate:

- wildcard dispatch zero。
- intent→prepared payload mapping、prepared proof/dispatchのwildcard zero、一対一mappingのunassigned row zero。
- external/siblingから`PreparedStructuralCommand` / private payload fieldを構築するcompile-failがE0603/E0451相当で
  failure。
- token-freeを含む全`PreparedPayload` variantのfamily-sibling direct construction zero。
- arbitrary handlerによる`Unchanged` construction zero。
- active capabilityなしgateway/query/cache call zero。
- machine latch getter/marker、terminal attempt command rejectionのbaseline parity。
- two outstanding shadow ticketの同一spare slot二重計上zero。
- fresh distinct-domain first ticketsのglobal ID collision zero、multi-domain ticket registry entry exactly one。
- dropped handle/scope exit、arena take後early error/deliberate panic後prepared/ticket/outstanding/pin zero。
- shadow dispositionはgatewayが受理した全successful mutation-intent commandでChanged。caller-side pure no-intent
  returnは母数に含めない。
- production structural output/read path byte-identical。

Rollback: shell/shadowだけを除去できる。

### CPK-SV-D-SS2: proof-relation family migration

Authority: sealed proof relations。cache readなし。

- `ProofOccurrenceStore`のcache-relevant proof/formula/certificate/adjacency/replay/claim/live/index relationを
  `StructuralData::proof`へ吸収する。
- prepare/commitをtyped commandへ移す。
- claim move/live transition/formula admission/corruption hooksをsingle finalizerへ通す。
- CPK-SV-C committed receiptとzero dependent-adjacency fanoutを維持する。
- old proof-store raw mutable accessをcompile errorにする。
- formula/claim/live/index shared containerのreservation planとone-shot reserved-operation write portをproductionへ
  切り替える。
- 全production proof-family prepare/commit portがSS1 active capabilityを要求する。

Gate:

- full CPK-SV-A/B/C oracle mismatch zero。
- gatewayへsame-record move intentを明示的に発行するfixtureでsuccessful command finalizer count exactly one、
  snapshot bump exactly one（allowlist前baseline）。
- claim/live changed transition bump exactly one。
- failed/conflicted commit bump/receipt/secondary publication zero。
- old/new logical proof snapshot parity。
- proof-family changed handlerのstaged-build failure/panicではauthoritative write zero。publication phase panic point zero。
- formula shadow、live coverage、projection indexのclosed publication-plan operation coverage 100%、post-write
  `HashMap::insert`/comparison/`assert!`/`expect` zero。

#### SS2 gateway-level fixture contract

current `proof/mod.rs:18037`付近のraw `ProofOccurrenceStore` prepare/commit fixtureはsemantic compatibility
baselineとして残してよいが、以下のgateを一件も満たさない。以下は全て**new fixture**として、actual
`ConstraintMachine` production coordinatorまたは`ProofAttemptKernel::try_with_structural_preparation_scope`からtyped
intentを発行し、gateway、active capability、prepared arena、global ticket registry、one-shot operation、finalizerを
通す。raw store method直接呼出しを禁止する。

1. **Actual claim-first production order**
   - one preparation scope内でclaim prepare → formula prepare → claim commit → formula commitを行う。
   - claim/formula ticketが同時にactiveで、IDが異なることをassertする。
   - claim commit後もformula ticket/semantic baseがvalidで、両commit成功、snapshot bump各一回、secondary
     publicationは各committed receipt後だけ、commit-time allocation zero。
2. **Two domains, two first tickets**
   - fresh attemptでformula以外の二domain（例: claimとrow）を、それぞれdomain上のfirst ticketとして同時prepareする。
   - domain-local ordinalが双方zero相当でもattempt-global IDが異なり、`active_tickets.len() == 2`、reverse-order
     commit/cancelでwrong-ticket activation/release zero。
3. **One ticket spanning multiple domains**
   - formula admission等、parent `by_record`、child entries、exact linksを一commandで予約する。
   - ticket IDは一つ、claim vectorは複数domain、active registry entryは一つである。
   - commit/conflict/cancelの各caseで全domain unitsをexactly once releaseし、partial active entryを残さない。
4. **Pinned child removal/recreation**
   - `claims_by_upper_record`: childに一entryをseedし、同childへのinsert ticketをprepareしたまま別gateway commitで
     last entryをremoveする。childはempty/pinnedでparent mapとcapacityを保持し、outstanding insert commitが
     forced allocator failure下でも成功する。
   - 同じsequenceを`live_states_by_coverage_root`でも実行する。
   - cancel variantではlast ticket release後にpending empty childをpruneし、次のrecreation prepareがparent slotと
     child capacityを新規reserveする。read resultはpinned empty/absentでparity。
5. **Cleanup matrix**
   - genuine semantic conflict、explicit `scope.cancel`、ordinary `drop(handle)`後のscope exit、`?` early return、
     terminal-failure transition、normal scope exit、attempt teardownを別fixtureにする。
   - 各case後にprepared arena entries zero、`active_tickets` zero、全domain `outstanding_units` zero、pending empty prune
     zero、snapshot/receipt/secondary publicationはsuccessful commit分だけである。
   - arena entryをtakeした直後、semantic-base check、no-op prover、staged-output buildの各点へdeliberate panic/errorを
     注入する。`InFlightCommitGuard::Drop`後にactive ticket/outstanding unit/pinがzeroである。
   - first authoritative write後へpanic injection pointを置かないこと、または置けばfixture/static gateが失敗する
     negative controlをfamilyごとに持つ。
6. **Existing compatibility interleavings through gateway**
   - formula prepare → representative move A→B commit → formula commit。
   - move prepare → new dependent formula commit → move commit。
   - frozen expected-root/current late-binding semantics、spurious global-snapshot conflict zero、commit-time allocation zero。
7. **Same-container arithmetic negative control**
   - physical spare一slotでdistinct A/Bをoutstanding prepareする。B prepareはrequired spare総数をreserveし、
     `try_reserve(required-current)` mutationを一時注入するとfixtureが失敗する。
   - 両ticket発行後はforced allocator failure下のA/B commitが成功する。
8. **Same-target semantic conflict**
   - same missing target A/BをprepareしAをcommitすると、Bは`ExpectedSlot::Absent` mismatchとなる。
   - loser ticket/receipt/bump/secondary publication zero、scope cleanup後pin/ticket zero。

### CPK-SV-D-SS3: bounds family migration

Authority: sealed bounds。cache readなし。

- `TypeBounds::{vars, canonical, records}`を吸収する。
- lower/upper admit、promotion、tombstone、derivation extensionをtyped commandへ移す。
- bounds shared map/vectorのreservation planとone-shot reserved operationをproductionへ切り替える。
- incomplete-evidence bound creationを含む、gatewayが受理した全successful mutation pathをfinalizerへ通す。
- disposition/diagnostic attachmentをnon-structural sidecarへ分離する。
- initial allowlistは引き続きempty。duplicate/subsumedもsuccessful structural commandとしてChanged、または
  command自体を発行しないpure read-only duplicate decisionとする。raw writeを伴う第三経路は禁止。

Gate:

- bounds/output/worklist parity。
- gatewayが受理したsuccessful cache-relevant command finalizer exactly one。
- diagnostic-only attachment snapshot effect zero、preflight read zero。
- allocation/failure atomicity parity。
- bounds changed handlerのbuild-then-publish/panic-injection matrix green。
- bounds publication plan外のraw multi-container write zero。

### CPK-SV-D-SS4: constraint / replay family migration

Authority: sealed constraint relations。cache readなし。

- canonical constraint、constraint record、constraint→lower correspondence、replay drop/route/dependencyを吸収する。
- constraint/replay/index shared containerのreservation planとone-shot reserved operationをproductionへ切り替える。
- entry/propagation pathsをtyped intent/receiptへ移す。
- structural/row/replay/reduction-route proof publicationをclosed commandsへ統合する。
- projection-index target/edge branchを一つのChanged command finalizer下へ置く。

Gate:

- canonical/replay/qualified-parent/projection-index logical parity。
- target-only、edge-only、both、no-write branchが全てgatewayを通る。
- no-write branchはallowlistなしならChanged bump exactly one。
- failed sibling attemptのterminal semantics parity。
- constraint/replay changed handlerのbuild-then-publish/panic-injection matrix green。
- projection-index target-only/edge-only/bothが同じclosed publication-plan vocabularyでpanic-free publishされる。

### CPK-SV-D-SS5: row / identity migration and seal completion

Authority: all cache-relevant structural writers are sealed。cache readなし。

- row derivation/reduction/residual/processed-lower/lower-filterのrelevant stateを吸収する。
- origin/source-boundary/witness/scheme-instantiation identityを吸収する。
- row/identity shared containerのreservation planとone-shot reserved operationをproductionへ切り替える。
- location/timing/diagnostic metadataをsidecarへ分離する。
- `ConstraintMachine`から最後のraw structural fields/mutatorsを除去する。
- compile-fail/UI gateで外部raw mutationを全面禁止する。
- D0 scattered bumpをgateway finalizer shadowと比較後、production writer authorityから外す。

Gate:

- raw structural `&mut` escape zero。
- external moduleから`StructuralWriteTxn`/proof token構築zero。
- all current production structural mutationがclosed intent/private payload variantへ到達。
- full proof testsとlogical snapshot parity green。
- cache authorityはまだoff。
- row/identity changed handlerのbuild-then-publish/panic-injection matrix green。
- live flat/root-child等のmulti-container stateがclosed publication planを通り、last-child remove/pin decisionを
  first write前に固定する。

### CPK-SV-D-SS6: HRTB sealed query scope + evaluator/active-latch hardening

Authority: refined canonical validation through HRTB sealed query scope。cache hitはshadow-only。

- `ProjectionPreflight` / evaluatorを`ProofAttemptKernel::with_projection_query`内の
  `ScopedQueryView<'query>`へ切り替える。
- current borrowed `ProjectionEvaluationRound<'a>`をlifetime-free `ProjectionEvaluationRoundState`へ、borrowed
  `CpkPublicationEvaluationRound<'a>`をlifetime-free `CpkPublicationEvaluationRoundState`へ置換する。checked/memo/
  override/cycle/terminal stateだけをpersistし、targetごとにscope-local preflight/evaluator facadeをfresh構築する。
- 両round stateはstandalone constructor/`Default`を持たず、machine/kernel factoryだけがcurrent
  `(ProofAttemptNonce, ProofStructuralSnapshotId)`へbindして生成する。foreign-attempt stateはquery/cache lookup前に
  typed rejectionし、miss/rebindとして回復しない。
- production `SemanticFactView for ConstraintMachine` dependencyを除去する。
- machine/round latchをscope entryで一回checkし、scope全体を`&mut ProofAttemptKernel` / `&mut round`のexclusive
  borrowで囲む。getter/cursorごとのlatch checkを置かない。
- raw reference/view/cursorをscope closureからreturn/saveできず、scope中に同じkernelのterminal setterを呼べない
  HRTB compile-fail gateを追加する。scope外へ必要な値はowned descriptor/candidateへ変換する。
- `ConstraintMachine::{with_projection_query, with_publication_projection_query}`のexact split-borrow signatureを
  実装し、`&TypeArena`を各kernel wrapperへ明示的に渡してscope-local `ImmutableTypeShapeView`を作る。
  type-shape borrowをround stateへ保存しない。production evaluatorとmigration fixtureはこのmachine delegateだけを
  entrypointとし、bare publication kernel wrapperを直接呼ばない。
- `SchemeProjectableLower<'a>`をowned `SchemeProjectableLower`へ変え、selected `WeightedLowerBound`だけをscope内cloneする。
- §3.6のfallible `try_enter`を全record/constraint/root recursionへ実装し、checked-count reservation依存を
  除去する。
- `CpkPublicationEvaluationRound::eval_record`とproduction publication callerを`Result`伝播へ変える。
- `record_overrides` / `root_overrides` constructor/insertionをfallibleにする。
- §3.7の`with_projection_query` wrapperへprojection round、private cache port、owned candidate publicationを結合し、
  round/machine terminal orderingをfixture化する。
- cache lookup/publishをshadow計測するが、結果でvalidationをskipしない。
- allocator failure、cache-heavy synthetic closure、cycle+failure fixtureを実行する。

Gate:

- sealed view/canonical baseline output、error、owner、precedence parity。
- cache-hit-equivalentにchecked closureを空/小にしてもinfallible evaluator allocation zero。
- recursive states、record override、root overrideのallocator failureがtyped `ProjectLowerEvaluation` failureと
  なり、existing latchへ一回だけ記録。
- authenticated projection/publication scope constructorへallocation failureを注入し、両方ともwrapperから
  `?`で早期脱出せずcommon `Err` branchへ到達する。`requires_attempt_terminal()` caseはmachine latchをexactly once
  markし、projection reusable caseはround first-failureもexactly once記録する。
- publication-time evaluator allocation failure後、当該/後続semantic publication zero、whole-attempt terminal、
  partial output visibility zero。
- terminal latch後cache lookup/publication zero。
- terminal latch後prepare/commit/query port到達zero。latch前mutation tokenもport入口再checkで拒否される。
- query scopeからraw `&T`を返すprobeがE0515/lifetime error、scope closure内から同じkernelのterminal transitionを
  呼ぶprobeがE0500/E0501でcompile-fail。owned value returnはgreen。
- `ScopedProjectionQuery` / `ScopedPublicationProjectionQuery` / `QueryCompletion<R>` / both owned round-state typesが
  exactly `pub(in crate::constraints)`でre-exportされ、両方の`ConstraintMachine::with_*_query` closure-bound
  signatureが`#![deny(private_bounds, private_interfaces)]` buildでgreen。scopeの`complete(value)`からreceiptを
  作るpositive fixtureはgreen、`QueryCompletion` struct literal / `new` / `Default` / forged candidate constructionは
  compile-fail。fields/constructorsはsibling/external construction compile-fail。
- one owned roundでtarget A、scope exit、target Bを順に評価し、両targetのstructural readsが各自のscope内だけで、
  BがAのsame-snapshot checked record/constraintまたはacyclic evaluator memoを実際にhitするcompiler/runtime fixtureが
  green。facade/viewをround fieldへ保存するcompile-failもgreen。
- A/B間でsnapshotをChanged commitにより進めるvariantはsuccess-only checked/memoをclearし、old memo hit zero。
- **projection round専用negative fixture**: K1 factoryで`ProjectionEvaluationRoundState`を作りchecked/memoを
  warmし、same K1の二回目でreal hitを確認する。trace counterをsnapshot/reset後、同じnumeric snapshotの
  fresh K2の`ConstraintMachine::with_projection_query`へ同じroundを渡し、
  `ForeignAttemptRoundState { expected, actual }`を返す。payloadは`expected == Some(K2 nonce)`かつ
  `actual == Some(K1 nonce)`を明示assertする。stale checked/memo hit、K2 canonical
  read、round clear/rebind、cache lookup/publicationはすべてzero。K1 roundにsticky terminal failureを入れたvariantでも
  K1 failureではなく`ForeignAttemptRoundState`が優先する。
- **publication round専用negative fixture**: K1 factoryで`CpkPublicationEvaluationRoundState`を作りmemoと
  record/root overrideをwarmし、same K1の二回目でreal memo/override hitを確認する。trace counterを
  snapshot/reset後、同じnumeric snapshotのfresh K2の
  `ConstraintMachine::with_publication_projection_query`へ同じroundを渡し、
  `ForeignAttemptRoundState { expected, actual }`を返す。payloadは`expected == Some(K2 nonce)`かつ
  `actual == Some(K1 nonce)`を明示assertする。stale memo/override hit、K2 canonical read、round clear/rebind、cache
  lookup/publicationはすべてzero。projection fixtureの共通helper/counterだけで代用せず、publication wrapperを
  machine delegate経由のactual production entrypointとして呼ぶ。
- `SchemeProjectableLower` returnにborrowed field zero。owned bound equality parityとselected-only clone counterがgreen。
- stable/canonical trace mismatch zero。
- scope-entry check count exactly query-scope count、getter/cursor-step追加check zero。
- prototypeの`0.42〜0.88 ns/check`をcontextに、scope-entry/HRTB/owned conversion overheadをcache off/on双方で測り、
  RMW/stdのgross regression zero。

### CPK-SV-D-SS7: conservative Changed-only cache cutover

Authority: same-snapshot successful cache hit。missはrefined canonical validation。

このsliceの「Changed-only」は、no-op operationが存在しないという意味ではない。gatewayへ発行された
cache-relevant commandは、same-record moveやduplicate-like successful no-writeを含め、explicit proofが無い限り
Changed bumpする。callerがread-only precheckだけでmutation intentを発行しないpure no-opはcommandではなく、
snapshot/disposition母数に含めない。allowlistはemptyのままである。

- record/constraint success cacheをproduction lookupへ接続する。
- top-level unwind後だけcandidateをpublishする。
- failure、cycle-local success、partial traversalをpublishしない。
- forced-uncached modeをtest/env gateとして保持する。
- optional cache allocation failureはuncached fallbackにする。

Correctness gate:

- cached/forced-uncached output、error、evidence、cycle behavior mismatch zero。
- snapshot bump後old hit zero。
- back-edge cycle+dangling leaf candidate publish zero。
- failure cache entry zero。
- saturation後hit/publish zero。
- no-claim allocation zero。

Performance decision gate:

- RMW N=1..6をsame-binary cache on/off、各3回以上でmin/median/max比較する。
- cold `std::text::parse`も同条件で比較する。
- hit/miss、expansion、candidate、evaluator reserve、wall、RSSを報告する。
- RMW N=6 medianがnoiseを超えて改善しない、またはhit率がnegligibleならcutoverをcommitせず停止する。
- SS7未達をSS8の大量allowlist追加で救済しない。

### CPK-SV-D-SS8+: one-command `Unchanged` allowlist

一sliceにつき一command/no-op predicateだけを追加する。候補順はSS7 censusで決める。same-record upper-claim
moveまたはexact-duplicate boundは候補だが、事前に採用を確定しない。

各slice:

- read-only command-specific proverを一件追加する。
- proof成立時mutating handler非呼出しをcounter/negative controlで確認する。
- equal、one-field-different、secondary-index-different、base-mismatch fixtureを追加する。
- false proof injectionがforced-uncached parityを必ず失敗させるnegative controlを持つ。
- no-op frequency、additional hits、comparison cost、wall/RSSをA/B測定する。
- independent adversarial review完了後だけ次entryへ進む。

Gate:

- allowlist外proof token construction zero。
- comparisonなしUnchanged zero。
- changed case bump exactly one、proven no-op bump zero。
- performance benefitがcomparison overheadを超える。

Rollback: 対象prover/proof variantを除き、commandをChangedへ戻せる。

### CPK-SV-D-SS9: integration / closeout

- RMW N=1..6、cold/warm std、representative corpusを最終測定する。
- full safety-scoped proof tests、CPK-SV-A/B/C、MPC/DPN cycle/error oracleを実行する。
- full-workload forced-uncached parityを実行する。
- profileでpreflight saving、gateway overhead、cache overhead、evaluator fallibility costを分離する。
- D0 scattered writer tags/counters、temporary shadow adapter、migration flagsを整理する。
- final command vocabulary、allowlist、proof predicates、capacity-inclusive footprintを記録する。

Gate:

- correctness mismatch zero。
- RMW改善がwall/counter/profileの三者で説明可能。
- std/corpus gross regressionなし。
- peak RSSが18 GiB hard limitから十分離れる。
- independent adversarial reviewとユーザcloseout承認完了。

## 8. Invariants

CPK-SV 追補のinvariant 21〜36、CPK-SV-C redesignの既存invariant、CPK計画の全invariantを継承する。
round 5/round 6の番号は未承認draftに属し予約されていないため、本書固有の統合invariantを37から
新規に定義する。

37. **Sealed structural ownership**
    - cache-relevant authoritative stateは`ProofStructuralState`だけが所有する。
    - external moduleへraw mutable field/reference/callbackを公開しない。

38. **Sealed read surface**
    - production `ProjectionPreflight`とevaluatorはHRTB `ScopedQueryView<'query>`だけからmandatory factを読む。
    - raw reference/view/cursorをquery closure外へ返さない。
    - `ConstraintMachine`や任意trait implementerをstructural read authorityにしない。

39. **Closed mutation vocabulary**
    - caller requestはdata-only closed `StructuralMutationIntent`、reservation-bearing formはgateway-private closed
      `PreparedPayload`をprivate-field `PreparedStructuralCommand`が所有する形として別々に表す。
    - intent→prepared mapping、changed/no-op dispatchにwildcard armを置かず、new variantはcompile-time更新を要求する。
    - `PreparedPayload`はgateway module完全privateであり、token-free variantを含めcaller/family siblingは
      name/match/constructできない。

40. **Single successful-commit finalizer**
    - gatewayがmutation intentを受理して返すevery successful commitはexactly one finalizerへ戻る。
    - handler、caller、early returnがsnapshot publicationを直接行わない。

41. **Conservative Changed default**
    - proofが無いsuccessful gateway commitは、actual write countに関係なく`Changed`である。
    - uncertainty、new branch、comparison failureを`Unchanged`へ倒さない。

42. **Private command-specific Unchanged proof**
    - `Unchanged` tokenはsmall private allowlistのread-only typed comparatorだけが構築できる。
    - generic constructor、arbitrary handler construction、cross-command token reuseを禁止する。

43. **No mutation after Unchanged proof**
    - proof成立pathは`StructuralWriteTxn`を構築せず、mutating handlerを呼ばない。
    - no-op receiptだけをsingle finalizerへ返す。

44. **No early-return escape**
    - callerがmutation intent発行前にpure read-only no-opと判定してreturnするpathはdisposition対象外である。
    - そのpathはraw state、prepared receipt、secondary publicationを変更できない。
    - changed handler内early returnはreceiptとしてgatewayへ戻り、Changed finalizerを通る。
    - gatewayが受理したintentのno-op returnはproof付きUnchangedまたはconservative Changedの二択であり、
      第三経路を持たない。

45. **Prepare-before-write atomicity**
    - ID bound、semantic base check、shared-resource ticketはwrite capability構築前に解決する。
    - changed applyはstaged outputとclosed `Prepared*PublicationPlan`をauthoritative write前に完全構築し、publicationは
      audited allocation-free/panic-free typed primitivesだけである。
    - failed prepare/conflict/whole-attempt discardはstate/snapshot/cache/receiptを変更しない。

46. **Atomic snapshot publication**
    - Changed commitは全authoritative write完了後にsnapshotを一回だけ進める。
    - multi-field commit途中のsnapshotを公開しない。

47. **Saturating snapshot safety**
    - `ProofStructuralSnapshotId`はwrapしない。
    - saturation後はreuseをdisableし、old cacheをclearする。

48. **Successful structural outcome only**
    - cacheはfully-resolved structural successだけを保存する。
    - failure、error、owner、projectability、evidence、cycle-cut、`Visiting`を保存しない。

49. **Top-level cache publication**
    - visiting stack完全unwind後のtop-level successでだけcandidateをpublishする。
    - round-local checked insertionとpersistent cache publicationを分離する。

50. **Evaluator insertion fallibility**
    - cache hitでpreflight checked closureが小さくても、every new evaluator state/record override/root override
      keyはfallible capacityを保証してからinsertする。
    - checked-count bulk estimateをallocation safetyの根拠にしない。
    - fallible `project_lower`とpublication-time `eval_record`の両production pathが`Result`を伝播する。

51. **Terminal latch precedence**
    - active-attempt capabilityなしにmutation portへ、HRTB exclusive query wrapperなしにquery/cache portへ到達できない。
    - round/machine terminal latchはquery scope entryより先に、owned candidate publish直前にも働く。
    - cache hitはsticky failureをclear、replace、maskしない。
    - terminal control stateをfailure cacheと混同しない。

52. **Committed receipt authority**
    - secondary index、queue、event publicationはsuccessful committed receiptだけを根拠にする。
    - prepared intentまたはfailed/conflicted commandからpublishしない。

53. **No partial-sealing cache authority**
    - SS1〜SS6の一部familyだけsealedな状態ではproduction cache hitを有効化しない。
    - cache authorityはall raw writers sealed、HRTB query scope cutover、capacity/latch gate後に限る。

54. **Non-structural sidecar separation**
    - diagnostic/timing/location metadataを`Unchanged` structural writeとして扱わない。
    - production preflightが読むようになったfactは同じchangeでsealed structural stateへ移す。

55. **CPK-SV-A/B/C preservation**
    - certificate/order authority/stable obligation/late binding/support-ledger closure/canonical fallbackを
      cache都合で変更しない。

56. **Evaluator memo separation**
    - structural successからprojectability/evidence/cycle resultを推定しない。
    - MPC/DPN round lifetime、cycle-cut sharing disable、fresh fallbackを維持する。

57. **Optional cache allocation safety**
    - cache borrow/reservation failureはuncached canonical validationへ戻る。
    - cache convenienceのためにpanic/new semantic failureを生まない。

58. **No-claim preservation**
    - no formula/no claim workloadへpersistent cache heap allocationを追加しない。

59. **Allowlist auditability**
    - production `Unchanged` proof variant、constructor、predicate、fixture、performance resultを全件列挙可能に
      保つ。

60. **Trusted-boundary honesty**
    - compile-time visibilityが証明するescape closureと、runtime/test/reviewが証明するhandler/comparator
      semanticsを区別する。
    - large handler LOCを「小さなtrusted kernel」と誤称しない。

61. **Changed-only value before allowlist growth**
    - SS7がRMWで実益を示す前に`Unchanged` allowlistを増やさない。

62. **Single-thread completed-snapshot premise**
    - current solverのsynchronous completed-commit orderingを前提とする。
    - true parallel query/mutationを導入する場合、本書のexclusive `&mut ProofAttemptKernel` scope/ordering argumentを
      そのまま使わない。

63. **Snapshot / conflict separation**
    - `ProofStructuralSnapshotId`はcache invalidation identityだけであり、prepared commit conflict baseにしない。
    - formula/claim/moveのapproved interleavingをglobal snapshot advanceだけでrejectしない。

64. **Semantic-base precision**
    - prepared commandはdelta計算に実際に読んだtarget/relationship-local revisionだけをbaseに持つ。
    - CPK-SV-Cがquery-time late bindするcurrent claim/live stateをformula semantic baseへ戻さない。
    - absent/present transitionとdelete/recreate ABAを検出し、local revision/generationをwrap/reuseしない。

65. **Outstanding reservation closure**
    - one attempt-global non-wrapping allocatorが全domain/multi-domain ticketへunique IDを一回だけ発行する。
    - active registryはone ticket/one ID/one entryで全domain claimをexactly once所有する。
    - shared resource domainごとに`physical_spare >= outstanding_units`を維持する。
    - distinct prepared commandが同じphysical spare slotを二重予約しない。
    - new-key/new-element writeはtyped one-shot reserved operationまたはbase-bound existing-slot witnessなしに
      実行できない。
    - commit/conflict/cancel/terminal teardown後にticketをleakしない。
    - outstanding prepared objectは後発reserveでinvalidになるshared-container reference/raw entryを保持しない。
    - child domainのoutstanding unitsがzeroになるまでempty child containerとcapacityをpinする。

66. **Concrete Rust privacy boundary**
    - raw storageはgateway child、family handlersはgateway siblingに置く。
    - familyはgateway-created write portだけを受け、raw storage/write-port constructorへ到達しない。

67. **Active-attempt access closure**
    - machine terminal latchとstructural stateを`ProofAttemptKernel`が所有する。
    - private active capabilityをprepare/commitのrequired parameterとし、port入口で再checkする。
    - query/cacheは`&mut ProofAttemptKernel`をborrowするHRTB scopeだけから到達する。
    - terminal attemptではticket cleanup以外のstructural operationを開始しない。
    - getter/cursorのraw borrowはscope外へescapeせず、scope中にsame-kernel terminal transitionを開始できない。

68. **Publication evaluator failure propagation**
    - publication-time evaluator/override allocation failureを`bool`へ畳まずtyped failureとして伝播する。
    - failure後の当該/後続publicationを停止し、terminal attemptのpartial outputを外部commitしない。

69. **Kernel-owned prepared lifetime**
    - prepared mutation/ticketはcaller handleではなくkernel arenaとbounded preparation scopeが所有する。
    - scope `Drop`がordinary handle drop、`?`、early return、panic unwindのuncommitted slotsをreleaseする。
    - arena take後からfinishまでは`InFlightCommitGuard`がprepared/ticketを所有し、early error/panicでreleaseする。
    - scope-bound handleはscope外へescape、clone、queueできない。

70. **Pinned-empty semantic transparency**
    - pinned empty childとabsent childはproduction semantic read/cursorで同じ結果を返す。
    - pending pruneはsnapshot/cache identityを変えず、outstanding zero後だけallocation-freeに物理removeする。

71. **Restricted cross-sibling visibility**
    - cross-sibling type namingに必要な型/methodだけを
      `pub(in crate::constraints::structural_kernel)`へ公開する。
    - field、constructor、raw mutator、capability/token constructorを同visibilityへ広げない。

72. **Non-panicking authoritative publication**
    - changed handlerはowned staged replacement/delta/receiptとclosed family publication planを最初のauthoritative
      write前に完全構築する。
    - first write後にallocation、fallible conversion、hash/user callback、panicking `Drop`、assert、`?`を実行しない。
    - この規律で表せないmulti-field commandはmigrateを停止する。co-owned aggregate再分割またはrollbackは別途
      signed designと独立査読なしに導入しない。

73. **HRTB query lifetime closure**
    - query closureのreturn typeは`for<'query>`によりraw structural borrowを含められない。
    - query scopeが`&mut ProofAttemptKernel`をborrowする間、same kernelのterminal/mutation methodはcompileしない。
    - per-getter `RefCell`/`Cell` checkをraw-reference revocationの根拠にしない。

74. **Prototype evidence boundary**
    - `/tmp/cpk-sv-d-kernel-skeleton`はtype/lifetime/privacy patternのevidenceでありproduction authorityではない。
    - E0603/E0451/E0515/E0500/E0501のlocal proofをsemantic/capacity/full-call-graph proofへ誇張しない。
    - prototypeは`PreparedPayload` token-free variantのsibling construction拒否も、rev.4 narrow scope-type visibilityも
      証明していない。production compile-fail gateを別に要求する。

75. **Lifetime-free round persistence**
    - cross-target checked/memo/override/cycle/terminal sharingはborrowを持たないowned round stateだけが保持する。
    - store/view/machine/type-shape borrowをroundへ保存せず、preflight/evaluator facadeはtarget scopeごとにfreshである。
    - normal modeではmachine/kernel factoryだけがroundをcurrent `(ProofAttemptNonce,
      ProofStructuralSnapshotId)`へbindして生成する。standalone constructor/`Default`を公開しない。
    - projection/publicationの両wrapperはcurrent kernel latch → attempt binding → matched round-local latchが
      存在する場合の確認 → snapshot/memo/override/cacheの順を守る。foreign roundのterminal/error stateを読まない。
    - same attempt / same snapshotだけmemoをreuseし、same-attempt snapshot change時はterminal failureを除く
      success-only stateをclear/rebindする。foreign attemptはtyped rejectionし、miss/rebindとして扱わない。
    - attempt nonce allocator exhaustion後はnonceをwrap/reuseせず、cacheとcross-scope round reuseをprocess永続で
      disableする。

76. **Exact query-scope visibility and construction**
    - public restricted wrapper signatureへ現れるscope/round typeはexactly `pub(in crate::constraints)`でre-exportする。
    - fields/constructors/cache portはprivateであり、broader callerはclosure inference/getterだけを使う。
    - `TypeArena`は`ConstraintMachine` field split-borrowからexplicit parameterでscopeへ入り、kernel/roundへ保存しない。

77. **Owned result boundary**
    - query scope外へ返すresultはstructural storageへのreference/cursor/viewを含まない。
    - `SchemeProjectableLower::bound`はowned `WeightedLowerBound`であり、raw borrowを再導入しない。

78. **Closed multi-container publication**
    - multi-container commandはfamily-specific closed publication-plan enumだけをpublishする。
    - first write前にlookup/hash/equality/assert/drop riskを解決し、publish primitiveのconcrete key/hash/drop contractを
      SS0 tableでauditする。
    - general rollbackやwhole-family clone/swapへsilent fallbackしない。

## 9. Stop conditions

次の一つでも発生した時点で次sliceへ進まず、本書の再設計・再査読へ戻る。

### 9.1 Sealing / gateway

1. SS5完了後もexternal moduleがcache-relevant raw fieldまたは`&mut`を取得できる。
2. `DerefMut`、`AsMut`、generic mutation closure、open trait implementationでgatewayを迂回できる。
3. `StructuralWriteTxn`をsingle commit gateway以外が構築できる。
4. gatewayが受理したmutation intentのsuccessful commitがsingle finalizerへ戻らないreturn pathを持つ。
5. handler/callerがsnapshotを直接bump/維持する。
6. `dispatch_changed`またはno-op dispatchにwildcard armがある。
7. target/relationship-local semantic base mismatchをauthoritative write後に発見する。
8. changed applyがticket/one-shot reserved operationなしnew-key insertを行う、またはfirst authoritative write後に
   allocation/error/panic/`?`/user callbackへ到達し得る。
9. one commandのatomic boundaryをsealed stateへ移すと既存CPK transaction invariantを維持できない。
10. partial migration中にold/new storeが同じfactの二重authorityになる。
    - multi-container changed commandがclosed prepared publication planへ落ちず、raw sequential write、post-write
      comparison/assert/hash callback、または未査読rollbackを必要とする場合もfamily migrationをstopする。

### 9.2 Conservative disposition

11. arbitrary command handlerが`ExplicitNoOpProof`を構築できる。
12. `Unchanged` proof pathが`StructuralWriteTxn`またはmutating handlerを呼ぶ。
13. prepared payload variantと異なるkindのproof tokenを受理できる。
14. old/new exact comparisonなしに`Unchanged`を返す。
15. comparatorがprimary fieldだけを見て、preflightが読むsecondary relation/indexを落とす。
16. prepare時proofをcurrent base recheckなしにcommitする。
17. no-op semantics変更後も古いproof predicateがgreenになり、fixture/reviewで検出できない。
18. unknown/new branchがChangedではなくsilent Unchangedへ落ちる。
19. no-op proverがcommit中にallocation、unbounded collect/sort、fallible error returnを必要とする。
20. commandがpost-mutation observationなしにdispositionを決められず、conservative Changedにも倒せない。

### 9.3 HRTB query scope / cache / evaluator

21. production preflightがHRTB sealed query scope外のmutable/cache-relevant inputを読む。
22. `TypeArena` existing payloadがin-place mutation可能なのにexternal immutable exceptionを使う。
23. SS7前にproduction cache hitを有効化する。
24. cache hit後のevaluator state/record override/root override insertionがinfallible reallocationし得る。
    - publication-time `eval_record`がallocation failureを`false`/fail-openへ畳む、またはfailure後も
      publicationを続ける場合も同じstop conditionとする。
25. per-node fallible reserveが実workloadで説明不能なgross regressionを生み、代替fallible strategyも成立しない。
26. failure、owner、projectability、evidence、cycle-cut、Visitingをcacheへ保存する必要が生じる。
27. top-level failure/cycle unwind前に`Valid(snapshot)`がpublishされる。
28. snapshot mismatch/saturation後にcache hitする。
29. optional cache allocation/borrow failureがpanicまたはsemantic output差を生む。
30. no-claim pathにpersistent allocationが生じる。
    - query getter/cursorがraw reference/viewをHRTB closure外へ返せる場合もstopする。
    - active query scope中にsame `ProofAttemptKernel`のterminal/mutation methodをsafe Rustで呼べる場合もstopする。
    - per-getter `RefCell`/`Cell` recheckをraw-reference revocationの根拠として復活させる場合もstopする。
    - owned round stateが`ProofStructuralState` / `ConstraintMachine` / `TypeArena`へのborrowを保持する場合もstopする。
    - same round内の複数top-level target checked/memo sharingを失う、またはsharingのためfacade/viewをscope外へ保存する
      場合もstopする。
    - `SchemeProjectableLower`その他production resultがsealed structural borrowをscope外へ返す場合もstopする。

### 9.4 Terminal failure / existing semantics

31. round terminal latch後にcache lookup/publishする。
32. machine attempt-terminal latch後にactive capabilityを発行する、またはnew prepare/commit/query/cache operationを
    開始する。
33. cache hitが既存sticky failureをclear/overrideする。
34. evaluator failure後、machine latch設定前に別roundがcacheを利用できるinterleavingが実在する。
35. terminal latchとの調停にfailure cacheが必要になる。
36. CPK-SV-A/B/C、MPC/DPN cycle、error precedence、committed receipt authorityを変更しなければ成立しない。

### 9.5 Project viability

37. SS7 Changed-only cacheのRMW hit率がnegligible、またはmedian wallがnoise内/negativeである。
38. SS7未達を、多数の`Unchanged` entryを一括追加して救済しようとする。
39. no-op comparator costが追加hitのsaved workを上回る。
40. cold std/corpusへ説明不能なwall/RSS regressionが出る。
41. peak RSSが18 GiB hard limitへ近づく、またはcapacity-inclusive footprintを説明できない。
42. counterだけ改善し、wall/profileが改善しない。
43. true parallel mutation/queryが導入される。
44. **本統合後にも、raw cache-relevant mutation、またはgatewayが受理したintentのsuccessful commitが
    gateway/finalizer/Changed defaultを迂回する新しいescape pathが一件でも見つかる。** callerがmutation
    intent発行前に行うpure read-only no-op returnとは区別する。真のescapeなら七回目の同型gapとして局所patchを
    止め、same-snapshot cache project自体を継続するか再判断する。

### 9.6 Reservation / capability / privacy

45. global `ProofStructuralSnapshotId`をprepared commit conflict baseへ使う。
46. actual claim prepare→formula prepare→claim commit→formula commit、formula-first compatibility、または
    move prepare→formula commit→move commitを、無関係なsnapshot advanceだけでrejectする。
47. distinct targetのoutstanding prepareが同じshared-container spare slotを二重予約できる。
48. `physical_spare >= outstanding_units`を維持できないdomainが一件でもある。
49. gateway publication plan/command-specific portがtyped one-shot reserved operation/existing-slot witnessなしに
    new-key/new-element insertできる、またはfamily handlerがraw insertへ到達できる。
50. conflict、cancel、terminal transition、attempt teardownでticket/outstanding unitが残る。
51. resource ticketをsemantic baseとして扱い、別target/unrelated writerをspurious conflictにする。
52. family moduleがRust parent/child privacyを通してraw storageへ到達できる。
53. mutation active capabilityをarbitrary callerがconstruct/cloneできる、またはmutation portが入口でlatchを
    再checkしない。
54. machine terminal latchを`ProofAttemptKernel`外から直接clearし、同attempt cache/ticketを再利用できる。
55. evaluator/publicationの`Result`伝播により既存whole-attempt discard semanticsを維持できない。
56. domain-local counter/ordinalをglobal `active_tickets` keyに使う、またはmulti-domain ticketへ複数IDを発行する。
57. attempt-global ticket counterがwrap/reuseする、ID発行後にfallible returnがありpartial ticket publicationを残す。
58. outstanding unitsがあるchild containerをlast-entry removalでdropする。
59. pinned empty childをsemantic cursor/fanoutがreal entryとして観測する。
60. ordinary handle drop/`?`/early returnでpreparation scopeを抜けた後もarena/ticket/pinが残る。
61. prepared handleがscope lifetimeを越えてqueue/field/return valueへescapeできる。
62. `ScopedQueryView`/cursor/raw referenceがquery closure外へescapeする、またはquery scope内でterminal transitionを
    開始できる。
63. cross-sibling type namingのためraw field/constructor/mutatorを`pub(crate)`またはkernel-wide visibilityへ広げる。
64. SS2 gateway fixtureをold raw `ProofOccurrenceStore` fixtureのpassで代用する。
65. public `StructuralMutationIntent`とprivate reservation-bearing `PreparedStructuralCommand`を一型へ畳む、または
    private tokenをoptional/untyped side channelとしてcaller/familyへ露出する。
66. arena entry take後からfinishまで`InFlightCommitGuard`以外のownerless ticket windowがある。
67. `InFlightCommitGuard`がreservationをreleaseできても、changed handlerのpartial authoritative write後panicを
    build-fully-then-publish規律/rollbackなしに許す。
68. `ScopedProjectionQuery` / `ScopedPublicationProjectionQuery` / `QueryCompletion<R>`またはowned round-state
    typeのvisibilityがwrapperより狭く`private_bounds`/private-type failureを起こす、またはreceiptの
    fields/constructor/candidate internalsをcallerへ公開して回避する。
69. `PreparedPayload`をkernel-wide visibleにしてtoken-free variantをfamily siblingが直接construct/matchできる。
70. `with_projection_query`が`ImmutableTypeShapeView`のsourceを暗黙global/raw accessorから得る、またはtype-shape
    borrowをroundへ保存する。

stop conditionをvisibility緩和、test期待値変更、organic mismatch除外、fail-open、cache key粗化、
error順序変更で回避してはならない。

## 10. Claude独立査読 checklist

Claude (Sonnet 5) は、統合理論の両側が本当に接続されているかを次で独立に反証する。

### 10.1 Round 6 early-return counterexample

1. current `commit_upper_claim_move`のsame-record early returnを実際に追い、SS2後のequivalent call graphを
   描けるか。
2. callerがmutation intent発行前にpure read-only判定でreturnするpathと、gatewayが受理したcommandを区別して
   いるか。前者がraw state/prepared receipt/secondary publicationを一件も変更できないか。
3. changed handlerがsame-recordでearly returnしてもgatewayの`Applied::changed`へ戻るか。
4. same-record no-op proofを追加した場合、read-only prover成功後にmutating handlerが一切呼ばれないか。
5. new write branchをchanged handlerへ追加しても、proofなしbaselineは必ずChangedになるか。
6. external callerが既存private helperを直接呼び、finalizerを迂回できないか。

### 10.2 Round 5 command-internal classification counterexample

7. mutating handler内にhand-written `changed: bool`が残らないか。
8. handlerは`Unchanged` tokenまたはdispositionを直接返せないか。
9. no-op token constructorはprivate typed prover以外から到達不能か。
10. command/proof variantの対応がexhaustiveで、generic/wildcard token reuseがないか。
11. proof成立pathがwrite capabilityを一度も作らないか。
12. allowlisted command semanticsへnew fieldを追加した場合、comparison/fixture更新漏れを反証できるか。
    compilerが完全には保証しない残余riskが文書どおり限定されているか。

### 10.3 Trusted kernel boundary

13. §3.1.1のactual module treeで`StructuralData` field visibilityはどこまで届くか。Rustのparent-private itemを
    childが読める規則を使い、family siblingがgatewayなしでraw stateへ到達できないことを確認したか。
14. `StructuralWriteTxn` constructor、raw data accessor、mutable callbackの全visibilityを確認したか。
15. public `StructuralMutationIntent`がdata-onlyで、private `PreparedStructuralCommand` / `PreparedPayload` /
    `ReservedInsert`をcallerがname/construct/extractできないか。
    - prototypeのouter-command E0451をpayload variant拒否へ誇張せず、productionでは`PreparedPayload`自体がgateway
      complete-privateでtoken-free variantもfamily siblingからname/match/construct不能か。
16. compile-fail/UI testがfield access、private prepared command/token construction、custom command、`DerefMut`
    escapeを反証するか。prototypeのE0603/E0451 evidenceとproduction module layoutが一致するか。
17. trusted **API/capability surface**とtrusted **semantic handler LOC**を混同していないか。
18. kernel module自身に残るtrusted codeが大きすぎて一回のreviewで扱えない場合、family slice reviewが
    実効的に分割されているか。

### 10.4 Mutation atomicity / receipt

19. every persistent reserve、ID bound、semantic base check、reservation ticket発行がwrite token前に完了するか。
20. conflict return前にprimary/secondary state、snapshot、cacheを変更していないか。
21. changed handlerはauthoritative write前にstaged outputを完全構築し、publication phaseがallocation-free/
    panic-free/infallible move/swapだけか。
    - formula shadow、live coverage、projection indexのmulti-container updateがclosed family publication planに入り、
      concrete ID `Eq`/`Hash`/hasher/dropとpost-write operationをauditしたか。
22. one handler returnにつきfinalizer exactly oneか。double bumpもmissing bumpもないか。
23. prepared intentではなくcommitted receiptだけがsecondary publication authorityか。
24. sibling commit後のgenuine semantic conflictがexisting terminal-failure/whole-attempt discardへ届く一方、
    unrelated global snapshot advanceをconflictにしていないか。
    - arena take直後からfinishまで`InFlightCommitGuard`がticketを所有するか。
    - deliberate panic/early error後にactive ticket/outstanding unitがzeroか。
    - first authoritative write後にpanic injection pointが残らないか。RAII cleanupをsemantic rollbackと誤認して
      いないか。

### 10.5 Evaluator capacity

25. cache hitで`checked_records/constraints`がrootだけまたはzeroに近くても全evaluator node insertがfallibleか。
26. `try_enter`以外の`states`/`record_overrides`/`root_overrides` map/set insertにinfallible growthが残らないか。
27. `finish`がexisting key replacementだけであることを実装・fixtureで確認したか。
28. recursive queryとpublication-time evaluator双方のforced allocator failureがtyped
    `ProjectLowerEvaluation`となり、partial round memo/outputを再利用しないか。
29. per-node reserve overheadをRMW/stdで実測し、gross regressionを隠していないか。

### 10.6 Failure / latch reconciliation

30. `ProjectionEvaluationRound::terminal_failure` checkがcache lookupより前か。
31. machine terminal latch後にmutation `ActiveProofAttempt`をmintできず、latch前tokenもport入口の再checkで
    prepare/commitを開始できないか。query/cacheはHRTB wrapper entryで拒否されるか。
32. structural validation failureがcandidateを一件もpublishしないか。
33. evaluator failure前にpublish済みのstructural successが、round/machine latchを越えて読まれないか。
34. latchをclearして同じattempt cacheを再利用するproduction APIがないか。
35. terminal failureとsnapshot-keyed failure cacheを混同していないか。

### 10.7 HRTB read closure / round state / CPK-SV preservation

36. production preflight/evaluatorのmandatory readが全て`with_projection_query`内の
    `ScopedQueryView<'query>`にあるか。
    - raw reference/view/cursor returnがE0515/lifetime errorでcompile-failするか。
    - query scope内same-kernel terminal/mutation callがE0500/E0501でcompile-failするか。
    - owned value/candidate returnだけがcompileするか。
    - per-getter RefCell/Cell recheck adapterがproductionに残っていないか。
    - current borrowed round/preflight/evaluatorをowned round state + scope-local facadeへ分離し、same-round A/B targetが
      checked/memoを共有しながら各target readを別scope内に閉じるか。
    - round state fieldにstore/view/machine/type-shape borrowがzeroか。attempt+snapshot bindingを持ち、snapshot
      change時old success memoをclearし、foreign attemptをtyped rejectionするか。
    - `ScopedProjectionQuery`とround typesがexactly `pub(in crate::constraints)`で、fields/constructors privateか。
    - `ConstraintMachine`が`types` / `proof_attempt`をfield split-borrowし、exact `&TypeArena` parameterからscope-local
      shape viewを作るか。
    - `SchemeProjectableLower::bound`を含むscope外resultがownedで、borrowed structural field zeroか。
37. claim/live transitionsがsealed Changed finalizerを通り、old snapshot hitを防ぐか。
38. CPK-SV-Cのlate-binding、support-ledger closure、RepresentativeRootMismatch、typed live-index failureを
    維持するか。
39. CPK-SV-A certificateがcurrent dynamic stateをcertifyしたことになっていないか。
40. CPK-SV-B error precedenceをcache hit/missで変えていないか。
41. `projection_lower_records_by_root`等scope外semantic mapを誤ってretireしていないか。
42. projectability/evaluator memo lifetimeをstructural cacheへ取り込んでいないか。

### 10.8 Slice discipline / value

43. SS1〜SS6でproduction cache authorityが完全offか。
44. family移行ごとにold/new logical output parityとraw-access compile failureを確認するか。
45. SS7のChanged-onlyが既存no-opをproofなしChangedとして正しく数えるか。
46. §2のraw hit opportunityをSS7 speedup保証へ誇張していないか。
47. SS7単独でRMW実益が出なければSS8へ進まないgateが実効的か。
48. SS8+が一slice一prover、一fixture matrix、一A/B、一reviewか。
49. cold stdの26.63% opportunityをbroad performance promiseへ変えていないか。
50. RSS 18 GiB protocol、same-binary A/B、median-of-3以上をcloseoutで固定するか。

### 10.9 Integration theoryへの最終反証

51. sealingが閉じるのは本当に「finalizerへ到達しないpath」か。それともearly returnをkernel内部へ移しただけか。
52. conservative defaultが閉じるのは本当に「internal logicの不完全性」か。それともprover側へ同じ
    hand-written boolを移しただけか。
53. no-op proverがread-only exact comparisonであり、changed handlerのwrite branch countを推測していないか。
54. storage/read/mutation capabilityの境界が、reviewerが全escapeを列挙できる大きさか。
55. 一件でも新escapeが見つかった場合、局所追補ではなく§9.5-44のproject再判断へ戻るか。

### 10.10 rev.5 resource / capability / lifetime反証matrix

56. `ProofStructuralSnapshotId`がcache identity以外のsemantic base/ticket invalidationへ使われていないか。
57. formula prepared objectがcurrent claim/live authorityをbaseに持たず、move prepared objectがformula revisionを
    baseに持たないか。
58. **new gateway fixture**でactual claim prepare→formula prepare→claim commit→formula commit、
    formula prepare→representative move→formula commit、move prepare→formula commit→move commitを成功させ、
    commit-time allocation zeroを確認したか。old raw-store fixtureだけを根拠にしていないか。
59. distinct missing target A/Bのoutstanding prepareが同じshared `by_record` mapで二slot分をaggregate reserveし、
    A commit後もB ticketのcapacity invariantが残るか。
60. physical spare one-slot fixtureで二ticketが同じslotを二重計上しないか。commit allocator-failure injection下で
    発行済み両ticketがallocationなしにcommitできるか。
    `try_reserve(required_spare - current_spare)`という誤った差分reserveをnegative controlが検出するか。
    - B prepareのrehash/reallocation後もA prepared objectがdangling reference/raw entryを持たず、stable IDから
      commit-time re-resolveするか。
61. same-target semantic conflict、explicit cancel、ordinary handle drop + scope exit、`?`、terminal transition、
    normal scope exit、attempt teardownの全pathでarena/ticket/outstanding unitがzeroへ戻るか。
62. existing prepared payload variantへnew insert branchを加え、prepare delta/reservation planを更新しないnegative compile
    fixtureがprivate one-shot tokenを構築できず失敗するか。
63. `ProofAttemptKernel`以外がactive capabilityをconstruct/cloneできないか。machine latch raw fieldが外部に
    残っていないか。
64. terminal transition後、prepared handleはcommit不能だがkernel-owned scope cleanupでticketだけをreleaseできるか。
65. `CpkPublicationEvaluationRound::eval_record`からsemantic publication caller末端まで`Result`が途切れず、
    `bool`/fail-openへ変換されないか。
66. record/root override insertの全constructorがfallibleで、test convenienceだけがinfallible old pathを残して
    いないか。
67. gateway外caller no-op returnをmandatory-disposition countへ混ぜず、同時にraw writeを伴うprecheck escapeを
    「no intent」と誤分類していないか。
68. §3.1.1のexact `pub(in ...)` declarationsがactual Rustでcompileし、`access.rs`/`gateway`/`read_view`の
    cross-sibling namingだけを許し、field/constructor/raw mutatorを許さないか。two-type splitと
    `InFlightCommitGuard`を含むfuller type setでもE0603/E0451 negative probeが成立するか。
69. fresh attemptの異domain first ticketsが異なるattempt-global IDを持ち、`active_tickets.len() == 2`か。
70. one multi-domain ticketがone ID/one active registry entryを持ち、全claimを一回のtakeでreleaseするか。
71. `next_ticket_id`はledger直下に一つだけで、`u64::MAX`後にtyped exhaustionとなりwrap/reuseしないか。
72. ticket ID発行後にfallible operation/early returnがなく、global map collision時にoverwriteして続けないか。
73. outstanding child ticket中に`claims_by_upper_record` / `live_states_by_coverage_root`のlast entryをremoveしても、
    parent slotとchild capacityがpinされるか。
74. last ticket release後のpending empty prune、途中reinsert時のflag clear、later recreation reserveが全て
    allocation/error/snapshot contractどおりか。
75. `StructuralPreparationScope`のHRTB/invariant handleがscope外return/queue/field保存をcompile-failにし、scope
    `Drop`がuncommitted arena slotを全件cleanupするか。
76. HRTB query scopeのraw reference escapeとscope中terminal transitionがcompile-failし、scope-entry check後に
    getter/cursor-step checkを追加していないか。scope count/getter count/perf counterがこのcontractを実測するか。
77. pinned empty childがcanonical cursor、support closure、semantic fanoutのreal memberに見えないか。
78. public intentとprivate prepared commandが別型で、external/siblingがprepared command/private tokenを構築できないか。
79. arena take後のpanic/early errorで`InFlightCommitGuard`がticket/domain units/pinをexactly once releaseするか。
80. staged-build phaseのpanicはauthoritative state zero-write、publication phaseのpanic point zeroか。
81. prototypeの`0.42〜0.88 ns/check`をproduction speedupへ直接換算せず、HRTB scope entry一回対旧N getter checksの
    real RMW/std profileを取るか。
82. `ProjectionEvaluationRoundState`を一つ作りtarget A/Bを別scopeで評価するnew fixtureが、BでAのchecked/memo hitを
    実測し、facade/referenceをroundへ保存せずcompileするか。borrowed facade保存probeはcompile-failか。
83. A/B scope間snapshot advance fixtureがold checked/evaluator memoをclearし、terminal latchだけをstickyに保つか。
84. `ScopedProjectionQuery` / `ScopedPublicationProjectionQuery` / `QueryCompletion<R>`をclosure boundに持つ両
    `ConstraintMachine::with_*_query` wrapperが`private_bounds`をdenyしたactual buildでgreenか。prototypeのpublic
    view buildだけで代用せず、publication signatureと全三型のre-exportもcompileしているか。
85. family siblingからtoken-free `PreparedPayload` variantをconstruct/matchするprobeがprivacy errorになり、outer
    `PreparedStructuralCommand` E0451だけで代用していないか。
86. `commit_projection_formula_shadow_delta`、`record_prepared_live_coverage`、
    `commit_projection_index_admission`の各publication planがfirst write後panic point zeroを示すか。
87. `with_projection_query`のactual callが`&TypeArena`を明示的にscopeへreborrowし、round/kernelへ保存しないか。
88. `SchemeProjectableLower` owned conversionがoutput parityを保ち、selected-only clone costをRMW/stdで測ったか。
89. projection round専用K1→K2 fixtureがsame-K1 checked/memo hitを先に実測し、counter reset後のK2で
    `ForeignAttemptRoundState`を返すか。foreign sticky terminalをK1 failureとして返さず、stale hit/K2 read/
    clear/rebind/cache lookup/publicationが全てzeroか。payloadは`expected == Some(K2 nonce)`、
    `actual == Some(K1 nonce)`の向きをassertするか。
90. publication round専用K1→K2 fixtureがsame-K1 memo/override hitを先に実測し、counter reset後のK2で
    `ForeignAttemptRoundState`を返すか。stale memo/override hit、K2 canonical read、clear/rebind、cache
    lookup/publicationが全てzeroか。payloadは`expected == Some(K2 nonce)`、`actual == Some(K1 nonce)`の向きを
    assertするか。bare kernel helperやprojection fixtureだけで代用せず、
    `ConstraintMachine::with_publication_projection_query`を呼んでいるか。
91. both round typesのstandalone construction/`Default`がcompile-failし、`ProofAttemptNonce`のname visibilityと
    `ForeignAttemptRoundState { expected: Option<ProofAttemptNonce>, actual: Option<ProofAttemptNonce> }`が
    `deny(private_interfaces)`でgreenか。nonceのtuple field/mint functionはprivateのままか。
92. projection/publication両wrapperのauthenticated scope constructor failureが`?`でcommon failure branchを
    bypassせず、terminal-required failureをmachine latchへexactly once記録するか。publication production/fixture
    callerが`ConstraintMachine` delegateへ統一されているか。

一項目でも反例、raw escape、proof-token escape、infallible evaluator growth、latch precedence差、
ticket ID alias、container capacity loss、scope cleanup leak、reservation double-booking、partial-sealing cache
authorityがあれば、本書を確定しない。

## 11. 本統合理論の残余gapと完了条件

### 11.1 起案時点で残るgap

本書を起案した時点で、次はmechanically完全には閉じない。

1. **Kernel自身の変更**
   - future developerはgateway/data moduleそのものを編集できる。Rust privacyはrepository ownerを敵対者として
     防がない。compile-time closureは通常call siteに対するもので、kernel API変更は独立review対象である。
2. **Allowlisted comparatorのsemantic drift**
   - command semanticsへnew relevant fieldを追加したのにcomparatorを更新し忘れることは、一般にはcompilerが
     証明しない。proof pathでmutating handlerを呼ばない設計はround 5より強いが、small allowlistのfixture/
     reviewは不可欠である。
3. **Migration completeness before final sealing**
   - SS0〜SS5の途中はhuman censusを使う。compiler closureが成立するのはraw fieldsをstateへ吸収し外部accessを
     消した後である。このため途中cache authorityを禁止する。
4. **Large semantic TCB**
   - gateway APIは小さくてもfamily handlersは大きい。transaction/output correctnessは従来同様tests/reviewに
     依存する。本書がmechanically強化するのはinvalidation finalizationであり、proof system全意味ではない。
5. **External immutable type-shape exception**
   - `TypeArena` append-only premiseが反証された場合、§3.1の例外は成立しない。SS0で必ず決着する。
6. **Current single-thread ordering**
   - true parallel commit/queryではexclusive `&mut ProofAttemptKernel` query scopeとcompleted snapshotのordering proofを
     再設計する必要がある。
7. **Resource-domain planning correctness**
   - closed command/one-shot reserved operationはplan更新漏れを機械的に狭めるが、commandが将来必要とする最大unit数のsemantic
     見積り自体はreview/test対象である。unbounded input-dependent unitはprepareでfallibly数え、ticketへ正確に
     保存しなければならない。
8. **Active capability TCB**
   - `ProofAttemptKernel`、mutation token、HRTB query wrapperがlatch couplingのtrusted control surfaceになる。
     kernel内部でscope-entry checkを外す変更をRust privacyだけでは防げないため、port-level negative fixtureと
     独立査読を要する。
9. **Pinned-container representation cleanup**
   - pinned empty/absentのsemantic parityはtype systemだけでは証明しない。全read cursor/fanoutがempty childを
     skipするfixtureと、pin/prune helperの単一化を要する。
10. **Preparation-scope orchestration cost**
   - existing coordinatorをbounded scopeへ入れるownership rewriteが必要である。scopeをattempt全体へ広げてticket
   cleanupを遅延させず、actual multi-prepare operationごとに閉じる必要がある。
11. **Changed-handler semantic panic discipline**
   - `InFlightCommitGuard`はreservation leakを閉じるがsemantic rollbackを提供しない。build-fully-then-publishの
     panic-free primitive分類はfamilyごとのreview/test対象であり、compilerが全operationのpanic freedomを一般には
     証明しない。
12. **HRTB call-graph migration cost**
   - current trait/read helperがborrowed factを複数layerへ返している場合、query closure内へcall graphを移すかowned
     descriptorへ変換する必要がある。clone増加を隠さずSS6 profileで測る。
13. **Round-state split migration cost**
   - current roundがborrowed preflight/evaluatorを長期所有する形を、owned memo stateとtarget-local facadeへ分ける
     call-graph rewriteが必要である。same-target recursionは一scopeに留め、cross-target sharingはowned IDs/memosだけへ
    限定するfixtureが必要である。
14. **Multi-container primitive audit**
   - closed publication planはpanic pointを狭めるが、concrete `Eq`/`Hash`/hasher/dropとstandard container operationの
     panic-free premiseはcompilerが自動証明しない。SS0 tableとfamily reviewを省略できない。
15. **Prototype privacy evidenceの不足**
   - prototypeはtoken-free `PreparedPayload` sibling constructionとrev.4 narrow closure-bound visibilityを反証して
     いない。rev.5のstronger privacyはproduction compile-fail/UI testsで初めて確定する。
16. **Owned result conversion cost**
   - selected `WeightedLowerBound` cloneと他borrowed-result descriptor化はscope safetyに必要だが、payload容量次第で
     costを持つ。SS6で選択件数/容量/wall/RSSを測り、reference escapeへ戻さず改善する。

これらは統合理論を直ちに否定しないが、隠すと七回目のvacuous guaranteeになる。Claude査読はとくに1〜3を
反証対象にする。

### 11.2 Rollback

- SS1 shellはproduction behaviorを変えず単独revertできる。
- SS2〜SS5はfamily単位でold ownerへ戻せるが、二重authorityを残さない。
- family rollback時はoutstanding ticketをzeroにし、old/new reservation authorityを同時に残さない。
- scope rollback時はprepared arena、global ticket allocator/registry、child pin metadataをまとめて除去し、
  raw caller-owned prepared handleと混在させない。
- SS6 HRTB query-scope/evaluator hardeningはcache readと独立にrevertできる。
- SS7 cache lookup/publicationだけをoffにし、sealed state/snapshotを残せる。
- SS8+は個別prover/proof variantだけを除去しChangedへ戻せる。
- rollback後にpartial cache identity、failure entry、old snapshot authorityを残さない。

### 11.3 完了条件

- Claude (Sonnet 5)の独立査読とユーザ承認が完了している。
- all cache-relevant stateがsealed ownerへ移り、external raw mutation compile-fail gateが成立する。
- public intent/private prepared command split、closed dispatch、single finalizer、default Changed、private proof
  allowlistが成立する。
- `commit_upper_claim_move` early-return counterexampleがchanged/no-op両caseでfixture化される。
- new gateway-level actual claim-first、異domain two-ticket、multi-domain one-ticket、approved compatibility
  interleaving、distinct A/B fixtureがgreen。
- `claims_by_upper_record` / `live_states_by_coverage_root`のpin/remove/recreate fixtureがgreen。
- conflict/cancel/drop/`?`/terminal/scope-exit/teardown後、prepared arenaとall resource domainのoutstanding ticket/pin
  zero at quiescence、commit-time allocation zeroが成立する。
- arena take後panic/early errorで`InFlightCommitGuard` cleanup zero-leak、staged-build failure時authoritative write zero、
  publication phase panic point zeroが成立する。
- evaluator/override insertionがquery/publication両pathでfallibleで、allocator failure fixtureがgreen。
- HRTB query scopeのE0515/E0500/E0501 compile-failとowned-return positive fixture、round/machine terminal latchと
  cache/gatewayのprecedence fixtureがgreen。
- lifetime-free decision/publication round stateが複数top-level target間でsame-snapshot checked/memoを共有し、
  scope-local facade/store/type-shape borrowを保持しないcompiler/runtime fixtureがgreen。
- normal modeのroundがmachine/kernel factoryからcurrent attempt+snapshotへbindされ、projection roundとpublication
  roundの独立したK1→fresh K2 negative fixturesがtyped foreign-attempt rejectionとなる。各fixtureはsame-K1
  hitを先に実測し、K2でstale hit/read/clear/rebind/cache lookup/publication zeroを示す。nonce exhaustion modeでは
  unauthenticated round terminalを読まず、cache/cross-scope reuse zero。
- exact query/round type visibilityが`private_bounds` deny buildでgreen、private fields/constructorsとfully-private
  `PreparedPayload`のnegative probesがgreen。
- formula shadow/live coverage/projection indexを含む全multi-container commandがclosed panic-free publication planを
  持ち、first-write後panic point zero。
- `SchemeProjectableLower`その他scope外resultのborrowed structural field zero、owned-result parity green。
- cache on/off、forced-uncached、cycle/error/full-workload oracle mismatch zero。
- Changed-only SS7がRMW N=6でreal median improvementを示す。
- all `Unchanged` proof variantsがpredicate/fixture/performance resultを持つ。
- failure/projectability/evidence/cycle result cache zero。
- no-claim allocation、saturation、optional allocation fallback、18 GiB RSS gateが成立する。
- RMW N=1..6、cold std、representative corpusのwall/counter/profileを保存する。
- temporary D0 writer mechanism/shadow/migration codeをcloseoutで整理する。

---

著者: Codex gpt-5.6-sol（xhigh）が起案、Claude (Sonnet 5) が独立査読・確定

状態: **確定 rev.9、Claude (Sonnet 5) 独立査読済み、ユーザ承認済み（2026-08-14）**。本書はCPK-SV-D
実装authorityである。
