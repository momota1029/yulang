# CPK-SV-D SS2 read foundation resequencing addendum

日付: 2026-08-14

版: **rev.9（確定）**

状態: **確定 rev.9、Claude (Sonnet 5) 独立査読済み、ユーザ承認済み（2026-08-14）**

著者: Codex gpt-5.6-sol（xhigh）が起案、Claude (Sonnet 5) が独立査読・確定

> **Authority notice**
>
> 本書はドラフトであり、Claude (Sonnet 5) の独立査読とユーザ承認が完了するまで実装authorityとして使っては
> ならない。承認後は、
> `notes/design/2026-08-13-cpk-sv-d-sealed-conservative-cache-plan.md`
> rev.9（以下、親設計）の§7にあるSS1完了後からSS6完了までの**実装順序とslice gateだけ**を本書が補足・
> 置換する。rev.9はこれに加え、親設計invariant 76のexact visibilityを、§2.1.1に列挙する
> projection-side cross-sibling surfaceだけ`pub(crate)`へ狭く修正する。それ以外の親設計§0〜§6、§8
> invariants 37〜78の結果要件、§9 stop conditions、§10 review checklist、SS7以降のcache authorityは
> 変更しない。

rev.2はrev.1への独立adversarial reviewで判明した、partial sealing中のcross-scope reuseがD0 writer censusの
exhaustivenessへ依存するsoundness gapを修正する。SS2〜SS5ではcross-scope checked/memo reuseを機械的に無効化し、
一つのimmutable HRTB scope内だけでtarget間共有を許す。D0 snapshotをround-reuse correctness authorityに使わない。

rev.3はrev.2への独立査読で残った二点を閉じる。第一に、SS6の`Sealed` reuseを五familyのwrite/read cutoverとfinal
sealed read surfaceへ機械的に接続するnon-forgeable witness chainを定義する。第二に、one-scope batchingを抽象的な
gateに留めず、production caller inventory、before/after call graph、RMW/std counter・wall checkpointをSS2本体より
前のmandatory checkpointとして固定する。

rev.4はrev.3の三つのHIGHを閉じる。第一に、family sealをzero-sized attestationではなく、実際のlegacy ownerを
by-valueで消費して`ProofAttemptKernel<Layout>`のownership typestateを進めるtransitionへ置き換える。第二に、SS2-P0が実行時に
使うall-legacy HRTB read routeを定義する。第三に、current production codeから再確認した六つのround ownerを
before/after call graph付きでSS2-P0の正本に固定する。

rev.5はrev.4が過大に主張した保証強度を明示的に下げる。ownership typestateは、named familyの実valueを
consumeせずにcareless callerが`Sealed`を有効化する誤りを防ぐ**structural best-effort guard**として維持する。
しかし、`Legacy*Owner`からのfield脱落、aggregate外に残った新規mandatory input、HRTB closureがcaptureするexternal factの
不在までRustのtype systemがexhaustiveに証明するとは主張しない。この不在性は、CPK-SV-D0と同じく、SS5→SS6の
明示的な人手census・独立review・fault-injectionを含むexhaustive test gateで判定する。これは強いproofを
復元するbug fixではなく、従来のmechanical-exhaustiveness目標を意図的にde-scopeしたものである。
同時に、post-check formatting/generalizationが実際に`&mut ConstraintMachine`へ到達するcaller signature cascadeを固定し、
`scheme_projection_record_is_included`を七番目のproduction round ownerとして追加し、sealed round snapshotを
witnessがborrowするgateway authorityから導出する。

rev.6はrev.5のP0 caller rewriteに残っていた一つのsignature/scope cascadeを閉じる。
`capture_generalized_witnesses`とscheme-mode input-type compactionも内部で
`scheme_projectable_lowers`を使うため、これらをrow 1の派生callerとして明示的にP0へ含める。
七round-owner rowは変更せず、各top-level witness/compaction entryを一回のbounded HRTB invocationで包む。

rev.7はcaller inventoryの残る二つのmechanical gapを閉じる。row 7へclause-link mutation直前・直後の
`scheme_projection_record_is_included` callを追加し、pre-mutation scopeをwrite前に必ず閉じ、post-mutation scopeを
publication evaluation全体の外側で一回だけ開く。またP0ではborrowed `SchemeProjectableLower<'query>`をscope-localに
留め、owned conversionは従来どおりSS2へ残す。P0から逃がすのはwitness draftや`CompactRoot`など上位のowned outputだけである。

rev.8はSlice Cの実装contactで判明したexact visibility gapを閉じる。rev.7は
`generalize/mod.rs`と`check.rs`をprojection queryのproduction callerとして列挙したが、これらは
`constraints`のdescendantではなくsiblingである。従ってprojection-sideのmachine entrypoint、その
signatureに現れるround/scope/completion type、および必要なsafe scope methodだけを`pub(crate)`へ広げる。
publication-side、raw source/view/storage、field、constructor、candidate internalsは広げない。

rev.9はrev.8のcross-sibling safe surfaceに不足していたtype-shape queryを追加する。row 2は
projectable lowerのweightを検査した後、その`PosId`が`TypeVar`かを解決する。scope内で
`ConstraintMachine::types()`を再borrowせず同じ条件付き順序を保つため、legacy/final projection facadeへ
`pos_var_in_scope(PosId) -> Option<TypeVar>`だけを追加する。general view、type arena、raw type-shape referenceは
公開しない。

## 0. 決定の要約

親設計の実装順序を、次のように変更する。

```text
旧:
SS1 sealed shadow shell
  -> SS2 proof write authority
  -> SS3 bounds
  -> SS4 constraints/replay
  -> SS5 rows/identities + seal completion
  -> SS6 HRTB read scope / owned round / evaluator hardening

新:
SS1 sealed shadow shell（完了済み）
  -> SS1-RF HRTB read foundation shadow（新設）
  -> SS2 proof write authority + production proof-read HRTB cutover
       （cross-scope reuse off。sharingはone immutable scope内だけ）
  -> SS3 bounds write/read source cutover
  -> SS4 constraints/replay write/read source cutover
  -> SS5 rows/identities write/read source cutover + seal completion
  -> SS6 sealed-snapshot cross-scope reuse + evaluator/cache-shadow closeout（縮小）
```

新設する`CPK-SV-D-SS1-RF`は、親設計§3.1.1、§3.7.1、旧SS6に定義済みのHRTB exclusive-query-scope、
lifetime-free round state、exact visibility、attempt bindingを、production proof authorityへ触れないshadow foundation
として先に実装する。

SS2はこのfoundationを前提に、`ProofOccurrenceStore`から`StructuralData::proof` / `ProofRelations`へのwrite authority
cutoverと同じsliceで、proof-family mandatory readもHRTB scopeへ切り替える。従ってSS2〜SS5の間にpersistentな
`InterimProofRelationsView<'a>`、raw `&ProofRelations`、`SemanticFactView for ConstraintMachine`をproduction read
authorityとして新設しない。

ただし、SS2〜SS5ではlifetime-free round objectをcross-scope success-reuse authorityにしない。各
`with_projection_query` / `with_publication_projection_query` invocationはfresh ephemeral checked/memo/evaluator stateを
持つ。複数targetがchecked/memoを共有する必要がある場合は、同じexclusive immutable HRTB scope内でまとめて評価する。
scope終了後にsuccess-derived checked/memo/override/cycle stateを次scopeへ持ち越さない。全writer sealingをSS5 gateで
確認した後、SS6が§6.1のstructural guardと§6.2のhuman census/test/reviewの両gateを完了し、gateway
completed snapshotへbindするcross-scope reuseを再有効化する。

採る形は**2b: round control objectはthreadするが、SS2〜SS5のsuccess-reuse payloadはinert/absent**である。2aの
「round object全体を毎target作り直す」はround terminal first-failureとattempt authenticationまで分断し、親設計のexact
machine delegate signatureを不要に揺らす。2bならterminal/attempt controlを保持したまま、危険なchecked/memo reuseだけを
private enumで構造的に不可能にできる。

この順序変更は、親設計が最終形として既に定めたread architectureを前倒しする。cache authority、
`Unchanged` proof、domain/token architectureは変更しない。一方、rev.4の「SS5完了のtypeだけでlegacy authorityの不在を
機械的にexhaustive証明する」というclaimは撤回する。SS6のactivation authorityは、typestateだけではなく、
そのbest-effort guardと、本書で新たに明文化する人手census/test/review gateの両方を必要とする。

## 1. 背景と解決するgap

親設計の旧SS2はproof relationのwrite authorityをsealed stateへ移し、旧SS6はproduction preflight/evaluatorを
HRTB sealed query scopeへ移す。しかし旧SS2〜SS5の間に、現行の
`ProjectionPreflight<'a>` / `CpkProjectionEvaluator<'a>`等がsealed proof authorityを読むための合法なtemporary
surfaceが定義されていない。

次のtemporary surfaceは採れない。

- persistent `InterimProofRelationsView<'a>`をroundへ保存する。
- `ProofStructuralState`からraw `&ProofRelations`を返す。
- terminal check時にmintしたviewを後続operationへ持ち回る。
- current `ConstraintMachine` / arbitrary trait implementerをsealed proof read authorityにする。

これらは親設計§3.1.1のpersistent read-view禁止、invariant 38、67、73、75、§9.3のraw-reference escape stop
conditionに反する。そこでtemporary facadeを設計せず、最終HRTB boundary自体をwrite cutoverより先に作る。

現行borrowed `ProjectionEvaluationRound<'a>`のcross-target sharingは、同じimmutable store borrowが生きる間に限られ、
その間のintervening mutationをlifetimeが排除する。rev.2はこの安全条件を、複数targetを一つのexclusive immutable
HRTB scopeへbatchすることで保存する。separate scopeは別immutable borrowであり、SS2〜SS5では必ずfresh stateから始める。

## 2. 親設計SS6から前倒しするread foundation

### 2.1 Exact restricted surface

SS1-RFではSS1ですでに`crates/infer/src/constraints/structural_kernel/mod.rs`と`access.rs`へ入った
round/scope shellを、本節のexact lifetime・visibility・reuse-mode contractで**拡張・置換**する。
同名の二重shellは作らない。rev.9以降のexact visibilityは次の二帯で固定する。

| Surface | Exact visibility | Reason |
|---|---|---|
| `ProjectionEvaluationRoundState` | `pub(crate)` | `generalize` / `check` / `compact`が`constraints`のsiblingからprojection roundをthreadする |
| `ScopedProjectionQuery<'query>` | `pub(crate)` | final sealed projection closureのparameterとしてcross-sibling signatureに現れる |
| `QueryCompletion<R>` | `pub(crate)` | projection closure boundのreturnに現れるshared opaque completion typeである |
| `CpkPublicationEvaluationRoundState` | `pub(in crate::constraints)` | publication callerはcurrent inventory上`constraints` subtree内だけである |
| `ScopedPublicationProjectionQuery<'query>` | `pub(in crate::constraints)` | 同上 |
| `ScopedQueryView<'query>` | `pub(in crate::constraints)` by default | cross-sibling callerには`ScopedProjectionQuery`上の目的別safe methodを出し、raw/general view型は広げない |
| `ProofAccessError::ForeignAttemptRoundState` | `pub(in crate::constraints)` | access/kernel internal contractの現行範囲を維持する |

`ScopedProjectionQuery::complete`、`ScopedProjectionQuery::pos_var_in_scope`とcross-sibling production callerが
実際に使う列挙済みの目的別safe projection getter/helperは`pub(crate)`とする。
`ScopedProjectionQuery::view()`をcross-sibling surfaceにしてはならない。将来それが必要に
なった場合は、`ScopedQueryView<'query>`と対象safe getterも`pub(crate)`でなければ
`deny(private_bounds, private_interfaces)`を満たせないため、本列挙の自動拡張ではなく再査読対象とする。

`structural_kernel/mod.rs`は対象型のre-export bindingだけを`pub(crate)`に分離する。
`constraints/mod.rs`は`structural_kernel`自体を`pub(crate)`にせず、cross-sibling signatureに必要な
`ProjectionEvaluationRoundState`、`ScopedProjectionQuery`、`QueryCompletion`だけを
`pub(crate) use structural_kernel::{...}`で再exportする。field、constructor、cache candidate、raw storageはそれぞれの
owner module privateのままとする。

`ProjectionEvaluationRoundState` / `CpkPublicationEvaluationRoundState`は、final SS6 APIとpartial-sealing safetyを同じ型で
表すためprivate reuse modeを持つ。

`Sealed` variantを`access.rs`が直接constructできないよう、inner enumは`access/sealing.rs` module完全privateにする。
`access.rs`へ見せるのはprivate-field opaque slotとwitness必須methodだけである。

```rust
// access/sealing.rs
enum RoundReuseState<T> {
    SealingIncomplete,
    Sealed {
        snapshot: ProofStructuralSnapshotId,
        reusable: T,
    },
}

pub(super) struct RoundReuseSlot<T>(RoundReuseState<T>);

impl<T> RoundReuseSlot<T> {
    pub(super) fn sealing_incomplete() -> Self {
        Self(RoundReuseState::SealingIncomplete)
    }

    // Sealed inner variantを作る唯一のfunction。witnessをby-value consumeする。
    pub(super) fn sealed(
        witness: AllFamiliesSealedWitness<'_>,
        reusable: T,
    ) -> Self {
        // raw snapshotは受け取らない。witnessがborrowするfully-sealed authorityからだけ得る。
        let binding = witness.into_round_binding();
        Self(RoundReuseState::Sealed {
            snapshot: binding.snapshot,
            reusable,
        })
    }
}

// access.rs。RoundReuseState自体をname/match/constructできない。
pub(crate) struct ProjectionEvaluationRoundState {
    attempt: Option<ProofAttemptNonce>,
    terminal_failure: Option<ProofFailure>,
    reuse: sealing::RoundReuseSlot<ProjectionReusableRoundState>,
}

pub(in crate::constraints) struct CpkPublicationEvaluationRoundState {
    attempt: Option<ProofAttemptNonce>,
    reuse: sealing::RoundReuseSlot<PublicationReusableRoundState>,
}
```

`RoundReuseSlot` field、mode constructor、`Sealed` activationは`access.rs`の外へ出さない。SS1-RF〜SS5の
machine/kernel factoryは必ず`sealing_incomplete()`を使い、arbitrary caller/test helperは`Sealed`を構築できない。
SS6のwitness chainは§6.1で定義する。このchainはcareless premature activationを防ぐbest-effort guardであり、
legacy authorityが他に残っていないことのexhaustive proofではない。その不在性は§6.2の人手gateが判定する。
`SealingIncomplete`には
record/constraint checked set、evaluator `Done` memo、record/root override result、cycle-sharing success stateを保存する
場所がない。wrapperはinvocationごとにfresh `ProjectionPreflightRoundState` /
`CpkProjectionEvaluationRoundState` / publication override stateをlocal stack valueとして作り、scope drop時に破棄する。

`ProjectionEvaluationRoundState`がSS2〜SS5でscopeを跨いで保持できるのはattempt identityとround terminal failureだけで
ある。`CpkPublicationEvaluationRoundState`が保持できるのはattempt identityだけである。SS6の`Sealed` modeで初めて、
record/constraint visiting/checked set、acyclic evaluator memo、cycle-sharing state、record/root override等のowned
ID/valueをcross-scope reuseできる。どのmodeでも`ProofStructuralState`、`StructuralData`、`ProofOccurrenceStore`、
`ConstraintMachine`、`TypeArena`、`ScopedQueryView`へのborrowをfieldへ持たない。

publicationのrecord/root override入力を複数targetが共有する場合も、SS2〜SS5では同じpublication query closure内へ
batchし、そのinvocationのephemeral stateとして構築する。scope由来のoverride/evaluator resultをouter roundへ書き戻さず、
次invocationはcaller inputからfreshに構築する。

scope-local objectは次で固定する。

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

これらはquery invocationごとにfreshに作り、round stateへ保存しない。一つのinvocationは複数top-level targetを
順に評価してよく、そのscope内だけはfacadeのchecked/memo stateを共有できる。recursive `validate_record` /
`validate_constraint`、CPK-SV-C late-bound claim/live read、record/root recursionも同じfacade内で直接再帰し、nested
query scopeを作らない。scope間の共有はSS6の`Sealed` modeまで禁止する。

#### 2.1.1 Projection callerのcross-sibling visibility例外

rev.7のexact surfaceはproduction callerがすべて`constraints` subtree内にいると暗黙に仮定していた。しかし
§4.0.1.1と§4.0.2 row 1/2が列挙する`generalize/mod.rs`、`generalize/provenance.rs`、`compact/collect`、
`check.rs`は`constraints`のdescendantではなくcrate siblingである。`pub(in crate::constraints)`の
`ConstraintMachine::with_legacy_projection_query`はこれらから呼べず、entrypointだけを`pub(crate)`に
しても、closure bound内のscope/completion typeとround argumentがより狭いため
`deny(private_bounds, private_interfaces)`でcompileしない。

従って次のprojection-side列挙だけをcross-sibling surfaceとする。

- `ConstraintMachine::new_projection_evaluation_round`: `pub(crate)`
- `ConstraintMachine::with_legacy_projection_query`: `pub(crate)`
- `ProjectionEvaluationRoundState`: `pub(crate)`
- `ScopedLegacyProjectionQuery<'query>`: `pub(crate)`
- `QueryCompletion<R>`: `pub(crate)`
- `ScopedLegacyProjectionQuery::complete`: `pub(crate)`
- `ScopedLegacyProjectionQuery::scheme_projectable_lowers_in_scope`: `pub(crate)`
- `ScopedLegacyProjectionQuery::pos_var_in_scope(PosId) -> Option<TypeVar>`: `pub(crate)`
- final sealed cutoverの`ConstraintMachine::with_projection_query`、`ScopedProjectionQuery<'query>`、
  `ScopedProjectionQuery::complete`、
  `ScopedProjectionQuery::pos_var_in_scope(PosId) -> Option<TypeVar>`、および本節に列挙する実caller用の
  目的別safe projection getter/helper: `pub(crate)`

`structural_kernel/mod.rs`は上の型のre-export bindingだけを`pub(crate)`に分離し、
`constraints/mod.rs`はその型だけを`pub(crate) use structural_kernel::{...}`で到達可能にする。
`structural_kernel`自体、`LegacyOnlyReadSources`、`LegacyOnlyQueryView`、`RoundReuseState`、
`ProofAttemptKernel`、scope/round/completionのfield・constructor・candidate internals、raw storageは広げない。

publication-sideのround/scope/delegateはcurrent caller inventoryが`constraints` subtree内で閉じているため、
`pub(in crate::constraints)`のままとする。将来cross-sibling publication callerが見つかった場合だけ、
そのcallerとsignature surfaceを別の査読対象とする。

この例外はinvariant 66のraw storage/write authority privacyを弱めない。nameableになるのは
HRTBでlifetime-boundされたopaque safe facadeとmachine-minted round/completionの型名・必要safe methodだけである。
constructor、field、raw getter/mutator、capability、cache/publication portはprivateのままである。invariant 76の
「wrapperとsignature typeを同じeffective visibilityにし、constructorを閉じる」結果要件を、
cross-sibling projection callerの実breadthに合わせて正確化するものである。

`pos_var_in_scope`はraw `Pos`、`TypeArena`、`ImmutableTypeShapeView`へのreferenceを返さない。実装はscope内の
type-shape authorityに対する`PosId` lookupを行い、`Pos::Var(var)`だけをowned `TypeVar`として返す。
row 2は現行どおりweightがalias-neutralと判定されたlowerに対してだけこのmethodを呼ぶ。従って全lowerを
eagerにresolveするresult-shape変更を避け、lookup順序、skip条件、allocation特性を変えない。

### 2.2 Exact machine entrypoints

production caller breadthへ見せるsignatureのerror/lifetime/constructor contractは親設計rev.9から変更しない。
visibilityだけは§2.1.1のcross-sibling projection例外を適用する。

```rust
impl ConstraintMachine {
    pub(crate) fn new_projection_evaluation_round(
        &self,
    ) -> ProjectionEvaluationRoundState;

    pub(crate) fn with_projection_query<R>(
        &mut self,
        round: &mut ProjectionEvaluationRoundState,
        query: impl for<'query> FnOnce(
            ScopedProjectionQuery<'query>,
        ) -> Result<QueryCompletion<R>, ProofFailure>,
    ) -> Result<R, ProofFailure>;

    pub(in crate::constraints) fn new_publication_evaluation_round(
        &self,
    ) -> CpkPublicationEvaluationRoundState;

    pub(in crate::constraints) fn with_publication_projection_query<R>(
        &mut self,
        round: &mut CpkPublicationEvaluationRoundState,
        query: impl for<'query> FnOnce(
            ScopedPublicationProjectionQuery<'query>,
        ) -> Result<QueryCompletion<R>, ProofFailure>,
    ) -> Result<R, ProofFailure>;
}

impl<'query> ScopedProjectionQuery<'query> {
    pub(crate) fn pos_var_in_scope(&self, pos: PosId) -> Option<TypeVar>;
}
```

両delegateは`&self.types`と`&mut self.proof_attempt`をfield split-borrowし、kernel wrapperへexact `&TypeArena`を
渡す。kernel wrapperはscope内でのみ`ImmutableTypeShapeView::new(type_shapes)`を作り、kernel/roundへ保存しない。
bare kernel wrapperはmachine delegateのprivate implementation detailとし、production callerへ別entrypointを
作らない。

kernel wrapperのorderingも親設計どおりとする。

1. current kernel terminal latchを確認する。
2. roundの`ProofAttemptNonce` bindingを認証する。
3. nonce match後だけround-local terminal latchを確認する。publication roundではこのstepはno-opである。
4. `SealingIncomplete`ならsnapshotを照合せずfresh ephemeral checked/memo/override stateを作る。`Sealed`ならgateway
   completed snapshotへbind/rebindしてowned reusable stateへ到達する。
5. HRTB scopeを構築し、一つ以上のtop-level targetを同じscope内で評価する。
6. scope drop後、success candidate publication前にkernel/roundを再確認する。

scope constructionまたはquery closureのauthenticated `ProofFailure`はcommon `result`へ畳み込み、共通failure branch
を通す。constructor内の`?`で`mark_terminal_once`を迂回しない。foreign roundは
`ForeignAttemptRoundState { expected: K2, actual: K1 }`として、round terminal/memo/cacheを読む前にrejectする。
SS2〜SS5でもattempt authenticationは維持するが、`ProofStructuralSnapshotId`をcross-scope reuse判定へ使わない。

### 2.3 SS1-RFでまだ行わないこと

SS1-RFはread **foundation**でありread authority cutoverではない。

- `StructuralData::proof`へreal `ProofOccurrenceStore` payloadを移さない。
- current `ProjectionPreflight<'a>` / `CpkProjectionEvaluator<'a>` production callerを切り替えない。
- current `SemanticFactView for ConstraintMachine`をproduction pathから外さない。
- `SchemeProjectableLower<'a>`を変更しない。
- cache hitでvalidationをskipしない。cache candidate lookup/publicationはinert shadowとする。
- evaluator `try_enter`、publication-time `Result` propagation、fallible override insertionをまだcut overしない。
- proof/bounds/constraint/row/identity write authorityを変更しない。
- `RoundReuseSlot::sealed`をproduction factoryから呼ばず、cross-scope checked/memo reuseを有効化しない。

SS1のplaceholder `StructuralData` / `ProofRelations`またはcfg(test)のminimal shadow factsだけで、scope lifetime、
visibility、attempt binding、one-scope内のephemeral sharingを検証する。shadow queryの結果をproduction semantic outputへ
使わない。

## 3. 新設slice: CPK-SV-D-SS1-RF

### 3.1 Scope and authority

**Authority:** current production storage/read/write。cache readなし。SS1 sealed shellはshadowのまま。

実装内容:

- §2.1のlifetime-free round stateとscope-local facadeについて、existing SS1 shellのplaceholder field/implを置換・拡張する。
- machine/kernel factoryだけがround stateをcurrent
  `ProofAttemptNonce`へbindし、private `RoundReuseSlot::sealing_incomplete()`で生成する。standalone `new` / `Default` /
  field constructionを公開しない。snapshot-bound `Sealed` constructionはSS6までproductionへ置かない。
- §2.2の両machine delegate、kernel wrapper、scope type、opaque `QueryCompletion<R>`を追加する。
- `ScopedQueryView<'query>`はSS1 shadow `StructuralData`とexplicit `ImmutableTypeShapeView<'query>`だけをborrowし、
  mutation/cache-publication/terminal setterを持たない。
- one-scope内ephemeral sharing、scopeを跨ぐalways-miss、foreign-attempt rejection、nonce exhaustion時reuse-disabled
  ephemeral executionをshadow fixtureで固定する。
- `#![deny(private_bounds, private_interfaces)]`相当のreal UI/build gateを両delegate signatureへ適用する。
- raw reference/cursor escape、same-kernel terminal transition、facade/viewのround field保存をcompile-failで固定する。

### 3.2 Gate

- projection-sideの`ProjectionEvaluationRoundState` / `ScopedProjectionQuery` / `QueryCompletion<R>`はexactly
  `pub(crate)`で`constraints` rootからre-exportされ、publication-side round/scopeはexactly
  `pub(in crate::constraints)`のままである。fields/constructors/candidate internalsはprivateである。
- legacy/final projection facadeの`pos_var_in_scope(PosId) -> Option<TypeVar>`がexactly `pub(crate)`で、
  raw `Pos` / view / type-shape referenceを返さず、row 2 closureが`ConstraintMachine::types()`を再borrowしない。
- 両`ConstraintMachine::with_*_query` signatureが`deny(private_bounds, private_interfaces)`でgreenである。
- query scopeからraw `&T` / cursor / viewを返すprobeがE0515相当、scope内からsame kernel terminal/mutation methodを
  呼ぶprobeがE0500/E0501相当でcompile-failし、owned value returnはgreenである。
- one HRTB scope内でshadow target A→target Bを評価し、BがAのchecked/memoをhitする。同じowned round objectを使って
  scopeを終了し、fresh scopeでtarget Bを再評価するvariantは、numeric D0 snapshotが同じでもchecked/memo hit zero、
  canonical shadow read nonzeroである。
- `SealingIncomplete` modeのround objectにsuccess-derived checked/memo/override/cycle payloadが保存されず、scope drop後の
  reusable entry countが構造的にzeroである。
- projection/publicationそれぞれのK1→K2 fixtureが`ForeignAttemptRoundState`を返し、payload orientation、stale memo/
  override hit zero、clear/rebind/cache lookup/publication zeroを確認する。
- authenticated scope-construction failureがcommon failure branchへ入り、terminal mark orderingが親設計と一致する。
- scope-entry check count exactly scope count、getter/cursorごとの`RefCell`/`Cell` capability check zeroである。
- round-persistent fieldにstore/view/machine/type-arena borrow zeroである。
- production validation output/read/write call graphとcache authorityはSS1 baselineから不変である。

### 3.3 Stop condition

次のいずれかが起きた場合、SS2へ進まず本addendumを再査読する。

- recursive validationまたはCPK-SV-C late-bound traversalにnested/re-entrant query scopeが必要になる。
- current productionが一roundで共有するtarget集合をone HRTB invocationへbatchできず、SS2〜SS5でcross-scope
  checked/memo reuseを correctness requirementとして残す必要がある。
- `SealingIncomplete` modeでもsuccess-derived checked/memo/override/cycle payloadをpersistent roundへ保存できるescapeが
  残る。
- raw reference/cursorをscope外へ返さないとexisting semantic resultを表せず、owned result planでも閉じない。
- §2.1.1の列挙外でexact restricted visibilityが`pub(crate)`、public field/constructor、private-bound lint回避を
  要求する。
- production pathを切り替えないままshadow APIを置くこと自体がexisting terminal-latch semanticsを変える。
- `TypeArena` append-only premiseがSS0結果と矛盾する。

RollbackはSS1-RFがextend/replaceしたfield/impl/delegate/testsだけを戻し、SS1の既存shell shapeとproduction
behaviorへ復帰できることを要求する。同名typeを二重に追加してrollbackする設計は認めない。

## 4. 改訂slice: CPK-SV-D-SS2

### 4.0 Mandatory entry checkpoint: production caller / batch closure

SS2のproof-family storage/write migrationへ入る前に、`CPK-SV-D-SS2-P0`として独立commit・独立review checkpointを
置く。P0のauthorityはcurrent legacy production storageのままであり、SS1-RFでcompiler-verifiedにしたHRTB
wrapper/lifetime machineryを§4.0.1のlegacy-only routeで使い、caller boundaryだけを移す。P0がgateを満たすまで
`ProofOccurrenceStore` payload移動、proof write authority cutover、legacy proof field削除を開始しない。

#### 4.0.1 P0 all-legacy scope-private read route

SS1-RFのfinal-shape shadow `ScopedQueryView` はproduction factsを持たないため、P0はそれをsemantic authorityに使わない。
P0専用に、実際のlegacy ownerを一つのHRTB scope内だけ借用するall-legacy routeを作る。

```rust
// access/read_view内部だけ。re-export・runtime fallback・round保存はしない。
struct LegacyOnlyReadSources<'query> {
    proof: &'query ProofOccurrenceStore,
    bounds: &'query TypeBounds,
    constraints_replay: LegacyConstraintReplayReadSources<'query>,
    rows: LegacyRowReadSources<'query>,
    identities: LegacyIdentityReadSources<'query>,
}

// projection型名だけcrate sibling callerへ見せ、field/constructor/getter backendはprivateにする。
pub(crate) struct ScopedLegacyProjectionQuery<'query> {
    view: LegacyOnlyQueryView<'query>,
    // projection用scope-local ephemeral state
}

pub(in crate::constraints) struct ScopedLegacyPublicationQuery<'query> {
    view: LegacyOnlyQueryView<'query>,
    // publication用scope-local ephemeral state
}

impl<'query> ScopedLegacyProjectionQuery<'query> {
    pub(crate) fn pos_var_in_scope(&self, pos: PosId) -> Option<TypeVar>;
}

impl ConstraintMachine {
    pub(crate) fn with_legacy_projection_query<R>(
        &mut self,
        round: &mut ProjectionEvaluationRoundState,
        query: impl for<'query> FnOnce(
            ScopedLegacyProjectionQuery<'query>,
        ) -> Result<QueryCompletion<R>, ProofFailure>,
    ) -> Result<R, ProofFailure>;

    pub(in crate::constraints) fn with_legacy_publication_query<R>(
        &mut self,
        round: &mut CpkPublicationEvaluationRoundState,
        query: impl for<'query> FnOnce(
            ScopedLegacyPublicationQuery<'query>,
        ) -> Result<QueryCompletion<R>, ProofFailure>,
    ) -> Result<R, ProofFailure>;
}
```

P0 projection closureがcompletion、scope-local lower fold、条件付き`PosId`→`TypeVar`解決を表現できるよう、
`ScopedLegacyProjectionQuery::complete`、`scheme_projectable_lowers_in_scope`、
`pos_var_in_scope`だけを`pub(crate)`とする。
`ProjectionEvaluationRoundState`、`ScopedLegacyProjectionQuery`、`QueryCompletion`は`constraints/mod.rs`から
`pub(crate) use structural_kernel::{...}`でre-exportする。`LegacyOnlyReadSources`と`LegacyOnlyQueryView`は
re-exportせず、scope型のfield/constructorもprivateのままとする。publication-sideの
`ScopedLegacyPublicationQuery`、`with_legacy_publication_query`、safe methodは`pub(in crate::constraints)`を維持する。

delegateは`&mut self.proof_attempt`、`&self.types`、そして実際のlegacy family field群をfield split-borrowする。
closureに`&ConstraintMachine`を再渡しせず、現行preflight/evaluatorが必須とする読み取りを
`LegacyOnlyQueryView<'query>`のprivate semantic getter/cursorへ移す。これによりexclusive `&mut ConstraintMachine`
borrowとold `&ConstraintMachine` evaluation pathの二重borrowを作らず、同じlegacy valueをauthorityのまま読める。

P0はこのlegacy-only wrapperへproduction caller boundaryを移す**caller-side refactor**であり、storage owner、writer、read
authorityは100% legacyのままである。`LegacyOnlyReadSources`はread-only、scope-private、non-escapingで、
snapshot/cache/reuse keyを持たない。P0内のsharingは一回のclosureに作るephemeral stateだけである。

##### 4.0.1.1 `&ConstraintMachine` generalization callerの実ownership route

P0は「generalization callerが将来`&mut ConstraintMachine`を得る」と仮定しない。2026-08-14 HEADの実call
chainでは、`generalize_type_var_with_boundaries` (`generalize/mod.rs:73`) と
`expand_positive_aliases_in_scheme_compact` (`:281`) は`&ConstraintMachine`を受け取る。post-check formattingでは
`format_inferred_value_type_with_path_rewriter` (`check.rs:139`) が`&BodyLowering`からshared machineを取り、
`SourceTextAnalysis::hover(&self)` (`yulang/src/source/mod.rs:1683`) と`source_hover_from_check`
(`:3152`) は`&PolyCheckOutput`だけを渡す。`HoverFormatContext`も現在はcheck全体をshared borrowする。

row 1のsignature cascadeはこれらのdirect callerだけでは閉じない。`capture_generalized_witnesses`
(`generalize/provenance.rs:21`) は`&ConstraintMachine`を保持する`WitnessCollector`を作り、そのrecursive traversalから
`scheme_projectable_lowers`を呼ぶ (`:212`)。production callerはlocal loweringのgeneralization直後
(`lowering/expr/tail.rs:993`) と`AnalysisSession::quantify_component`のwitness phase
(`analysis/session/instantiate.rs:59`) の二つである。また
`format_inferred_input_type_with_path_rewriter` / `_public_with_path_rewriter`
(`check.rs:432,444`) は`compact_negative_type_var_for_scheme`へ入り、scheme-mode
`CompactCollector::compact_lower_bounds`が`scheme_projectable_lowers`を呼ぶ
(`compact/collect/mod.rs:655-660`)。このformat routeのproduction entryはlocal input completion
(`yulang/src/source/mod.rs:3280`) とlocal-definition hover (`:3990`) で、いずれも
`HoverFormatContext::format_input_type` (`:4131`) を経由する。これらは独立round ownerではないが、row 1の
scope/signature rewriteから省けない派生callerである。

ただし、このrouteのownerはshared global cacheではない。実のexclusive ownership chainは次である。

```text
fresh request / source API
  -> owned `SourceTextAnalysis`
     -> owned `PolyCheckOutput`
        -> owned `BodyLowering`
           -> owned `AnalysisSession`
              -> `InferArena::constraints_mut()`
                 -> `&mut ConstraintMachine`
```

`hover_from_loaded_files` (`yulang/src/source/mod.rs:2942`) は`check_loaded_files`の戻り値をlocalに所有し、
LSPの`hover_draft_for_source` (`yulang/src/server.rs:501`) も`source_analysis_for_source` (`:283`)の戻り値を
localに所有する。従ってP0は次のsignature cascadeを**mandatory caller rewrite**とする。

1. fresh-check routeは`let mut check` / `let mut analysis`を所有し、
   `source_hover_from_check(&mut PolyCheckOutput, ...)`、`SourceTextAnalysis::hover(&mut self, ...)`、
   `hover_for_analysis(..., &mut SourceTextAnalysis, ...)`へ引き上げる。member-completionの
   `source_member_completion_from_check` (`source/mod.rs:3310`付近)とそのfresh-check entryも同じくmutable ownerを渡す。
2. `format_inferred_value_type*_with_path_rewriter`と
   `inferred_member_receiver_public_with_path_rewriter` (`check.rs:139-196`)のprojection-generalization routeは
   `&mut BodyLowering`または、そのdisjoint fieldをsplitした`&mut ConstraintMachine` + immutable formatting inputsを受け取る。
3. lowering中のlocal-scheme route (`lowering/expr/tail.rs:986-1000`)は既にmutable lowering/session owner内にある。
   generalization用scopeが終わった直後、`capture_generalized_witnesses`をold immutable machine callへ戻さず、
   `constraints_mut()`からwitness-capture専用の`with_legacy_projection_query`へ**一回だけ再entry**する。
   `capture_generalized_witnesses_in_query`相当は`WitnessCollector`のroot/recursive traversal全体へscope-local facadeを
   threadし、owned `(Vec<GeneralizedWitnessDraft>, ProvenanceCompleteness)`を返す。そのscopeをdropしてから
   `finalize_generalized_compact_root`とscheme publicationへ進む。`AnalysisSession::quantify_component`
   (`analysis/session/instantiate.rs:45-72`)の第二loopも、各top-level witness captureについて同じ一回のbounded scopeを
   開き、owned draft/completenessを受け取ってからancestor adjustment/finalizeへ進む。
4. input-type formattingは`format_inferred_input_type*_with_path_rewriter` (`check.rs:432-452`)へ
   `&mut BodyLowering`またはsplitした`&mut ConstraintMachine`を渡す。各top-level format entryは
   `compact_negative_type_var_for_scheme`の**全scheme-mode collector traversal**を一回の
   `with_legacy_projection_query`で包み、`CompactCollector`にはmachineではなくscope-local facadeを渡す。
   closureはowned `CompactRoot`を返し、scope drop後にcloned `TypeArena`へのfinalizeとformatを行う。
   local input completion (`source/mod.rs:3280`)とlocal-definition hover (`:3990`)はこの同じentryを使い、
   collector inner varごとの再entryやpersistent read facadeを作らない。
5. `HoverFormatContext` / completion helperは`&PolyCheckOutput`全体を長生lifetimeで保持しない。candidateの
   `DefId` / `TypeVar` / label / documentation / schemeとpath-rewrite入力を先にowned化するか、
   `BodyLowering::{modules, labels, typing, session.poly, session.infer}`のdisjoint field borrowへ分解する。
   HRTB closureが受け取るのは`&mut ConstraintMachine`とscopeから必要なものだけで、scope外へはowned
   `PublicTypeDisplay` / `InferredMemberReceiver` / hover payloadを返す。

これは`constraints/`内だけの局所signature変更ではなく、`infer/check.rs`、
`yulang/source/mod.rs`、`yulang/server.rs`まで及ぶP0のscope拡大である。P0実装タスクがこれらのfileを
write scopeに含めない場合、caller rewriteは不可能なのでSS2本体へ進まずscope拡大を再承認する。
P0 gateはhover、member completion、lowering中local generalization、両production witness-capture caller、input-type
formattingのcompletion/hover entryがコンパイルし、現行outputとbyte/semantic parityを保つことを必須とする。
generalizationからwitness captureへの境界は二つの連続するbounded invocationでもよいが、witness traversal中にscopeを
閉じたり、scope外の`&ConstraintMachine`へfallbackしたりしてはならない。input compactionも一top-level formatにつき
一bounded invocationで完結する。

SS2のproof cutoverは次を一つのreviewable seriesで行う。

1. `ProofOccurrenceStore`の実valueをsealed proof ownerへmoveする。
2. callerを`with_legacy_*`から§2.2の`with_projection_query` /
   `with_publication_projection_query`へ移す。
3. private routeから`proof: &ProofOccurrenceStore`を削除し、§4.2のproof-sealed
   `PartialSealingReadSources`へ型とconstructorを置換する。
4. `ScopedLegacyProjectionQuery`、`ScopedLegacyPublicationQuery`、`with_legacy_*`、
   `LegacyOnlyReadSources`のproduction referenceをzeroにして削除する。

SS2 gateはこの四型/二delegateのname/reference zero、legacy proof getter zero、final/partial wrapperへのproduction
call 100%を要求する。従ってP0 routeはSS2後へ残るinterim authorityではない。SS3以後は
§4.2のfamily-static partial routeのみを使う。

#### 4.0.2 Production caller / batch matrix

現在一つのlogical validation/evaluation passで一つの`ProjectionEvaluationRound` /
`CpkPublicationEvaluationRound`を所有し、record/owner/recursive target間でchecked/memo/evaluator stateを共有する
production callerを全件列挙する。rev.7起案時点のactual codeで次の七rowを再確認した。lineは
2026-08-14 HEADの目安であり、P0実装開始時に`rg`とcall graphで再確認する。

| # | current round owner | Before | After: HRTB boundaryとsharing維持 |
|---|---|---|---|
| 1 | `ConstraintMachine::scheme_projectable_lowers` (`constraints/mod.rs:1262`)とその派生caller | method内で一つ`ProjectionEvaluationRound`を作り、`scheme_projectable_lowers_in_round` (`:1271`)のowner-record loop全体へthreadする。さらに`capture_generalized_witnesses` (`generalize/provenance.rs:21,212`)のrecursive `WitnessCollector`と、scheme-mode `CompactCollector` (`compact/collect/mod.rs:655-660`)がこのmethodを呼ぶ | direct helperは`with_legacy_projection_query`内でだけ呼べるscope-local APIとし、borrowed `Vec<SchemeProjectableLower<'query>>` / iteratorをclosure外へ返さない。witness captureは`lowering/expr/tail.rs:993`と`analysis/session/instantiate.rs:59`の各top-level captureごとにcollector traversal全体を一scopeで包み、owned witness draft/completenessだけを返す。input formattingは`check.rs:432,444`からscheme-mode compaction全体を一scopeで包み、owned `CompactRoot`だけを返す。`SchemeProjectableLower`自身のowned conversionはSS2まで行わない |
| 2 | `expand_positive_aliases_in_scheme_compact` (`generalize/mod.rs:281`, round creation `:291`) | root、全recursive-variable bounds、role input、associated valueのwalk全体に一roundをthreadし、recursively reached ownerも同じroundを使う。projectable lowerのweightがalias-neutralなら`machine.types().pos(bound.pos)`で`TypeVar`を解決する | callerがexclusive machine accessを渡し、`with_legacy_projection_query`をroot/rec-var/role traversal全体の外側へhoistする。recursive helperはmachine/roundではなくscope-local facadeをthreadし、weight判定後に`pos_var_in_scope(bound.pos)`を呼ぶ。nested scope zero、machine再borrow zeroでcache/visiting/checked sharingと現行のconditional lookup順序を維持する |
| 3 | `record_scheme_projection_liveness_mutation` (`constraints/mod.rs:1399`) | root overrideを持つ`before_round`とcurrent resultの`after_round`を作り、`affected_records` filter全体でそれぞれのevaluator memoを共有する | 一回の`with_legacy_publication_query`がaffected-record traversal全体を包み、scope内にbefore/afterの二つの独立ephemeral evaluator laneを作る。owned affected-owner setをscope外へ返し、後続mutation/publicationはscope drop後に行う |
| 4 | `evaluate_record_inclusion_publication` (`constraints/mod.rs:1833`) | record override付きbefore roundとafter roundを作り、dependent-record loopで二つのmemoを共有する | outer entryでは一publication scopeがdependent-record loop全体を包み、scope-local before/after laneを使う。既にpublication scope内にいるrow 7 subrow 7-bからは`evaluate_record_inclusion_publication_in_scope`相当を直接呼び、wrapperをnested callしない。`SchemeProjectionPublicationIntent`に必要なowned owner set/metadataだけを返す |
| 5 | `try_evaluate_projection_inclusion_snapshot` (`constraints/mod.rs:1879`) | 一のafter roundを`before` snapshot map全entryで共有する | 一publication scopeをsnapshot-map loopの外へhoistし、同じscope-local evaluatorで全recordを評価する。owned intent/transition traceだけを返す |
| 6 | `projection_inclusion_snapshot` (`constraints/mod.rs:1931`) | premiseから拡張したdependent-record set全体で一publication roundを共有し、`FxHashMap<BoundRecordId, bool>`を作る | 一publication scopeをdependent-record collect全体の外へhoistし、scope内の一evaluatorでowned snapshot mapを作って返す |
| 7 | `scheme_projection_record_is_included` (`constraints/mod.rs:1920`) | helperが呼ばれるたびに`CpkPublicationEvaluationRound::new(self)`を作るevaluator ownerである。production callは`constraints/mod.rs:1453,1466`の単一record mutation path、`publish_projection_inclusion_snapshot` (`:1948`, call `:1954`)のmap-entry loopに加え、clause-link mutation直前 (`constraints/machine/bounds.rs:1331`) とmutation後のpublication evaluation直前 (`:1480`) にある | helperをscope-local evaluatorを受け取る`scheme_projection_record_is_included_in_scope` 相当へ変え、helper自身でround/scopeを作らない。`:1453,1466`はそれぞれのenclosing mutation operationを一publication scopeで包み、`:1948`は`before` map全loopの外に一scopeを置く。bounds側pre-mutation queryはboolをownedで返してscopeを必ず閉じてから`:1332-1393`のcommit/dependency/index mutationへ進む。post-mutation queryは`:1476`のevaluation helper全体を一publication scopeで包み、row 4の`evaluate_record_inclusion_publication_in_scope`と同じscope-local evaluatorへ合流し、owned intentを返してscope drop後にdefer/publishする |

row 1の派生callerはround owner rowを増やさないが、P0のsignature/scope inventoryでは次のsubrowとして別々に
追跡する。

| row 1 subrow | current production call graph | P0後のbounded scope |
|---|---|---|
| 1-a local witness | `lowering/expr/tail.rs:986` generalization → `capture_generalized_witnesses` (`:993`) → finalize | generalization scopeを完了後、witness capture全体へ一回再entryする。collector recursionは同じscope-local facadeを使い、owned draft/completenessを返してからfinalizeする |
| 1-b component witness | `AnalysisSession::quantify_component`のgeneralized component loop → `capture_generalized_witnesses` (`analysis/session/instantiate.rs:59`) → ancestor adjustment/finalize | 各top-level capture entryにつき一回のscopeがcollector root/recursive traversal全体を包む。scope外へowned draft/completenessだけを返す |
| 1-c input completion | local completion (`yulang/src/source/mod.rs:3280`) → `HoverFormatContext::format_input_type` (`:4131`) → public input formatter (`check.rs:444`) → scheme-mode collector | top-level input-format entry一回がcollector traversal全体を包み、owned `CompactRoot`を返してscopeを閉じ、その後formatする |
| 1-d input hover | local-definition hover (`yulang/src/source/mod.rs:3990`) →同じ`format_input_type` / public formatter / scheme-mode collector | 1-cと同じ。hover helper lifetimeへscope/view/collector borrowを保存しない |

1-a〜1-dはrow 1の`scheme_projectable_lowers`を内包するsignature cascadeであり、独立した
`ProjectionEvaluationRound` / `CpkPublicationEvaluationRound` ownerではない。このため七row countは維持する。
ただしsubrowごとのproduction caller、scope entry/exit、owned result、counter labelが一件でも未割当ならrow 1未完了とする。

P0はcaller convention adoption checkpointであり、data-model conversion sliceではない。従って
`SchemeProjectableLower<'query>::bound: &'query WeightedLowerBound`はP0中にowned化しない。
`scheme_projectable_lowers_in_scope`相当が作るborrowed vector/iteratorはHRTB closure内で全消費し、scope外result typeへ
現れてはならない。row 1のproduction result boundaryは、1-a/1-bのowned witness draft/completeness、1-c/1-dのowned
`CompactRoot`、および各direct callerがscope内でfold/mapして作るhigher-level owned resultだけである。
`SchemeProjectableLower<'a>`からowned `SchemeProjectableLower`へのselected-bound cloneは§4.1とrevised SS2 gateに
記したSS2作業のまま維持する。

row 7のbounds側cascadeもround owner rowを増やさないが、mutation boundaryを跨がないことを次のsubrowで固定する。

| row 7 subrow | current production call graph | P0後のbounded scope |
|---|---|---|
| 7-a clause-link before | `commit_record_proof_clause_link_batch_mutation` → `scheme_projection_record_is_included` (`constraints/machine/bounds.rs:1331`) → proof/clause-link commitとdependency/index mutation (`:1332-1393`) | pre-mutation publication query scope内で`was_included: bool`だけをowned化する。scopeをdropしたことを型で確定してからmutation gatewayへ入る。scope/view/evaluatorをmutation越しに保持しない |
| 7-b clause-link after | committed snapshot → `try_evaluate_record_proof_clause_link_batch` → current inclusion query (`constraints/machine/bounds.rs:1476-1480`) → `evaluate_record_inclusion_publication` (`:1481`) → deferまたはpublish (`:1305-1317`, `:1414-1431`) | mutation完了後にfresh publication scopeを一回開く。同じscopeでcurrent inclusionとrow 4のdependent-record before/after evaluationを行い、nested `with_legacy_publication_query`を呼ばない。owned `SchemeProjectionPublicationIntent`を返してscopeを閉じた後だけ、fenceへのdeferまたは`publish_scheme_projection_intent`を行う |

7-aと7-bの間にはauthoritative mutationがあるため、scopeまたはephemeral checked/memoを共有してはならない。
7-bとrow 4は別scopeを直列に作るのではなく、一つのpost-mutation scope内でscope-local helper同士としてcomposeする。
この二subrowが未割当、pre-scopeがmutationまで存続、post-scopeがrow 4 wrapperをnested callする、のいずれかならrow 7未完了とする。

`scheme_projectable_lowers_in_round`をdifferent ownerに使うexplicit multi-owner caseはproductionの第七rowではない。
productionでその役割を持つのは上のgeneralization traversalである。
`constraints/proof/mod.rs:21202`付近のregression testは異なるownerを一roundで評価するfixtureとして残し、
P0 gateで一scope内sharingを検査するが、production caller inventoryに重複計上しない。

上の七rowはminimum closed setである。P0は`ProjectionEvaluationRound::new`、
`CpkPublicationEvaluationRound::{new,with_*_override}`、`scheme_projectable_lowers_in_round`のproduction callを再検索し、
helper/recursive wrapperの未割当row zeroを確認する。新しいownerが見つかった場合は同じmatrixへ追加し、七件のまま
完了としない。

各rowは次を記録し、unassigned row zeroを要求する。

| Field | Required content |
|---|---|
| logical pass owner | roundを現在作る最外callerと、そのlifetime終端 |
| before call graph | round生成、各top-level machine call、recursion/loop、round dropの順序 |
| shared state | checked records/constraints、evaluator `Done`、cycle state、record/root overrideのどれを共有するか |
| intervening operations | current immutable borrow中に可能/不可能なmutation、terminal transition、publication |
| after call graph | 一回の`with_*_query` entry、scope内target loop/recursion、`complete`、scope drop |
| result boundary | scope外へ返すowned value/error/receiptと、返してはならないborrow |
| measurement label | workload counterでrow固有のtarget/scope/hitを識別するlabel |

rewrite ruleは「inner methodごとにscopeを作る」ではなく、**current round lifetimeを所有する最外callerまでHRTB boundaryを
hoistする**ことで固定する。例えばgeneralization walkはvariableごとに`with_projection_query`を呼ばず、walk全体を一回の
closureへ入れ、scope-local facadeをrecursive walkへthreadする。publication target loopもtargetごとにwrapperへ入り直さず、
loop全体をone publication scope内で実行する。multi-owner fixtureもowner A/Bを同じclosure内で評価する。

#### 4.0.3 Early performance/counter gate

caller rewriteが親設計§2の実測で大きかったexisting round-local guard効果を失わないことを、proof-family authority cutover
前に測る。historical contextはRMW N=6のround-local `39,886,843 / 50,309,515 = 79.28%`、cold
`std::text::parse`の`114,092,543 / 144,192,658 = 79.13%`である。ただしpass/failにはhistorical binaryを使わず、
SS2-P0直前baselineとbatched-HRTB candidateを同一toolchain・同一workloadで再測定する。

測定条件:

- RMW N=6とcold `std::text::parse`をsame-binary feature/test toggleまたは同一commitのA/B buildで各3回以上実行し、
  counterは全run、wall/RSSはmin/median/maxを記録する。
- candidate比較の前にbaselineどうしのA/Aを同一回数で取り、target-order/allocator/scheduler noiseを記録する。
- total validation/evaluator entry、one-scope checked hit、evaluator memo hit、canonical read、query scope count、targets/scope、
  terminal/cycle cutを別counterで記録する。
- row 1はdirect-owner loopに加え、`local-witness`、`component-witness`、`input-completion`、`input-hover`を別labelにし、
  各top-level entryのscope countがexactly one（local witnessは先行generalization scopeとは別にwitness scope exactly one）、
  collector内再entry zero、matched-target raw-hit低下zeroを確認する。
- row 7は`clause-link-before`と`clause-link-after`を別labelにし、間のauthoritative mutation countとscope exit/entryを
  traceする。before/afterのscope IDが異なること、7-bとrow 4 evaluationのscope IDが同じこと、mutation/publication中の
  active query scope countがzeroであることをassertする。
- before/afterでcounter denominatorが変わる場合、raw hit countとhit rateの両方を示し、denominator変化のcall-graph理由を
  inventory rowへ戻す。

Pass threshold:

- deterministicに同定した同一logical target集合・同一target traceで、round-local checked+memo **raw hit
  count低下がexactly 0**。一件の低下もbatch-boundary regressionとしてfailする。
- RMW、`std::text::parse`のaggregate workload全体で、round-local checked+memo hit rate低下がbaseline比
  **1.0 percentage point以下**。この幅はhash/target traversal order、terminal/cycle cutの到達順によるdenominatorの
  legitimate variationを分離するためだけに使い、上のmatched-target raw-hit zeroを緩和しない。A/Aで
  1.0ppを超える、またはcandidateの差をtarget-order traceで説明できない場合はthresholdを広げず停止する。
- wall median regressionが各workload **5.0%未満**、peak RSS regressionが **5.0%未満**かつ18 GiB hard limitから
  十分離れている。この5.0%はcold build/runのallocator、OS scheduling、RSS samplingが生むrun-to-run
  noiseを越えるgross-regression ceilingであり、speedupの主張線ではない。A/Aの実測jitterが5.0%以上なら
  比較環境不適格とし、thresholdを広げず再測定する。
- output、error、owner、cycle、publication count mismatch zero。

raw-hit zeroはdeterministic sharing parityを、hit-rateはaggregate denominator変動を、wall/RSSはcold caller-boundary hoistのgross
regressionを別々に検出する。いずれか一件でも超えた場合、noiseとして黙認せずSS2-P0で停止し、actual numbersとcall-graph rowを
Claude/ユーザへ報告する。SS2本体のproof migrationで後から回収する前提、threshold緩和、fixtureだけのpassで先へ
進まない。閾値変更は本addendumの再査読とユーザ承認を要求する。

#### 4.0.4 P0 gate / stop

Gate:

- production caller/batch inventoryのunassigned row zero。
- §4.0.2のknown七production ownerをactual codeで再確認し、row 1 subrow 1-a〜1-dとrow 7 subrow 7-a/7-bを含む
  各rowにbefore/after call graphがある。
- §4.0.1のlegacy-only HRTB routeがproduction semantic readの100%を供給し、shadow `StructuralData`の値を
  production resultへ使わず、old `&ConstraintMachine` evaluation pathと二重borrowしない。
- §4.0.1.1のmutable-owner cascadeをhover、member completion、lowering中local generalizationの実entryまで通し、
  whole-`PolyCheckOutput` shared borrowとHRTB machine borrowが重ならずコンパイルする。
- row 1 subrow 1-a〜1-dを全て移行し、`capture_generalized_witnesses`の両production callerとinput-type
  completion/hoverのscheme-mode compactionがscope外の`&ConstraintMachine`へfallbackせず、各collector traversalを
  一bounded invocation内で完了する。
- P0中の`SchemeProjectableLower<'query>` vector/iterator escape zero。borrowed entriesはscope内で全消費し、
  higher-level owned outputだけを返す。owned `SchemeProjectableLower` conversionはSS2 gateに留まる。
- row 7のclause-link pre-scopeが`:1332`のmutation前にdropし、post-scopeがmutation後にfresh entryし、row 4 evaluationと
  nested wrapperなしで同一scopeを共有し、owned intentを返した後だけdefer/publishする。
- authoritative mutationを含まない各current-round phaseのtarget集合がone immutable scope内へ入り、separate inner-call
  scope zero。row 7 subrow 7-a/7-bは間のmutationにより意図的に別phase・別scopeとする。
- §4.0.3のraw-hit-zero/counter/wall/RSS thresholdが両workloadでgreen。
- production semantic parityとterminal/cycle behavior mismatch zero。

Stop:

- fresh `SourceTextAnalysis` / `PolyCheckOutput` ownershipから`&mut ConstraintMachine`までの§4.0.1.1 cascadeを
  byte/semantic parityを保って実装できない、またはP0 taskのwrite scopeが必要fileへ拡張されていない。
- witness captureまたはinput scheme compactionがscope-local facadeをrecursive collectorへthreadできず、persistent
  facade、scope外raw machine read、collector inner-targetごとのscope再entryのいずれかを要求する。
- row 1のborrowed `SchemeProjectableLower<'query>`をscope外へ返さないとP0 caller parityを保てない。
- row 7のpre-mutation scopeをwrite前に閉じられない、またはpost-mutation inclusion queryとrow 4 evaluationを
  nested scopeなしの一bounded invocationへcomposeできない。
- logical round ownerを一意に定められず、HRTB boundaryをhoistできないcallerが一件でもある。
- external control flowのためtarget集合をone closureへbatchできず、SS2〜SS5のcross-scope reuseがcorrectnessまたは
  unavoidable performance requirementになる。
- threshold超過、counter説明不能、scope/target instrumentation gapが一件でもある。

P0 stopを「後続SS2 gateで直す」と繰り延べない。

### 4.1 Scope and authority

**Authority:** sealed proof relationsを、HRTB scope内のproduction refined-canonical validationが読む。cache hitなし。
unmigrated bounds/constraint/row/identity familyは引き続き各legacy ownerが唯一のauthorityであり、そのreadは同じ
HRTB scope内に限定する。

親設計SS2のproof-family write migrationを全て維持したうえで、次をSS2へ追加する。

- `ProofOccurrenceStore`のcache-relevant proof/formula/certificate/adjacency/replay/claim/live/index relationを
  `StructuralData::proof` / `ProofRelations`へ吸収する。
- `ProjectionPreflight<'a>`をscope-local `ProjectionPreflightFacade<'query>`へ、
  `CpkProjectionEvaluator<'a>`をscope-local `CpkProjectionEvaluatorFacade<'query>`へ移行する。
- current borrowed `ProjectionEvaluationRound<'a>` / `CpkPublicationEvaluationRound<'a>`をSS1-RFのlifetime-free owned
  round control objectへproduction cutoverする。ただしSS2〜SS5では`SealingIncomplete`だけを生成し、別々のwrapper
  invocation間でchecked/memo/override/cycle success stateをreuseしない。
- production projection/publication callerを、それぞれ
  `ConstraintMachine::{with_projection_query, with_publication_projection_query}`だけへ統一する。
- production proof-family mandatory readを`ScopedQueryView<'query>`のproof getter/cursorだけへ切り替え、
  direct `&ProofOccurrenceStore` borrowerをzeroにする。
- `SemanticFactView for ConstraintMachine`をproduction preflight/evaluator authorityから外す。test-only adapterもraw viewを
  scope外へ返さない。
- `SchemeProjectableLower<'a>`をowned `SchemeProjectableLower`へ変え、selected `WeightedLowerBound`だけをscope内で
  cloneする。SS0で列挙した他のborrowed structural resultも同じsliceでowned descriptor/valueへ変換する。
- CPK-SV-C late-bound claim/live readとrecursive record/constraint/root traversalを一top-level scope内で直接再帰させ、
  nested wrapperを呼ばない。
- current productionが一roundでchecked/memoを共有する複数top-level targetは、一回の`with_projection_query`または
  `with_publication_projection_query` closure内でbatch評価する。同じimmutable HRTB scope内のephemeral state共有で
  current semantic behaviorを維持し、scope外へfacade/stateを返さない。

### 4.2 Partial-sealing中のread source routing

SS2〜SS5でpersistent interim facadeは作らない。一方、まだsealed ownerへ移っていないfamilyをproduction
preflight/evaluatorが読む必要はある。これを、machine delegateがtargetごとに構築する**scope-private、
family-static routing**で扱う。

概念形は次である。

```rust
// SS2完了時のexact shape。access/read_view内部だけ。re-export/round保存はしない。
struct PartialSealingReadSources<'query> {
    sealed: &'query ProofStructuralState<ProofSealedLayout>,
    legacy_bounds: &'query TypeBounds,
    legacy_constraints: LegacyConstraintReadSources<'query>,
    legacy_rows: LegacyRowReadSources<'query>,
    legacy_identities: LegacyIdentityReadSources<'query>,
}

struct ScopedQueryView<'query> {
    partial: PartialSealingReadSources<'query>,
    snapshot: ProofStructuralSnapshotId,
    type_shapes: ImmutableTypeShapeView<'query>,
}
```

これはarbitrary callerへ渡すinterim viewではない。`ConstraintMachine::with_*_query`が`&mut proof_attempt`とlegacy
read-only fieldsをfield split-borrowし、private kernel constructorへ一scope分だけ渡す。外部signatureは§2.2から
変えない。`PartialSealingReadSources`とそのfieldはprivateで、HRTB closure外へescapeせず、roundへ保存されない。

familyごとのsourceはcompile-timeに一つだけとする。runtime fallback、old/new比較後の選択、`Option`でのdual readを
禁止する。上のstructを全phase分併存させるのではない。SS3は`sealed`を
`ProofStructuralState<ProofBoundsSealedLayout>`へ置き換えて`legacy_bounds`を削除し、SS4は
`ProofBoundsConstraintsSealedLayout`へ、SS5は`RowsSealedLayout`を経て`FullySealedLayout`へコンパイル時に
一方向変更する。各commitのproduction binaryにactive route shapeは一つしか存在しない。

| slice完了時 | proof | bounds | constraints/replay | rows | identities |
|---|---|---|---|---|---|
| SS2 | sealed | legacy scope borrow | legacy scope borrow | legacy scope borrow | legacy scope borrow |
| SS3 | sealed | sealed | legacy scope borrow | legacy scope borrow | legacy scope borrow |
| SS4 | sealed | sealed | sealed | legacy scope borrow | legacy scope borrow |
| SS5 | sealed | sealed | sealed | sealed | sealed |

各family sliceはwrite authority cutoverと同じcommit seriesで、そのfamilyの`ScopedQueryView` getter sourceをlegacyから
sealedへ一方向に切り替え、legacy fieldをprivate constructorから除去する。one factをold/new双方から読む期間、fallback、
dual authorityを作らない。SS5完了時に`PartialSealingReadSources`自体を削除し、親設計§3.1.1の最終形
`ScopedQueryView { fully_sealed_inputs, snapshot }`へ収束する。

このroutingはround reuse modeから独立する。`PartialSealingReadSources`は一invocationのexclusive borrowだけを表し、
checked/memoを所有せず、scope終了時に必ずdropされる。従って`SealingIncomplete`への変更でpersistent化も再構築も
不要であり、rev.1のfamily-static source assignmentをそのまま維持できる。

### 4.3 Partial-sealing中のround stateとD0 snapshotの非authority化

SS2〜SS5ではcross-scope success reuseを行わないため、D0 `ProofStructuralSnapshotId`をround binding identityへ使わない。
wrapperはattempt nonceだけを認証し、every invocationでfresh ephemeral checked/memo/override stateを作る。numeric snapshotが
前scopeと同じでも、checked record/constraint、evaluator `Done`、record/root override resultをhitできるpersistent
entryが存在しない。

D0 snapshotは次の既存shadow用途にだけ残る。

- 親設計SS2〜SS5が既に要求するD0-vs-gateway logical snapshot parity measurement。
- CPK-SV-A/B/Cの既存test/shadow instrumentationが独自に参照する箇所。
- SS5でgateway finalizerへwriter authorityを一本化したと証明してD0 scattered bumpをretireするための比較証拠。

D0 bumpの有無をproduction read skip、round reuse、cache lookup/publication、semantic error selectionの根拠にしない。
D0 parity mismatchは元のslice gateを失敗させるが、mismatch前後のproduction validation correctnessをD0 exhaustivenessへ
依存させない。

`ScopedQueryView`がtrace/receipt用にsnapshot valueを露出しても、SS2〜SS5ではobservational metadataでありreuse keyでは
ない。global snapshotをprepared semantic base/conflictへ使わず、invariant 63を維持する。

SS5 gateでall raw writers sealed、gateway single-finalizer closure、D0-vs-gateway parityがgreenになっても、そのcommit
series内ではまだcross-scope reuseを有効化しない。SS6がwitness-bound `RoundReuseSlot::sealed` factoryとgateway completed snapshot
bindingをlandingし、§6.2のhuman census/test/reviewとreal sealed-data fixtureを通した時点で初めて再有効化する。
SS2〜SS6はproduction cache hitで
validationをskipせず、invariant 53を維持する。

### 4.4 Revised SS2 gate

親設計SS2 gateと8件のgateway-level fixture contractを全て維持し、次を追加する。

- production proof-family mandatory readのdirect `&ProofOccurrenceStore` borrower zero。
- production `ProjectionPreflight` / evaluator proof readが全件HRTB `ScopedQueryView<'query>`経由である。
- P0専用の`ScopedLegacyProjectionQuery`、`ScopedLegacyPublicationQuery`、`LegacyOnlyReadSources`、
  `with_legacy_*`のproduction name/reference zero。
- old proof read/write authority、new sealed proof authorityのdual-source row zero。
- `ConstraintMachine::proof_store`へのread/write probeがE0609相当でcompile-failし、production kernel fieldが
  `ProofAttemptKernel<ProofSealedLayout>`相当のnext layoutだけである。
- proof transitionがactual `LegacyProofOwner(ProofOccurrenceStore)`とold kernel valueをby-value consumeするcall
  exactly oneで、empty/ZST proof seal constructor zero。
- round-persistent fieldにstore/view/machine/type-arena borrow zero。
- current round-sharing regressionのtarget A/Bを**同じ一scope内**で評価し、BがAのephemeral checked/memoを実際にhitする。
  target集合、output、error、cycle behaviorはbaseline parityである。
- 同じowned round control objectを二scopeへ順に渡すnegative fixtureでは、D0 numeric snapshotが同じでも二scope目の
  cross-scope checked/memo/override hit zero、mandatory canonical read nonzeroである。scope間にcache-relevant mutationを
  注入し、そのD0 bumpをtest hookで故意に抑止するvariantでも結果がfresh canonical executionと一致する。
- `SealingIncomplete`からsealed slotをcaller/test adapterがconstruct/activateできるpath zero。
- recursive validation、CPK-SV-C late-bound claim/live、record/root recursionのnested query-scope call zero。
- `SchemeProjectableLower`その他SS0列挙resultのborrowed structural field zero。selected-only clone/output parity green。
- unmigrated family readは`PartialSealingReadSources`のscope-private static routeだけであり、persistent view、runtime
  fallback、old/new dual read zero。
- D0 snapshotをround reuse/cache correctness authorityとして読むproduction branch zero。D0-vs-gateway logical parityは
  parent gateどおりshadow evidenceとしてgreenである。
- persistent structural-validity cache hitによるtop-level canonical validation skip zero。one-scope内のexisting checked
  guardによる重複抑止は許可し、scopeを跨ぐpersistent reuseとtrace上で区別してcross-scope skip zeroを明示assertする。
- full CPK-SV-A/B/C oracle mismatch zero、stable/canonical trace mismatch zero、owner/error precedence parity。

### 4.5 Revised SS2 stop condition

親設計§9の全stop conditionに加え、次は既存stop condition 9、10、21、30、36、62、70の具体的適用としてSS2を
停止する。

- proof write authorityとproof read authorityを同じreviewable cutover seriesで一意化できず、dual authorityが必要になる。
- P0 all-legacy semantic readをfield-split `LegacyOnlyReadSources`で表せず、scope中にold
  `&ConstraintMachine` pathへ戻るかshadow valueをproduction authorityにする必要がある。
- production proof readにpersistent facade、raw `&ProofRelations` escape、per-getter capability recheckが必要になる。
- actual `ProofOccurrenceStore` valueをconsumeするkernel layout transitionを作れず、ZST/boolean/reportでproof sealingを
  attestする必要がある。
- current cross-target semantic behaviorをone immutable HRTB invocation内で維持できず、SS2〜SS5でcross-scope
  checked/memo reuseを残す必要がある。
- `SealingIncomplete` roundへsuccess-derived checked/memo/override/cycle stateが保存される、またはscope entryがfresh stateを
  作らず以前のinvocationを参照できる。
- one top-level recursive traversalをsingle HRTB scopeで表せず、nested scopeまたはre-entrant kernel borrowが必要になる。
- partial-sealing static routeがfamily単位で一意にならず、runtime fallback/old-new mergeを必要とする。
- D0 snapshotをproduction cross-scope reuse、cache candidate lookup/publication、validation skipのauthorityへ戻す必要がある。
- D0 snapshot parityをshadow gateとして説明できない。ただしこのfailureをproduction read correctness failureへ結びつけず、
  slice completion failureとして扱う。
- owned `WeightedLowerBound` / other descriptor conversionがsemantic parityを保てず、raw borrowed resultへ戻す必要がある。

## 5. SS3〜SS5への波及

SS3、SS4、SS5のwrite-migration scope、authority、gate、stop conditionは親設計から変えない。各sliceに
read-source retirementと、§6.1の**actual legacy ownerをconsumeするkernel layout transition**を加える。

- SS2: `ConstraintMachine::proof_store: ProofOccurrenceStore`のvalueを`LegacyProofOwner`としてby-valueで取り出し、
  `ProofRelations`へ変換して`ProofAttemptKernel<Ss1ShadowLayout>`を
  `ProofAttemptKernel<ProofSealedLayout>`へ消費的に進める。cutover後の`ConstraintMachine`から
  `proof_store` fieldとP0 legacy proof routeを削除する。
- SS3: `ConstraintMachine::bounds: TypeBounds`を`LegacyBoundsOwner`としてmoveし、`BoundRelations`へ変換して
  `ProofBoundsSealedLayout`へ進める。同じseriesで`legacy_bounds`を`PartialSealingReadSources`から削除し、
  全bound getterをsealed sourceへ固定する。
- SS4: `canonical_constraints`、`constraint_records`、`replay_drop_records/index`、
  `replay_derivation_budget/storage`等のSS0でconstraint/replay familyに割り当てた実fieldを一つの
  `LegacyConstraintReplayOwner`へ所有させ、そのaggregate valueをconsumeして`ConstraintRelations`と
  `ProofBoundsConstraintsSealedLayout`を作る。legacy constraint/replay sourceとdirect fieldsを同時に削除する。
- SS5: row residual/derivation/index、unweighted row reduction state/owner/processed-lower、cache-relevant lower-filterの
  実field群を`LegacyRowOwner`に、`origins`、`source_boundaries`、`generalized_schemes/witnesses`、
  `scheme_instantiations/index`を`LegacyIdentityOwner`に束ねる。両aggregateをby-value consumeする二つの
  transitionで`RowsSealedLayout`を経由して`FullySealedLayout`へ進め、remaining legacy fields/read routesと
  `PartialSealingReadSources`自体を削除する。SS5自身はround reuseの`SealingIncomplete`を維持する。

constraint/replay、row、identityは現行`ConstraintMachine`上の複数のowned fieldから成るため、sliceの最初に
private `Legacy*Owner`へstructurallyグループ化する。このpre-stepは所有者とread/write authorityを変えず、
後続transitionが一つの実valueをmoveできる形にするだけである。diagnostic sidecarとSS0で分類したfieldは
aggregateに入れず`ConstraintMachine`に残す。SS0 owner tableの各cache-relevant rowがどのaggregate fieldまたはsealed
destinationに入るかをsliceごとにreviewed zero-unassignedで固定する。このreview結果は§6.2でfinal HEADへ再ベースする。

各slice gateへ、そのfamilyのlegacy read source zero、sealed getter coverage 100%、old/new fallback zeroを加える。
これはinvariant 37、38、53、75の既存要求をslice単位で検査可能にするrefinementであり、新しいinvariantではない。

SS2〜SS5の間、separate wrapper invocation間のchecked/memo reuseというperformance propertyは一時的にoffになる。
同じimmutable scopeへbatchできるtarget間のsharingは維持する。scopeを跨ぐsharingはSS5 gate完了後のSS6で、sealed
gateway completed snapshotを唯一のreuse identityとして回復する。これはcapabilityを暗黙に削除せず、安全な再開点を
明示するためのtemporary performance tradeoffであり、semantic output/error/precedenceを変更しない。

Family-slice gateへ次を追加する。

- 各slice完了時、old kernel layoutと実`Legacy*Owner`をby-value consumeするtransition callがexactly oneあり、
  cutover後の`ConstraintMachine` field typeはnext layoutだけである。
- 削除後のlegacy direct fieldを読む/writeするprobeがE0609相当、next-layout-only APIをold layoutで呼ぶprobeが
  E0599/type mismatch相当でcompile-failする。
- later layout、sealed family owner、legacy aggregateのfield/constructorはowner module privateで、external/siblingの
  struct-literal、`Default`、`Clone`、test-only forge pathがcompile-failする。
- SS5完了時、production kernel value自体が実の五family ownerを持つ
  `ProofAttemptKernel<FullySealedLayout>`である一方、`RoundReuseSlot::sealed` production callはまだzeroである。
- 列挙済みlegacy raw field/read-sourceを残したtypeは`FullySealedLayout`を求めるSS6 APIと型一致せず、
  compile-failする。列挙外field/authorityの不在は§6.2のcensus gateで判定する。

## 6. 改訂slice: CPK-SV-D-SS6

SS6は独立sliceとして残す。ただし名称とscopeを次へ縮小する。

### CPK-SV-D-SS6: sealed-snapshot reuse activation + evaluator/cache-shadow closeout

**Authority:** SS2〜SS5でproduction cutover済みのHRTB sealed query scopeを通るrefined canonical validation。
cache hitはshadow-only。

### 6.1 Structural best-effort seal-completion guard

`SS5 gate green`というtest/reportやzero-sized receiptだけから`Sealed` modeを作らない。SS2〜SS5の
actual type/layout cutoverは、各familyのlegacy storage valueをby-valueで消費し、実のsealed family ownerを所有する
next kernel layoutへ進む。SS6はこの最終layout valueを持つkernelからしかwitnessを得られない。

ただし、このchainが証明するのは「型に列挙された各`Legacy*Owner`とsealed family valueを所有・消費した」
ことに限る。次は証明しない。

- cache-relevant fieldが`Legacy*Owner`の定義から漏れていないこと。
- legacy valueがaggregate外の`ConstraintMachine`、別owner、duplicate、side tableとして残っていないこと。
- 将来のmandatory inputがsealed family外に追加されていないこと。
- HRTB closureがowned external fact/callbackをcaptureし、gateway snapshotと無関係に変化するread pathを作っていないこと。

Rustのtype systemは、一つのaggregateが「将来追加されるfieldも含めて完全な世界集合」であることを形式化しない。
従って、このtypestateは、`access.rs`のcareless editがfamily transitionを通らず`Sealed`を作ること、または
明示的に列挙されたfamily ownerをconsumeし忘れることを防ぐbest-effort guardである。
「all legacy authority absent」の完全性は§6.2の人手census/test/review gateが判定する。

#### 6.1.1 Ownership typestate and real-value transitions

カーネルのstructural ownerはlayout type parameterを持つ。各layoutのfieldはplaceholder markerではなく、その段階で
すでにcut overした実family ownerである。

```rust
// gateway/storage.rs。traitとlayout fieldはstructural_kernel外へ出さない。
trait StructuralLayout: private::Sealed {}

struct Ss1ShadowLayout {
    // SS1のshadow placeholdersだけ。production family authorityは持たない。
    shadow: ShadowStructuralData,
}

struct ProofSealedLayout {
    proof: ProofRelations,
}

struct ProofBoundsSealedLayout {
    proof: ProofRelations,
    bounds: BoundRelations,
}

struct ProofBoundsConstraintsSealedLayout {
    proof: ProofRelations,
    bounds: BoundRelations,
    constraints: ConstraintRelations,
}

struct RowsSealedLayout {
    proof: ProofRelations,
    bounds: BoundRelations,
    constraints: ConstraintRelations,
    rows: RowRelations,
}

struct FullySealedLayout {
    proof: ProofRelations,
    bounds: BoundRelations,
    constraints: ConstraintRelations,
    rows: RowRelations,
    identities: IdentityRelations,
}

pub(in crate::constraints::structural_kernel) struct ProofAttemptKernel<L: StructuralLayout> {
    structural: ProofStructuralState<L>,
    terminal_failure: RefCell<Option<ProofFailure>>,
    // reservation ledger / arena / attempt nonce等は従来どおり。
}

struct ProofStructuralState<L: StructuralLayout> {
    data: L,
    snapshot: ProofStructuralSnapshotId,
    // cacheはSS7までauthorityを持たない。
}
```

`StructuralLayout`とlayout type名は`pub(in crate::constraints)`までname可能にし、
`ConstraintMachine`のprivate field typeとfactory signatureに使えるようにする。一方、layoutの全field、
field constructor、transitionのraw assembly helperは`gateway/storage.rs`またはowning family moduleのmodule-privateに保つ。
`ConstraintMachine`側は各sliceで一つのprivate alias（例: `ActiveProofAttemptKernel`）をfield typeに使い、
そのalias targetをsliceのnext layoutに更新する。これは`deny(private_interfaces, private_bounds)`でgreenにする。

各later layoutにpublic/restricted `new` / `Default` / field constructorを作らない。列挙済みfamily valueについて後続layoutを作る唯一の経路は、
old kernel valueと実legacy owner valueの両方をconsumeするfamily-owned transitionである。概念signatureを次で固定する。
各`Legacy*Owner`はnon-`Copy`、non-`Clone`、non-`Default`で、inner valueを取り出すpublic/restricted methodを
持たない。そのfamilyがcutoverする直前の`ConstraintMachine`はraw fieldではなく該当
`Legacy*Owner`をexactly one所有し、transitionはそのfieldを所有するconstruction stepだけから呼ぶ。
`mem::take`、empty replacement、`Option::None`を使ってlegacy fieldを残すpathを禁止する。

```rust
fn install_proof_family(
    kernel: ProofAttemptKernel<Ss1ShadowLayout>,
    legacy: LegacyProofOwner, // ProofOccurrenceStoreを所有
) -> Result<ProofAttemptKernel<ProofSealedLayout>, ProofFailure>;

fn install_bounds_family(
    kernel: ProofAttemptKernel<ProofSealedLayout>,
    legacy: LegacyBoundsOwner, // TypeBoundsを所有
) -> Result<ProofAttemptKernel<ProofBoundsSealedLayout>, ProofFailure>;

fn install_constraints_replay_family(
    kernel: ProofAttemptKernel<ProofBoundsSealedLayout>,
    legacy: LegacyConstraintReplayOwner,
) -> Result<ProofAttemptKernel<ProofBoundsConstraintsSealedLayout>, ProofFailure>;

fn install_rows_family(
    kernel: ProofAttemptKernel<ProofBoundsConstraintsSealedLayout>,
    legacy: LegacyRowOwner,
) -> Result<ProofAttemptKernel<RowsSealedLayout>, ProofFailure>;

fn install_identities_family(
    kernel: ProofAttemptKernel<RowsSealedLayout>,
    legacy: LegacyIdentityOwner,
) -> Result<ProofAttemptKernel<FullySealedLayout>, ProofFailure>;
```

transitionはactive query中のmachineをruntime migrationするAPIではない。各sliceのproduction
`ConstraintMachine` constructor graphがowned legacy valueを作り、そのままtransitionへmoveして新しいmachineを構築する。
transitionがfallibleなら、machine publication前に失敗し、partial attemptを外へ出さない。cutover後の
`ConstraintMachine`はlegacy direct fieldを持たず、そのsliceのnext-layout kernelだけを所有する。

列挙済みの実value移動自体は現行code shapeで五familyすべてに適用可能である。`proof_store`と`bounds`は単一owned fieldである。
constraint/replay、row、identityは複数owned fieldだがalias/referenceではないため、§5のprivate aggregateに先に束ねて
一valueとしてconsumeできる。ただしこれはaggregateの列挙完全性を型で証明しない。SS0 owner tableの一rowでもmove先が不明な場合、
そのfamilyのtransitionは作らず、親設計§9.1どおり停止する。

2026-08-14 current `ConstraintMachine`のowned fieldとtransition inputの対応は次である。この表はSS0の
cache-relevant owner tableを置き換えず、実valueをmoveできることを確認する。

| family / slice | consumed production-owned value | next layoutが所有するvalue |
|---|---|---|
| proof / SS2 | `proof_store: ProofOccurrenceStore` | `proof: ProofRelations` |
| bounds / SS3 | `bounds: TypeBounds`のcache-relevant `vars/canonical/records`（`BoundDisposition`系はdiagnostic sidecarへ先に分離） | `bounds: BoundRelations` |
| constraints/replay / SS4 | `canonical_constraints`、`constraint_records`、`replay_drop_records`、`replay_drop_index`、`replay_derivation_budget`、`replay_derivation_storage`とSS0のconstraint→lower/replay rows | `constraints: ConstraintRelations` |
| rows / SS5 | `row_residuals`、`row_residual_record_ids`、`row_residual_records`、`unweighted_row_reductions_by_source`、`unweighted_row_reduction_owners_by_upper`、`unweighted_row_reduction_records`、`row_derivations`、`row_derivation_index`、`lower_filters`、`lower_filter_record_ids`、`lower_filter_records`とSS0のcache-relevant row rows | `rows: RowRelations` |
| identities / SS5 | `origins`、`source_boundaries`、`generalized_schemes`、`generalized_witnesses`、`scheme_instantiations`、`scheme_instantiation_index` | `identities: IdentityRelations` |

`events`、timing、queue、outbox、diagnostic sidecarはこのtransition inputに入れない。逆にSS0でcache-relevantと
判定したrowを「表に名がない」ことを理由に外へ残してはならない。family sliceはSS0 tableとこの
aggregate definitionをjoinし、reviewed zero-unassignedをgateにする。このzero-unassignedは人手でreviewされるcensus
propertyであり、typestateが自動で証明するpropertyではない。

#### 6.1.2 Restricted final read-surface guard

最終read surfaceは別の`NoLegacyReadSources`証明tokenを作らない。`FullySealedLayout`の実value自体が
五family ownerの集約であり、SS5は`PartialSealingReadSources`と全`Legacy*ReadSources`を削除し、
final constructorを次のexact inputだけへ収束させる。

```rust
struct FullySealedReadInputs<'query> {
    data: &'query ProofStructuralState<FullySealedLayout>,
    type_shapes: ImmutableTypeShapeView<'query>,
}

// read_view.rs private。final ScopedQueryView constructorと同じ場所でのみ生成する。
fn fully_sealed_read_inputs<'query>(
    kernel: &'query ProofAttemptKernel<FullySealedLayout>,
    type_shapes: ImmutableTypeShapeView<'query>,
) -> FullySealedReadInputs<'query>;
```

`FullySealedReadInputs`は`ConstraintMachine`、legacy store、generic trait object、callback、`Option<Legacy*>`をfieldに持たない。
constructor argumentのkernel layoutがpartialならtype mismatchであり、`ProofAttemptKernel<ProofBoundsConstraintsSealedLayout>`
等からfinal viewを作れない。SS5 gateは次をstructural compile/UI checkとreviewed source searchで固定し、
§6.2でlatest HEADに対して全件再検査する。

- `PartialSealingReadSources` / `Legacy*ReadSources` type、constructor、field reference zero。
- final `ScopedQueryView` constructorへ`ProofAttemptKernel<FullySealedLayout>`と
  `ImmutableTypeShapeView`以外を渡すproduction call zero。
- production preflight/evaluatorが`ScopedQueryView`以外のmandatory structural inputをnameするknown path zero。
  これはcompile proofではなく、semantic getter/cursor/captureの人手census resultである。
- censusに列挙したold family storage field/raw read/write accessがcompile-fail。
- partial layoutから`fully_sealed_read_inputs`を呼ぶnegative probeがtype mismatch/E0308相当でcompile-fail。

正規のfacade constructor経由で将来mandatory inputをsealed state外へ追加すると、facadeはその値を受け取れない。値を読ませるには
`FullySealedLayout`、`FullySealedReadInputs`、`fully_sealed_read_inputs`というchoke pointを明示変更し、
SS5/SS6 compile gateも同時に変更する必要がある。忘れたままsilent stale hitへ進むのではなく、input unavailableのcompile error
またはこの単一のsecurity-sensitive diffとして表面化する。

この保証は正規constructorとそのfield集合に限られる。query closure自体がexternal owned fact/callbackをcaptureすること、
あるいはmandatory readがfacade外のhelperへ追加されることの不在まで型は証明しない。従って「final input typeが
restrictedだからmandatory input完全性もmechanicalに証明済み」とは判定せず、§6.2でclosure captureと全semantic
getter/cursor callerを人手で再棚卸しする。

#### 6.1.3 Aggregate authority and per-round witness

`AllFamiliesSealedAuthority`という別のZSTをassemblyしない。実のaggregate authorityは
`ProofStructuralState<FullySealedLayout>`自体である。per-round witnessはこのactual ownerへのborrowを持ち、
`ProofAttemptKernel<FullySealedLayout>`にだけ定義するmethodから発行する。

```rust
pub(super) struct AllFamiliesSealedWitness<'authority> {
    authority: &'authority ProofStructuralState<FullySealedLayout>,
    _private: Private,
}

// access/sealing.rs module private。raw constructorとfield accessは他moduleへ出さない。
struct SealedRoundBinding {
    snapshot: ProofStructuralSnapshotId,
}

impl ProofAttemptKernel<FullySealedLayout> {
    // access/sealing.rsからだけ使う。partial-layout implにはこのmethod自体が存在しない。
    pub(super) fn issue_round_reuse_witness(&self) -> AllFamiliesSealedWitness<'_> {
        AllFamiliesSealedWitness {
            authority: &self.structural,
            _private: Private,
        }
    }
}

impl<'authority> AllFamiliesSealedWitness<'authority> {
    fn into_round_binding(self) -> SealedRoundBinding {
        SealedRoundBinding {
            // D0やcaller-supplied IDではなく、witnessがborrowするgateway authorityから得る。
            snapshot: self.authority.completed_snapshot(),
        }
    }
}
```

round factoryはfully-sealed kernelのactual state borrowを持つfresh non-Copy witnessを一つissueし、§2.1の
`RoundReuseSlot::sealed(witness, reusable)`へby-valueで渡す。`sealed`はraw
`ProofStructuralSnapshotId`を受け取らず、witnessを`SealedRoundBinding`へconsumeして、そのauthorityが所有する
gateway completed snapshotだけをbindする。従ってvalid witnessとD0 snapshot、caller-supplied snapshot、foreign kernelのsnapshotを
組み合わせるAPIはない。witness/bindingは保存、clone、再利用できない。roundのattempt nonce checkは従来どおり
別層で維持する。

重要なのはwitnessのprivate fieldではなく、method receiverのtypeである。SS4完了時のkernelは
`ProofAttemptKernel<ProofBoundsConstraintsSealedLayout>`であり、`issue_round_reuse_witness`をnameしても
E0599相当でcompileしない。SS5の二つのtransitionが実`LegacyRowOwner` / `LegacyIdentityOwner`をconsumeして
初めてreceiver valueが`FullySealedLayout`になる。ZST receiptを早期mintする余地はない。

`RoundReuseState` inner enumと`Sealed` variantは`access/sealing.rs` module privateなので、`access.rs`はstruct literal/
variant syntaxで迂回できない。careless editが`Sealed`を早期生成するには、少なくとも次のsecurity-sensitive boundaryを
明示変更しなければならない。

1. `access/sealing.rs`へwitness不要constructorを追加する。
2. `issue_round_reuse_witness`をpartial layoutのimplへ新設する。
3. family transitionのowned legacy argumentをoptional/ZSTに弱める。
4. `ConstraintMachine`のfield typeをactual migrationと無関係に`FullySealedLayout`へ改変する。
5. final read surfaceへlegacy/external inputを追加する。

これらは通常のcaller editで偶発的に起きず、compile-fail/UI gateとsingle choke-point reviewへ露出する。本書はmalicious
editorに対するproofも、列挙されていないlegacy authorityの不在proofも主張しない。防ぐのは、
「constructorからZST attestationを返す」または「access.rsでenum variantを直接選ぶ」というaccidental bypassである。

SS6 compile gate:

- later layout、legacy aggregate、sealed family owner、per-round witnessのexternal/sibling constructionが
  E0451/E0603相当でfailure。
- `RoundReuseSlot::sealed`へmissing/foreign/forged tokenを渡すprobeがcompile-fail。
- `RoundReuseSlot::sealed`へraw/D0/caller-supplied `ProofStructuralSnapshotId`を別引数で渡すprobeが
  signature mismatchでcompile-failし、snapshotは`SealedRoundBinding`以外から構築できない。
- 各transitionからlegacy owner argumentを除くnegative probeがargument/type errorでcompile-fail。
- partial-layout kernelから`issue_round_reuse_witness`を呼ぶprobeがE0599相当でcompile-fail。
- `ConstraintMachine`のSS6 production field typeがnon-optional `ProofAttemptKernel<FullySealedLayout>`で、censusに列挙した
  legacy structural owner/read-source field zero。列挙の完全性は§6.2へ渡す。
- final kernelの`FullySealedLayout`が列挙済み五familyの実owner valueをexactly oneずつ所有する。
- direct `RoundReuseState::Sealed` syntaxを`access.rs`/family/testからnameできない。

### 6.2 SS5→SS6 human census / adversarial test gate

§6.1のcompile gateだけでは`Sealed` activationを許可しない。SS6の最後のactivation changeより前に、
次のhuman/process gateを独立checkpointとして完了する。これはcompiler proofではなく、CPK-SV-D0で受け入れたのと同じ
水準の「structural best-effort guard + reviewed census + adversarial test」である。本書はこのgateをmechanical
exhaustivenessと呼ばない。

#### 6.2.1 Reviewed owner / read / writer census

SS0表を最新HEADへrebaseし、少なくとも次の実体をfield/container単位で全件再走査する。

- `ConstraintMachine`の全field、nested child container、diagnostic sidecar、queue/outbox/timing。
- `ProofAttemptKernel<FullySealedLayout>`、`ProofStructuralState`、五family ownerの全field。
- constraints/proof/bounds/row/replay/identityを読む全production getter/cursor/helperと、
  §4.0.2の七callerから到達するmandatory read。
- `with_projection_query` / `with_publication_projection_query` closureがcaptureする値、callback、
  trait object、global/thread-local/test hook。`ImmutableTypeShapeView`のappend-only exceptionも一rowとして扱う。
- raw writer、prepare/commit、changed/no-op branch、gateway receipt、snapshot publication。

各rowは`owner`、`cache relevance`、`writers`、`readers/callers`、`sealed family destination`、
`gateway receipt/snapshot route`、`non-cache-relevant exclusion rationale`、`source reference`を持つ。
cache-relevant rowはexactly one sealed familyへ割り当て、除外rowは親設計§5.4または既承認invariantに根拠を持たせる。
unassigned、multi-authority、unexplained external captureをzeroにする。

D0の既存19+ writer-site censusとshadow notificationは候補探索とlogical parity比較へ再利用してよい。五回のD0 reviewで
確認されたlocal bump mechanicsは比較証拠になる。一方、D0 inventory自体のexhaustivenessをauthorityにせず、
「D0に無いからnon-cache-relevant」「D0 parityがgreenだから全writer sealed」とは結論しない。`rg`によるraw field/
mutator/getter検索、constructor/closure capture検索、SS0表、final layout表、D0表を相互に突き合わせ、差分を全件説明する。

#### 6.2.2 Production-caller fixtures and omission-sensitive fault injection

§4.0.2の七production rowそれぞれについて、実entrypointを通るfixtureを少なくとも一つ持つ。production factoryは
`SealingIncomplete`のまま保ち、private test-only activation harnessだけが§6.1 witnessを使って予定する最終routeを検証する。
各fixtureは同一attemptでtarget Aを評価してcross-scope reusable stateをwarmし、scopeを閉じ、次のtarget/record集合をtarget Bで評価する。
forced-canonical executionをoracleとして、result、error precedence、checked/memo/override traceを比較する。

各family（proof、bounds、constraints/replay、rows、identities）について、そのcallerが読むfactをChanged gateway commandで
更新するvariantを作り、gateway completed snapshot advance、old hit zero、canonical result一致を確認する。加えて実装可能な
rowではtest-only fault injectionで次のいずれかを故意に起こす。

- legacy/cache-relevant fieldをfamily aggregate/read routerから一時的に省いたequivalent sourceを読む。
- authoritative factをgateway finalizer/receiptを通さず変更する。
- HRTB closureへsnapshot外のmutable external factをcaptureする。

fault-injected build/fixtureは「そのまま正しく動く」ことを期待しない。forced-canonical oracleとの差、D0-vs-gateway trace差、
またはcensus completeness assertionの少なくとも一つが確実にfailureを報告することを確認し、test harnessが omissionへ
sensitiveであることを示す。faultを外したproduction candidateでは全七rowがgreenでなければならない。物理field omissionを
安全に注入できないrowは`not practical`と黙って省略せず、理由と代替のwriter-bypass/external-capture injectionを
evidence packageへ記録する。

#### 6.2.3 Evidence package and activation authority

SS6の`RoundReuseSlot::sealed` production callを追加するreviewより先に、次を一つのevidence packageとして
Claudeへ提示する。

1. 最新HEADのcensus表と、zero-unassigned / zero-unexplained-captureのreview記録。
2. raw writer/read/constructor/closure-capture検索結果と、各hitの割当または除外理由。
3. D0-vs-gateway parity trace。D0はshadow comparisonでありcorrectness authorityではない旨を明記する。
4. 七caller × applicable familyのfixture matrix、forced-canonical comparison、fault-injection sensitivity結果。
5. §6.1 compile/UI gate、SS5 family gate、SS6 capacity/latch/failure hardeningの結果。
6. reviewerが発見した残余、実施不能なfault injection、明示的に受容するhuman-review risk。

Claudeの独立reviewが完了するまで`SealingIncomplete`を維持する。既存のslice承認・push processは変更しない。
§6.1のtype witnessはこのprocess approvalをencodeしないし、encodeすると主張しない。production activation commitは
evidence packageへの参照を持ち、compiler gateとhuman gateの両方を満たした最後のatomic changeだけとする。

SS6から削除済みとして扱う項目:

- existing SS1 HRTB scope/round shellのfinal-shapeへの拡張・置換と、machine delegate/exact visibilityの完成
  （SS1-RFへ移動）。
- borrowed roundからlifetime-free round control objectへのproduction cutover（SS2へ移動）。
- `ProjectionPreflight` / `CpkProjectionEvaluator` scope-local facade cutover（SS2へ移動）。
- production `SemanticFactView for ConstraintMachine` dependency removal（SS2へ移動）。
- `SchemeProjectableLower`と他borrowed resultのowned migration（SS2へ移動）。
- family read sourceのfinal `StructuralData`一本化（SS2〜SS5へ分散）。

SS6に残す項目:

- SS5 gateのreviewed all-writer census、raw writer zero、D0-vs-gateway parityをpreconditionとして再確認し、
  §6.2のhuman census/test/evidence reviewを完了する。
- §6.1の実`ProofAttemptKernel<FullySealedLayout>`からper-round witnessを発行し、それをconsumeした
  `RoundReuseSlot::sealed`だけをproduction round factoryへ接続する。gateway completed `ProofStructuralSnapshotId`へ
  checked/memo/override/cycle reusable stateをbindし、D0 snapshotをreuse keyにしない。
- same attempt/same gateway snapshotのseparate query invocation間でcross-target reuseを再有効化する。snapshot change時は
  terminal failureを除くsuccess-only stateをclear/rebindし、foreign attemptはtyped rejectionする。
- one-scope ephemeral sharingとcross-scope sealed reuseを別counterで計測し、SS2〜SS5のalways-miss modeが残らないこと、
  かつlegacy/D0 authorityへ戻らないことを確認する。
- §3.6のfallible `try_enter`を全record/constraint/root recursionへ実装し、checked-count bulk reservation依存を除去する。
- `CpkPublicationEvaluationRound::eval_record`相当とproduction publication callerを`Result`伝播へ変える。
- `record_overrides` / `root_overrides` constructor/insertionをfallibleにする。
- authenticated projection/publication scope-construction failureをcommon failure branchへ流し、round/machine terminal orderingを
  allocator-failure fixtureで実証する。
- private cache portとowned success candidate publicationをHRTB wrapperへ結合する。lookup/publishはshadow計測だけで、
  validationをskipしない。
- cache-hit-equivalentなsmall/empty checked closure、publication evaluator allocation failure、cycle+failure、terminal
  latch後port rejectionを実データで検証する。
- scope-entry count、getter/cursor count、owned conversion、fallible insertion、cache shadowのwall/RSS overheadをRMW/stdで
  測定する。

SS6のproduction cutover orderingはatomicとする。capacity reservation、publication `Result` propagation、override
fallibility、terminal-latch ordering、candidate discard、allocator-failure fixtureを`SealingIncomplete` modeのまま先に
landing/greenにする。これらと§6.1 compile gate、§6.2 human gateが全てgreenになるまでproduction round factoryは
`RoundReuseSlot::sealed`を一件も呼ばない。最後のreviewed activation changeだけが
`ProofAttemptKernel<FullySealedLayout>::issue_round_reuse_witness`をfactoryへ接続する。SS6途中の個別commitを
「Sealed reuseだけ先にlandingした部分完成」としてmerge/cutoverせず、SS6全体を一つのauthority gate・rollback単位として
扱う。

Revised gate:

- 親設計旧SS6 gateのうち、allocator fallibility、common failure branch、publication stop、terminal latch、cache shadow、
  performanceに関する項目を全て維持する。
- SS1-RF/SS2で成立済みのvisibility/lifetime/foreign-attempt/owned-result gateをreal sealed data上でも再実行し、regression
  zeroを確認する。
- SS5完了後の`ScopedQueryView`にlegacy read source zero、D0 binding source zero、raw borrowed result zeroである。
- §6.2 censusのcache-relevant field/input/writer/callerにunassigned row zero、unexplained closure capture zeroであり、
  七callerのforced-canonical/fault-injection matrixとClaude reviewが完了している。
- one owned roundでtarget A→scope exit→target Bを評価し、same gateway snapshotならBがAのchecked/memoをreal hitする。
  A/B間のChanged gateway commit variantはsuccess-only stateをclearし、old hit zeroである。
- `RoundReuseSlot::sealed` construction pathは§6.1 witnessをconsumeするSS6 machine/kernel factoryだけであり、
  named family ownerがmissingなpartial layoutやD0/caller-supplied snapshot sourceではactivation不能である。
  列挙外legacy authorityの不在はこのcompile claimに含めず、直前bulletのhuman gateで判断する。
- cache lookup/publish traceを記録しても、persistent structural-validity cache hitによるcanonical validation skip count
  zeroである。SS6で別途有効化するsealed-snapshot checked/memo reuseとはcounterを分ける。
- SS7へ渡すcapacity/latch/candidate publication gateが全件greenである。

Revised stop condition:

- 親設計§9.3、§9.4、§9.5のstop conditionを変更しない。
- legacy ownerをconsumeせずlater kernel layoutを構築できる、partial layoutにwitness issuance methodが必要になる、
  またはproduction kernel layoutをoptional/dynamic/fallbackにする必要がある。
- §6.2 censusにunassigned row、説明不能なexternal capture、fault-injectionで検出できないstale reuseが残る、
  またはD0 censusを単独のcross-scope reuse correctness authorityへ再採用する必要がある。
- fallible evaluator/override pathを既存whole-attempt discard/error precedenceを変えずに表せない。
- cache-shadowを接続するとHRTB exclusivityを破るinterior mutabilityまたはraw view escapeが必要になる。
- cache-heavy closureでinfallible allocation、partial publication、terminal後lookup/publicationが残る。

SS6はempty/folded sliceにはしない。SS2〜SS5で一時停止したcross-scope sharingの安全な回復と、SS7のproduction cache
authority前に必要なallocation/failure/candidate-publication hardeningを独立review/rollback単位として残す。

## 7. Supersession boundary

本書の承認後、親設計§7の次だけを置換する。

1. SS1とSS2の間へSS1-RFを挿入する。
2. SS2本体より前へSS2-P0 caller/batch inventory・performance checkpointを置く。
3. SS2へproduction HRTB proof-read、lifetime-free round control、owned result cutoverを追加し、SS2〜SS5の
   cross-scope success reuseをoffにする。
4. SS2〜SS5へfamilyごとのscope-private legacy read source retirementとvalue-consuming kernel layout transitionを追加する。
5. SS6を§6のfully-sealed-layout best-effort witness + human census/test gate +
   sealed-snapshot reuse activation + closeout sliceへ縮小する。

変更しないもの:

- 親設計§3のfinal architecture。exact visibilityは§2.1.1に列挙するprojection-side cross-sibling surfaceだけ
  `pub(crate)`に正確化し、それ以外は親設計の範囲を変更しない。
- sealed gateway、closed mutation vocabulary、conservative Changed default、private `Unchanged` proof allowlist。
- semantic base、domain-typed reservation token、closed publication plan、panic-free publication、receipt authority。
- CPK-SV-A/B/Cのcertificate/order/stable obligation/late binding/support-ledger/canonical fallback/error precedence。
- invariants 37〜78の要求結果。rev.5はその成立をtypestate単独で証明したという主張を撤回し、§6.2の
  human census/test/reviewを追加の判定手段にする。
- §9の全stop condition。
- SS0/SS1の完了判定、SS7以降のcache cutover/performance/allowlist計画。
- production cache hitはSS7までoffというauthority boundary。

## 8. Invariant / stop-condition consistency check

本addendumは新しいinvariant番号を追加しない。resequenceが既存要求を満たす対応は次のとおりである。

| Existing rule | Resequencingでの維持方法 |
|---|---|
| 37 sealed ownership | 各familyのwrite authorityはSS2〜SS5で一回だけcutoverし、old kernel layoutと列挙済みの実legacy owner valueをconsumeする。`ProofAttemptKernel<FullySealedLayout>`はその五family ownerを所有するstructural guardとなるが、列挙外authorityの不在は§6.2 census/test/reviewで判定する |
| 38 sealed read surface | SS2 proof cutover時点からproduction proof readをHRTB scopeへ限定し、persistent interim viewを作らない。facade外helper/closure captureの不在は§6.2 mandatory-read censusへ含める |
| 39 closed vocabulary | command/payload vocabularyとdispatchは変更しない |
| 51 terminal latch precedence | SS1-RFでexact wrapper orderingを先に固定し、SS2でproduction callerをそのwrapperへ移す |
| 52 committed receipt authority | read scopeはreceipt publication authorityを持たず、SS2 proof writesは従来gateを維持する |
| 53 no partial-sealing cache authority | SS1-RF〜SS5はcross-scope checked/memo reuseもcache hitもoff。SS6も§6.1 structural guard、§6.2 human census/test/review、capacity、latch、failure propagation、candidate discardの全gateがgreenになるまでは`SealingIncomplete`を維持し、最後のatomic gateでだけ`Sealed` reuseを有効化する。SS6中の早期activationを部分landingとして認めない。persistent validity-cache hitはSS7までoff |
| 55 CPK-SV-A/B/C preservation | recursive/late-bound readと共有target batchをsingle exclusive query scope内で行い、formula/claim/move semanticsを変えない |
| 63 snapshot/conflict separation | SS2〜SS5はD0 snapshotをround reuseにもprepared base/conflictにも使わない。SS6のround bindingはwitnessがborrowするgateway authorityからcompleted snapshotを導出し、raw/D0 snapshotを別引数で受け取らない。gateway completed snapshotもreuse identityだけでconflict baseにしない |
| 66 Rust privacy | P0 legacy-only sourceとpartial read sourceはprivate access/read_view internalsだけに置く。§2.1.1の`pub(crate)`例外はopaque projection round/scope/completionの型名と必要safe methodだけで、`structural_kernel`、layout field/constructor、family/raw storage/mutator、capability、candidate internalsのvisibilityは広げない |
| 67 active-attempt closure | queryはSS1-RFの`&mut ProofAttemptKernel` HRTB wrapperだけから到達する |
| 68 publication failure | SS6 closeoutで従来どおりtyped `Result` propagationをlandingし、SS7前gateを維持する |
| 69 prepared lifetime | read resequenceはpreparation arena/guard lifetimeを変更しない |
| 70 pinned-empty transparency | proof getterはSS2からsealed semantic cursorを使い、pinの物理状態をsemantic resultへ漏らさない |
| 72 panic-free publication | SS2のclosed proof publication-plan gateを一切縮小しない |
| 73 HRTB lifetime closure | SS1-RFでcompiler gateを先行し、SS2からreal readへ適用する |
| 75 lifetime-free round persistence | SS2〜SS5は意図的なtransition narrowingとしてround-persistent stateをattempt identityとprojection terminal controlだけへ限定し、success-derived checked/memo/override/cycle payloadを保持しない。current sharingはone immutable scope内で維持する。親invariantのfull cross-scope owned-state complianceは、SS6 atomic gateが§6.1 witnessをconsumeし、§6.2 human gateも完了してsealed snapshot-bound reuseを回復した時点で再開する。witness単独をexhaustive sealing proofとは扱わない |
| 76 exact visibility/type shape | cross-sibling production callerを持つprojection-side列挙はwrapperとsignature typeを同effective visibilityのexact `pub(crate)`にし、`constraints` rootから必要型だけre-exportする。safe methodはlegacy/final両facadeの`complete`、legacyの`scheme_projectable_lowers_in_scope`、legacy/final両方の`pos_var_in_scope`と本節で明示した目的別helperだけに限定する。publication-sideはexact `pub(in crate::constraints)`を維持する。両帯ともfield/constructor/cache portはprivate、`&TypeArena` split borrowはexplicitのままとする |
| 77 owned result boundary | proof read cutoverと同じSS2でborrowed resultをowned化する |
| 78 closed multi-container publication | original SS2〜SS5 gateを維持する |

§9との照合では、新順序によりstop conditionを回避・緩和する箇所はない。特に§9.1(9)(10)、§9.3(21)(22)(30の
subconditions)、§9.4(31)(32)(36)、§9.6(62)(68)(70)をSS1-RF/SS2の明示stopとして前倒しする。

## 9. Claude独立査読 checklist

Claude (Sonnet 5) は少なくとも次を反証する。

1. SS1-RFがproduction proof read/write/cache authorityへ触れていないか。
2. SS2でproof write authorityだけ先に移り、production readerがlegacy `ProofOccurrenceStore`へ残るwindowがないか。
3. `PartialSealingReadSources`がpersistent view、round field、public trait authority、runtime fallbackになっていないか。
4. SS2〜SS5の各family factにold/new read authorityが同時に存在しないか。
5. SS2〜SS5でD0 snapshotがchecked/memo reuse、cache、validation skipのauthorityへ一件でも使われていないか。
6. `SealingIncomplete` roundがscope間でsuccess-derived checked/memo/override/cycle stateを保存・hitできない構造か。
7. SS2-P0 inventoryが§4.0.2の七production ownerをactual codeで再確認し、`scheme_projection_record_is_included`の
   per-call round construction、`publish_projection_inclusion_snapshot` loop、bounds clause-link mutation前後の
   subrow 7-a/7-bを割り当て、multi-owner regression testをproduction rowと誤数せず、row 1 subrow 1-a〜1-dの
   witness/input-formatting cascadeも割り当て、その他callerを含むunassigned row zeroになっているか。
8. 各callerのHRTB boundaryがinner methodではなくcurrent round ownerまでhoistされ、target-local facade/referenceを
   roundへ保存せずone-scope ephemeral stateだけでsharing parityを維持しているか。
9. SS2-P0のmatched-target raw-hit低下exactly zero、1.0 percentage-point aggregate hit-rate、5.0% wall/RSS
   thresholdをproof migration前に実測し、A/A noiseと分離し、failureを後続sliceへ繰り延べていないか。
10. 各family transitionがactual old kernel layoutと列挙済みのactual `Legacy*Owner`をby-value consumeし、later
    layoutのdirect/empty/ZST constructorがないか。同時に、これを列挙外legacy authorityの不在proofと誤って扱っていないか。
11. 正規`FullySealedReadInputs`が`ProofAttemptKernel<FullySealedLayout>`以外から作れず、canonical view inputの
    変更がlayout/read-input choke pointへ現れるか。さらにfacade外helper/closure captureは別途§6.2 censusへ全件載っているか。
12. `ProofAttemptKernel<FullySealedLayout>`が実の五family ownerをnon-optionalに持ち、partial layoutから
    round witnessをissueできないか。
13. `RoundReuseState` inner enumが`access/sealing.rs` privateで、access/family/testはwitness-bound
    `RoundReuseSlot::sealed`以外からsealed modeを作れないか。
14. SS6 capacity/latch/failure/candidate hardeningと§6.2 human gateが全てgreenになる前にproduction factoryへwitness
    issuanceを接続していないか。
15. recursive validationとCPK-SV-C late-bound traversalがnested HRTB scopeを必要としていないか。
16. `SchemeProjectableLower`その他scope外resultにborrowed structural fieldが残っていないか。
17. revised SS6にSS7前必須のcapacity/failure/latch/cache-candidate gateが全て残っているか。
18. invariants 37〜78または§9 stop conditionを、新しいslice名を理由に弱めていないか。
19. SS7 production cache authorityの開始条件が親設計rev.9から変わっていないか。
20. P0 production evaluationが§4.0.1のlegacy-only HRTB routeから100%のfactsを得ており、shadow
    `StructuralData`、old `&ConstraintMachine` reborrow、persistent legacy viewのどれにも依存していないか。
21. §4.0.1.1のreal ownership cascadeが、fresh `SourceTextAnalysis` / `PolyCheckOutput`から
    `InferArena::constraints_mut()`まで実装され、hover/member completion/local generalizationに加え、
    `lowering/expr/tail.rs`と`analysis/session/instantiate.rs`のwitness capture、`check.rs` input formatterを経る
    completion/hover entryがshared whole-check borrowを残さずコンパイル・parity greenになっているか。
22. SS2でP0-only scope/delegate/read-source typeが全て削除され、proof read/write cutoverとのwindowがないか。
23. proof、bounds、constraints/replay、rows、identitiesの各layout transitionがSS0で列挙した実owner rowを
    consumeし、複数field familyにZST代用やoptional escapeが入っていないか。そのzero-unassigned判定が
    compiler proofではなく§6.2 reviewed censusとして提出されているか。
24. partial layoutのwitness issuance、removed legacy field access、later-layout direct constructionがそれぞれreal
    compile-fail gateで固定されているか。
25. §6.2 censusが`ConstraintMachine`全field、nested container、external capture、全semantic getter/cursor、
    七callerを覆い、`unweighted_row_reduction_records`相当のfieldをaggregate外へ残すfaultを検出できるか。
26. 七caller × applicable familyのforced-canonical comparisonとfault-injection sensitivityが提示され、実施不能rowの
    理由と代替injectionが明記され、Claude review前に`Sealed` activationされていないか。
27. `RoundReuseSlot::sealed`がraw snapshot引数を持たず、`AllFamiliesSealedWitness::into_round_binding`が
    borrow中のgateway authorityからcompleted snapshotを導出しており、D0/foreign/caller-supplied snapshotと
    witnessを組み合わせられないか。
28. row 1の各top-level witness captureとinput-type formatが一bounded HRTB invocationでcollector traversal全体を包み、
    `WitnessCollector` / scheme-mode `CompactCollector` / scope-local facade/referenceをclosure外へ保存せず、inner targetごとの
    scope再entryまたはpersistent cross-call facadeへ退行していないか。
29. P0でborrowed `SchemeProjectableLower<'query>` vector/iteratorがscope外resultへ現れず、higher-level owned outputへ
    scope内変換され、`SchemeProjectableLower`自身のowned conversionをSS2より前へ無断で移していないか。
30. row 7 subrow 7-aのscopeがclause-link write前にdropし、7-bがwrite後にfresh scopeへ入り、current inclusionとrow 4の
    dependent-record evaluationを同じscope-local evaluatorで行い、scope drop後だけdefer/publicationしているか。
31. `pub(crate)`へ広げたitemが§2.1.1のprojection-side列挙だけで、safe accessorがlegacy/final両facadeの
    `pos_var_in_scope(PosId) -> Option<TypeVar>`を含む一方、publication-side、`structural_kernel`自体、
    `ScopedQueryView` / `LegacyOnlyQueryView` / `ImmutableTypeShapeView`、legacy/raw source/storage、capability、
    candidate internalsへ広がっていないか。
32. `constraints` rootの`pub(crate) use structural_kernel::{...}`が必要なprojection round/scope/completion typeだけを
    re-exportし、fields/constructorsのexternal struct-literal構築とscope/completion偽造がcompile-failのままか。

---

著者: Codex gpt-5.6-sol（xhigh）が起案、Claude (Sonnet 5) が独立査読・確定

状態: ドラフト、Claude査読待ち、ユーザ未承認

## 2026-08-15 追記（改訂）: row 4 / row 7 Phase A/B failure boundary

本節は同日の先行草案「row 4 / row 7 Phase A/B pending-receipt propagation」を置き換える。
先行草案は独立査読でNOT SOUNDと判定されたため撤回する。指摘されたHIGH 4件は、pendingを`let _ =`や
early `?`でsilent dropできること、event-local性をRustの型で保証できないこと、persistent
`TerminalLatchBusy`に対するretry loopに合法な終了経路がなくsolver全体を停止し得ること、pre-event query時点で
enclosing admissionが既に別のside effectをcommit済みの場合を見落としたこと、である。本改訂ではpending receipt、
retry loop、cross-call ownership propagationを一切導入しない。

### 問題

SS2-P0 row 4の`apply_scheme_projection_mutation`とrow 7のclause-link/index cascadeは、どちらも
pre-commit inclusionを読んだ後、実のstructural mutationをPhase Aで無条件commitし、その後にfresh scopeで
post-commit inclusionとdependent-record publicationを評価する。Phase B queryはこのHRTB migrationによって初めて
fallibleになる。pre-migrationの同じ位置はlegacy `proof_store`へのdirect readであり、access denialやretryという
production contractを持っていなかった。

Phase A後のfailureを通常のretryable denialとして返すと、commit済みmutationに対応するpublicationを失う。
一方、失敗を保持してretryする先行草案は上記四経路を閉じられない。従って、不可逆commit後のPhase Bだけに
局所化したconservative failure boundaryが必要である。

### 決定: post-commit Phase B failureはvariantを問わずattempt-terminal

row 4の直接entryとrow 7 subrow 7-bでは、Phase A commit後に開くPhase B queryが返す
**すべての**`ProofFailure`をattempt-terminalとする。`TerminalLatchBusy`と`ForeignAttemptRoundState`を含み、
`failure.requires_attempt_terminal()`の値はこの二つのpost-commit boundaryでは参照しない。

この局所規則は`ProofFailure::requires_attempt_terminal()`の一般分類を変更しない。同methodは、不可逆commit前で
安全かつ安価なretry pathを持つcaller向けのdefault classificationとして維持する。row 3や通常のpre-commit queryでは、
既存どおり`false`のfailureをsticky terminalへ格上げしない。row 4 / row 7 Phase Bだけは、既にauthoritative mutationが
commit済みであり、安全なretry ownership protocolが存在しないため、call-site-specificにattempt terminalへ昇格する。

これは既存retry contractの削除ではない。Phase Bのfallibility自体がP0で新設されたものであり、pre-migrationの
direct readにはfailure/retry contractがなかった。failure後に同じattemptを継続してincomplete publicationを観測可能に
するより、attempt全体をterminalにして以後のsemantic resultを不採用とする方がpre-migration robustnessに対して
conservativeである。

### 共通Phase B wrapperとscope-local evaluator

row 4とrow 7は同じpost-commit wrapperとscope-local evaluatorを使う。名称は実装時に既存命名へ合わせてよいが、
failure terminalizationをcaller任せに分散してはならない。

```rust
fn try_evaluate_record_inclusion_publication_after_commit(
    &mut self,
    lower_record: BoundRecordId,
    was_included: bool,
    metadata_changed: bool,
) -> Result<SchemeProjectionPublicationIntent, ProofFailure>;

fn evaluate_record_inclusion_publication_in_scope(
    query: &ScopedLegacyPublicationQuery<'_>,
    lower_record: BoundRecordId,
    was_included: bool,
    metadata_changed: bool,
) -> SchemeProjectionPublicationIntent;
```

outer wrapperはfresh `with_legacy_publication_query`を一回だけ開き、scope内で共通helperを呼ぶ。helperは自分でscopeを
開かず、current post-commit inclusion read、dependent-record closure、before record-result override、独立した
before/after ephemeral evaluator lane、owner dedup、owned intent constructionを一つのscope内で完了する。

outer wrapperはquery resultをcallerへ返す**前に**failure branchを処理する。`Err(failure)`ならvariant分類を問わず、
existing `mark_proof_terminal_failure` / attempt-terminal latch mechanismへ必ず記録し、その後にfailureを既存failure channelへ
伝播する。従って、上位callerが誤って`let _ = ...`、early `?`、early returnを使っても、Phase B failureがterminal化されずに
失われることはない。`Ok(intent)`だけがdefer/publishへ進める。

### row 4のflow

row 4の直接entryは次の順に固定する。

1. Phase A前にfresh `with_legacy_publication_query` scopeを開き、current evaluatorからowned
   `was_included: bool`を取得してscopeを閉じる。
2. このpre-Phase-A scopeがfailureを返した場合は、row 4 Phase A commitへ進まず、既存のcaller failure-handling contractへ
   伝播する。本追記のpost-commit special terminalizationは適用しない。enclosing admissionにそれ以前のside effectが
   ない、またはevent全体をscratchから安全にretryできる、とは仮定しない。本追記はpre-Phase-A failureへの新しい
   retry保証を追加しない。
3. pre-read成功後、`commit_scheme_projection_mutation`を一回だけ無条件に実行する。
4. fresh Phase B scopeを共通post-commit wrapperから開き、live `is_included`とdependent-record propagationを評価する。
5. success時だけowned `SchemeProjectionPublicationIntent`をdefer/publishする。failure時はwrapper内でattempt-terminalを
   latchし、publication zeroのままfailureを伝播してcurrent attemptを終了する。Phase Bをretryしない。

### row 7のflow

row 7は承認済みの7-a/7-b phase分離を維持する。

1. 7-aのfresh pre-mutation scopeでowned `was_included: bool`を取得し、scopeを閉じる。
2. 7-a failureはclause-link/dependency/index mutationへ進めず、既存のpre-commit failure contractへ伝播する。
   本追記によるautomatic retryまたはspecial terminalizationを追加しない。
3. 7-a成功後、clause-link/dependency/index mutationを一回だけ無条件にcommitする。
4. fresh 7-b scopeを共通post-commit wrapperから開く。同じscopeでcurrent inclusionとrow 4の
   `evaluate_record_inclusion_publication_in_scope`を実行し、nested query wrapperを作らない。
5. success時だけcompleted intentを`ReplayAdmissionPublicationFence`へappendまたはimmediate publishする。
   failure時はvariantを問わずwrapper内でattempt-terminalをlatchし、fence append/publication zeroのままcurrent attemptを
   終了する。7-bをretryしない。

row 4とrow 7の違いはPhase Aのcommit内容と`metadata_changed`だけである。post-commit query entry、
dependent traversal、before/after lanes、owner dedup、intent construction、failure terminalizationは共通実装にする。

### 既存invariantとの整合

1. **一般failure classificationは不変**: `TerminalLatchBusy` / `ForeignAttemptRoundState`の
   `requires_attempt_terminal() == false`は変更しない。昇格はrow 4 / row 7のpost-commit Phase B boundaryに限る。
2. **CPK-SV-C Phase A/B precedent**: authoritative structural mutationはPhase Aで無条件commitし、derived
   evaluation/publicationはPhase B successにgateする。Phase B failure時はPhase Aをrollbackまたは再実行せず、attemptを
   terminalにしてそのattemptのsemantic resultを採用しない。
3. **MPC/DPN round boundary**: pre-commit scopeとpost-commit scopeは必ずfreshとし、mutationを跨いでmemo、override、
   visiting/cycle state、reference、query facadeを保持しない。pending stateやcross-round evaluator stateを新設しない。
4. **Publication authority**: completed `SchemeProjectionPublicationIntent`だけがfence/publisherへ入る。Phase B failure時は
   publication zeroかつattempt-terminalであり、未完成intentを保存、drop、retryする状態を作らない。
5. **Scope coverage**: row 4 Phase Bとrow 7 7-bは同じscope-local evaluatorを使い、post-commit semantic readの
   direct `proof_store` fallback、nested scope、duplicated evaluator implementationを残さない。

### Gate / stop

実装gateに次を追加する。

- row 4でpre-Phase-A query failureならrow 4 Phase A commit zeroであり、既存pre-commit failure pathへ伝播すること。
- row 4でPhase A commit exactly oneの後、Phase Bへ`TerminalLatchBusy`、`ForeignAttemptRoundState`、および一つの
  proof-semantic failureを注入し、いずれもattempt-terminal latch set、publication/defer zero、retry zeroになること。
- row 7で7-a scope exit -> clause-link/dependency/index commit exactly one -> fresh 7-b scopeの順序をtraceし、7-bの
  failure variantを問わずattempt-terminal latch set、fence append/publication zero、retry zeroになること。
- 両pathのPhase B successではattempt-terminal latchを設定せず、completed intentをexactly onceだけdefer/publishすること。
- terminalizationが共通post-commit wrapper内でquery `Err`のreturn前に起き、outer callerの`let _ =`、`?`、early returnで
  bypassできないこと。
- row 4 Phase Bとrow 7 7-bが一つの`evaluate_record_inclusion_publication_in_scope` implementationを共有し、row 7が
  nested `with_legacy_publication_query`を呼ばないこと。
- rejected draftの`PendingRecordInclusionPublication`、pending failure wrapper、retry loop、cross-call pending storageの
  production symbol/referenceがzeroであること。

Phase B failure後も同じattemptを継続する必要がある、attempt-terminal latch後にcompleted intentがpublishされ得る、
またはPhase B terminalizationを共通wrapperの外へ出さなければ実装できない場合は停止する。pending保存、busy-loop、
failure分類のglobal変更、Phase A rollbackで穴埋めしない。

本追記が許可するのはrow 4 / row 7のpost-commit Phase B failureをcall-site-specificにattempt-terminalへ昇格することだけである。
他のcaller row、pre-commit failure contract、`requires_attempt_terminal()`の一般分類、SS2以降のfamily cutover、sealed gateway、
cache、snapshot、visibility、round reuse、その他の既存invariant/stop conditionを変更または緩和しない。

追記著者: Codex gpt-5.6-sol（xhigh）が起案、Claude (Sonnet 5) が独立査読・確定予定

追記状態: ドラフト、Claude査読待ち、ユーザ未承認

## 2026-08-15 追記: row 4 / row 7 Phase A/B failure boundary、二度目の却下とblocked状態

上の「2026-08-15 追記（改訂）: row 4 / row 7 Phase A/B failure boundary」節も、一切文脈を持たない
独立review（Codex gpt-5.6-sol、xhigh）でNOT SOUNDと判定された。指摘はHIGH 3件・MEDIUM 1件。

1. **HIGH**: pre-Phase-A read失敗時の「既存のpre-commit failure contractへ伝播する」という記述に対応する
   実装が存在しない。`apply_scheme_projection_mutation`は`()`を返し、row 7の該当entryは`Option`を返す
   （`Result`ではない）ため、retry ownership を保持できる形になっていない。さらに重要な点として、
   row 4のこの関数が呼ばれる時点で、同じadmission event内で**それより前に**original claim admission /
   derived claim admissionの実commitが既に起きている（`constraints/mod.rs:1634,1707`、
   `machine/bounds.rs:903,972`）。つまり「Phase A commit前は安全にscratch retryできる」という前提が、
   row 4/7で新設したPhase Aの手前だけを見ても成立しない——真の不可逆commit境界はこのaddendumが想定した
   よりも早い時点にある。
2. **HIGH**: 既存の`mark_proof_terminal_failure` / attempt-terminal latch機構は、実際には全ての下流
   消費経路を守っていない。`lower_binding_bodies`（`lowering/body/mod.rs:637`、`lowering/mod.rs:119`で
   re-export）やsingle-file dump経路（`dump.rs:57,95`）はterminal latchを検査せずに結果を消費し得る。
   「terminalizeすればそのattemptのsemantic resultは採用されない」という本節の前提は、現在の
   production API surface全体には及ばない。
3. **HIGH**: `defer_scheme_projection_mutation`（`machine/bounds.rs:1892`、production callerは
   `bounds.rs:1005,2146`）が、named entry（`apply_scheme_projection_mutation`）と全く同じ
   read→commit→evaluateの構造を持つにもかかわらず、本節の「row 4 / row 7の二箇所限定」という
   scope記述に含まれていない。
4. **MEDIUM**: `TerminalLatchBusy`は`RefCell::try_borrow()`失敗から生成される
   （`structural_kernel/access.rs:139`）が、本節が要求するterminalization自体が同じcellへの
   `borrow_mut()`を呼ぶ（`access.rs:89`）。conflicting borrowが生存中なら、これはErrを返さずpanicする。
   つまり「genuineなTerminalLatchBusyを確実に記録できる」という約束が、その机構自身と矛盾する。

**現状の評価**: 2回連続の独立reviewが、いずれも「row 4/7固有の設計ミス」というより、
このaddendumが仮定した「Phase Aという単一の無条件commit境界」自体が実際のcall graphと一致しない
——真の不可逆側面はより広い範囲（admission event全体、terminal latchの消費側網羅性、
`defer_scheme_projection_mutation`を含む複数のcaller）に及ぶ、という共通の根を指摘している。
これはCPK-SV-C redesignで経験した「severityが収束せず実質的な指摘が出続ける」パターンと同型であり、
このプロジェクトの既存の教訓（[[cpk-preflight-and-sv-c-redesign-2026-08-12-13]]）に従えば、
これは「あと一手で直る」局面ではなく、設計そのものを立ち止まって見直すべき局面と判断する。

**この場でのpending action**: row 4 / row 7のPhase A/B failure boundary設計はblockedとする。
row 4の最初の実装commit（`97c382eb`、pushされていない local-only commit、独立reviewでHIGH 1件・
MEDIUM 2件が未修正のまま残っている）はそのまま保持し、破棄しない——共有evaluator helperや
scope構造など、設計が確定すれば再利用できる部分を含むため。row 5〜7の着手も、row 4の
failure-boundary設計が row 7 と共通することを踏まえてこの節が解決するまで見合わせる。

次に着手する際は、狭い「row 4/7だけの局所修正」ではなく、次を最初に調査するところから始めるべきと考える。
(a) このadmission eventの本当の不可逆commit境界はどこか（original claim / derived claim commitまで
遡る必要があるか）、(b) attempt-terminal latchが実際に守るべき消費経路の全量棚卸し（`lower_binding_bodies`
やdump系列を含む）、(c) `defer_scheme_projection_mutation`を含めた完全なcaller inventory。
これは新しい正本文書として起案するに値する規模であり、既存addendumへの追記では収まらない可能性がある。

記録状態: 2026-08-15、ユーザは就寝中のため確認を求めず、既存の「質問なくpushしながら続けてOK」という
標準承認の範囲内でこの規模の新規architecture判断まで進めるべきではないと判断し、ここで区切った。

## 2026-08-15 追記（三度目）: row 4 / row 7はrow 3の既存idiomをそのまま転用する

本節は、二度目の却下後に行ったactual call graphとgateway failure contractの調査結果に基づく。
新しいpending ownership protocol、call-site-specific terminal escalation、retry loop、terminal latch書き込み
mechanismは追加しない。row 4 / row 7は、既にmerge済みで独立査読greenのrow 3が使っている
failure-handling idiomと同じclassification branchを、post-commit queryのcaller boundaryでそのまま使う。

### 調査で確定した既存contract

`with_legacy_projection_query` / `with_legacy_publication_query`はgateway内のquery closureまたは
scope constructionから`Err(failure)`を受けたとき、次の既存branchを通る。

```rust
if failure.requires_attempt_terminal() {
    self.mark_terminal_failure(
        ProofOperation::ProjectLowerEvaluation,
        failure.clone(),
    );
}
Err(failure)
```

したがって、`requires_attempt_terminal() == true`のproof-semantic failureはgatewayから返る時点で
attempt terminal latchは既にset済みである。一方、access-layer denialである
`TerminalLatchBusy`と`ForeignAttemptRoundState`は`requires_attempt_terminal() == false`であり、gatewayはこれらを
deliberately latchしない。pre-authenticationの`ensure_query_kernel_active` / `authenticate_round`が返すdenialも、
query-result共通branchより前に返るためautomatic latchの対象にならない。

row 3の既存`insert_scheme_projection_live_coverage_state` /
`remove_scheme_projection_live_coverage_state`は、fallible queryをauthoritative commitより前に行う
`try_update_scheme_projection_live_coverage`の`Result`を受け、denial時に次のidiomを使う。

```rust
Err(failure) => {
    if failure.requires_attempt_terminal() {
        self.mark_proof_terminal_failure(
            proof::ProofOperation::UpdateClaimLifecycle,
            failure,
        );
    }
    false
}
```

このcaller branchはgatewayと同じclassificationを尊重する。proof-semantic failureはterminalのままであり、
`TerminalLatchBusy` / `ForeignAttemptRoundState`を新たにsticky terminalへ格上げしない。その後、このcaller自身は
failureを`false`へ畳み込み、そのoperationをno-opとして終了する。

### 決定: pre-commitは`Result`で防ぎ、post-commitはrow 3 idiomでno-opに畳み込む

この決定は、row 4の直接entryである`apply_scheme_projection_mutation`だけでなく、row 7の
clause-link/index cascadeと、同じread -> commit -> read/evaluate構造を持つ
`defer_scheme_projection_mutation`も明示的に対象とする。

#### 1. pre-commit read

`was_included`の読み取りは、fresh `with_legacy_publication_query`を一回だけ開いてowned `bool`へ
畳み込み、scopeを閉じる。このscopeがdenialを返した場合、Phase A commitはzeroとする。

これを実現するため、`apply_scheme_projection_mutation` / `defer_scheme_projection_mutation`と、
row 7 subrow 7-aのpre-readをownする必要最小限のcaller chainは`Result<_, ProofFailure>`を返す。
pre-commit denialは`?`で上位のfailure boundaryへ伝播する。これは新しいfailure categoryや
recovery protocolではなく、既存gatewayとrow 3の`try_*` helperが使う`Result<_, ProofFailure>`
signatureをcaller chainへ機械的にthreadする変更である。

#### 2. authoritative commit

pre-commit readが成功した後だけ、対象のauthoritative structural mutationを一回だけ無条件にcommitする。

- row 4の直接entryと`defer_scheme_projection_mutation`: `commit_scheme_projection_mutation`
- row 7: clause-link / dependency / index mutation

このcommitにrollback、prepared overlay、pending receiptを追加しない。

#### 3. post-commit read + dependent evaluation

commit後にfresh `with_legacy_publication_query` scopeを開く。このscope内でlive `is_included`を読み、
Phase A前のowned `was_included`をbefore laneのrecord-result overrideに使い、before/afterの独立ephemeral laneで
dependent-record traversalを完了する。scopeから返すのはowned
`SchemeProjectionPublicationIntent`だけとする。

row 4の直接entry、`defer_scheme_projection_mutation`、row 7 subrow 7-bは、同じ
`evaluate_record_inclusion_publication_in_scope`相当のscope-local helperを使う。row 7は7-bのouter scope内からこの
helperを呼び、nested gateway scopeを開かない。

#### 4. post-commit denial

post-commit scopeが`Err(failure)`を返した場合、各callerはrow 3と同一のbranchを使う。

```rust
if failure.requires_attempt_terminal() {
    self.mark_proof_terminal_failure(
        proof::ProofOperation::ProjectLowerEvaluation,
        failure,
    );
}
```

その後、completed intentを作らず、publication / fence append / deferを行わず、そのcaller operationを
no-opとして終了する。post-commit denialはこのcallerからさらに`Err`として返さず、
`apply_scheme_projection_mutation`は`Ok(())`、`defer_scheme_projection_mutation`とrow 7の該当operationも各自の
success/no-op値へ畳み込む。この後半はrow 3のinsert/remove callerが`Err`を`false`へ畳み込む形と同じである。

`TerminalLatchBusy` / `ForeignAttemptRoundState`は`requires_attempt_terminal() == false`のため、
`mark_proof_terminal_failure`は呼ばれない。proof-semantic failureは同methodが`true`を返すため、
gatewayのautomatic latchに加えてcallerもrow 3と同じclassification checkを通す。新しいterminal escalation規則はない。

### 二度目案の査読指摘への対応

1. **pre-commit failure contractが存在しない**: 存在しないcontractに依存せず、
   `apply_scheme_projection_mutation` / `defer_scheme_projection_mutation`と必要caller chainを
   `Result<_, ProofFailure>`へ機械的に変更し、pre-commit denialを`?`で伝播することを明記した。
2. **terminal latchが全downstream consumerをgateしない**: 追加調査により、
   `lower_binding_bodies`とsingle-file `dump.rs`経路は未checkだが、現在のin-repo production callerはzeroであること、
   actual production entryは`lower_loaded_files*`とその上位経路でterminal latchをcheckすることを確認した。
   これはrow 3の既に承認されたfailure idiomにも存在するpre-existingかつ直交するgapであり、
   row 4 / row 7 migrationで新たに修正または拡大しない。
3. **`defer_scheme_projection_mutation`が未網羅**: 本節のpre-read、commit、post-read/evaluate、
   denial/no-opの全flowに明示的に含めた。
4. **`TerminalLatchBusy`をmarkする際の`RefCell` borrow conflict**: `TerminalLatchBusy`は
   `requires_attempt_terminal() == false`であり、row 3と同じbranchでは
   `mark_proof_terminal_failure`呼び出しへ到達しない。従って同cellへの新しい`borrow_mut()` pathは生じず、
   二度目案のpanic riskをconstructionで持ち込まない。

### 残るtradeoffと適用範囲

post-commit Phase Bが`TerminalLatchBusy` / `ForeignAttemptRoundState`のようなnon-terminal failureでdenyされた場合、
Phase Aのauthoritative commitは残るが、そのadmission eventに対するderived publication / dependent-record propagationは
そのroundでは行われない。これは意図的なgraceful degradationであり、silent corruptionとは扱わない。
authoritative proof/support/clause/index mutation自体は既存commit contractに従って完了し、half-commitにはならない。
欠落するのは後続のderived publication signalであり、authoritative store自体を別の値へ書き戻したり
不完全なintentをpublishしたりしない。

調査では、同じadmission eventのconstraint / bound / original claim / derived claim / row reduction /
qualified-parent admissionにもrollbackのないcommit pointが複数あり、それらのcommit後には現在fallible queryも
rollback pathもないことが確定した。row 4 / row 7の新しくfallibleになる特定readにだけ、
classification済みfailureをterminal latchまたはno-opに畳み込む経路を与えることは、同call chainのその他の
commit pointが持つ「failure handling zero」に比べて厳しくなることはあっても、新しい不安定性を加えるものではない。

現行production call graphでは、fresh same-machine roundへのforeign-attempt denialは正常経路で生じず、
`TerminalLatchBusy`も主にfailure injectionで観測する防御経路である。ただし、これを「不可達」とは主張しない。
上記のnon-terminal denial tradeoffを明示した上で、fault injection gateで振る舞いを固定する。
本節で新規に承認が必要なpolicy判断は、このpost-commit non-terminal denialをpublication zeroのno-opとし、
authoritative commitを保持するgraceful degradationだけである。branch自体はrow 3と同一だが、
commit後に適用することの意味はrow 3から自動的に導かれるものではなく、本追記の査読対象とする。

本追記が承認するのは、row 4 / row 7 / `defer_scheme_projection_mutation`に既存row 3 idiomを
適用するためのResult signature threadingとscope relocationだけである。他のcaller row、family authority、sealed reuse、
snapshot、cache、visibility、terminal classification、その他の既存invariantを再開または緩和しない。

### 既存invariantとの整合

1. **failure classificationは不変**: `ProofFailure::requires_attempt_terminal()`の定義と各variantの分類は変更しない。
   gatewayとcallerはrow 3と同じbranchを使う。
2. **pre-commit denialはcommitを防ぐ**: pre-readの`Result`を`?`で伝播し、denialの後に対応する
   Phase A commitを実行しない。enclosing eventがそれ以前にcommitした状態へのrollbackは約束しない。
3. **commitをscope間に置く**: pre-scopeをdropしてからcommitし、commit後にfresh post-scopeを開く。
   mutationを跨いでmemo、override、visiting/cycle state、reference、facadeを保持しない。
4. **publicationはcompleted intentだけ**: post-scope successが返したowned intentだけをpublish / defer / fence appendする。
   denial時はこれらを全てzeroとする。
5. **single scope-local evaluator**: row 4の直接entry、`defer_scheme_projection_mutation`、row 7 subrow 7-bは
   同じscope-local helperを使い、nested scope、direct `proof_store` fallback、duplicated evaluator logicを残さない。
6. **no persistent retry machinery**: pending receipt、retry ownership、retry loop、cross-call pending state、
   call-site-specific attempt-terminal overrideを作らない。

### Gate / stop

実装gateに次を追加する。

- row 4の直接entry、`defer_scheme_projection_mutation`、row 7 subrow 7-aのそれぞれで、pre-commit queryに
  failureを注入すると`Result::Err`が上位へ伝播し、対応するPhase A commit、publication、defer、fence appendが
  全てzeroになること。
- pre-commit success後のPhase A commitがexactly onceかつ無条件で、post-scope resultによってrollbackまたは
  二重実行されないこと。
- 三pathのpost-commit scopeにproof-semantic failureを注入すると、row 3と同じ
  `requires_attempt_terminal()`-gated branchが通り、attempt latch set、publication / defer / fence append zeroになること。
- 三pathのpost-commit scopeに`TerminalLatchBusy`と`ForeignAttemptRoundState`を注入すると、
  `mark_proof_terminal_failure`に到達せず、panic zero、publication / defer / fence append zero、caller operationがno-opとして
  終了すること。
- post-commit success時はcompleted `SchemeProjectionPublicationIntent`をexactly onceだけpublish / defer / fence appendし、
  pre/postのactual inclusionとdependent owner setがpre-migrationと一致すること。
- row 4直接entry、`defer_scheme_projection_mutation`、row 7 subrow 7-bが一つの
  `evaluate_record_inclusion_publication_in_scope`相当implementationを共有し、nested gateway scope zeroであること。
- `PendingRecordInclusionPublication`相当型、pending failure wrapper、retry loop、cross-call pending storage、
  Phase B専用terminal escalation branchのproduction symbol/referenceがzeroであること。

pre-commit denialを`Result`で伝播できない、post-commit no-opの後に同期admission eventがcompleted publicationを
必須とする不変条件を破る、authoritative store自体がhalf-commitまたは内部矛盾になる、またはrow 3の
existing branch以外のfailure machineryが必要となる場合は停止する。pending state、retry loop、
call-site-specific terminal escalation、global failure reclassificationで穴埋めしない。

追記著者: Codex gpt-5.6-sol（xhigh）が起案、Claude (Sonnet 5) が独立査読・確定予定

追記状態: ドラフト、Claude査読待ち、ユーザ未承認

## 2026-08-15 追記: 三度目も却下、構造的ジレンマの発見

上の「三度目」節も、一切文脈を持たない独立review（Codex gpt-5.6-sol、xhigh）でNOT SOUNDと判定された。
指摘はHIGH 4件・MEDIUM 1件。最も重要なのはHIGH #1・#2で、今回は前2回と質が異なる——実装の詰めの甘さでは
なく、この節の核心である「post-commit denial時、authoritative commitは残すがpublicationはこのroundでは
行わない」という graceful degradation の前提そのものを否定した。

`SchemeProjectionPublicationIntent::OwnersChanged` は単なる通知ではなく、owner の `ConstraintBounds`
mutation journal 発行・global `ConstraintEpoch` 進行・owner の `VarBounds::epoch` 進行・provenance epoch
進行を同期的に行う（`constraints/mod.rs:1988,2072`）。下流の method-role pass や owner-dirty scheduler は
この epoch の不変を「mutation が無かった証明」として使い、cached 結果を再利用する
（`constraints/mod.rs:194`、`analysis/session/selection.rs:217`、`analysis/session/lifecycle.rs:720`、
`analysis/session/owner_dirty_scheduler.rs:21,585`）。つまり publication は best-effort な信号ではなく、
correctness-sensitive な invalidation そのものであり、それを一度でも飛ばすと silent stale-reuse になる。
さらに、一度飛ばされた `was_included` は再admissionでは復元できない（`metadata_would_change == false`なら
`Ok(None)`、`proof/mod.rs:5805`）ため、「後で同じrecordに触れれば自然に直る」という前提も成立しない
（永久stale化のリスク）。row 7ではさらに、`ReplayAdmissionPublicationFence`が単純なvectorであるため、
denyされたintentだけがno-op化されても同じeventの他のintentは通常どおりpublishされてしまう
——event-level atomic publicationではなく部分publicationになる（HIGH #3）。

**この3回の却下を並べると、単なる実装の詰めが甘いという話を超えた構造的ジレンマが見える**。

1. pending receipt方式（retry） → NOT SOUND（Rustの所有権はaffineでlinearでないためsilent dropを防げない、
   `TerminalLatchBusy`が持続すると合法な終了経路が無くsolver全体を停止しうる）
2. どんな失敗もattempt-terminalへ昇格 → NOT SOUND（`TerminalLatchBusy`は`try_borrow()`失敗から生成される
   一方、terminal化は同じcellへの`borrow_mut()`を要求するため、conflicting borrowが生存中ならpanicしうる）
3. row3の既存idiom（no-op skip）を転用 → NOT SOUND（publicationのskip自体がcorrectness-sensitiveな
   状態更新を飛ばすことになり、stale-reuseを生む）

3つの設計が別々の理由で落ちているが、突き詰めると同一のジレンマに帰着する。post-commit Phase Bが
`TerminalLatchBusy`のようなnon-terminal-classified failureで拒否されたとき、**terminal latchへ書こうとすれば
その原因と同じborrow conflictでpanicしうる。書かなければ、publicationという correctness-sensitive な
state更新が silent に失われる。** この二択のどちらも安全ではない。これはrow 4/7固有の実装上の見落としでは
なく、「commit後のfallible readにHRTB query gatewayを使う」というこの migrationのアーキテクチャ自体が
内包する緊張だと考えられる。

**現状の評価**: これはCPK-SV-C redesign（[[cpk-preflight-and-sv-c-redesign-2026-08-12-13]]）で経験した
「severityが収束せず実質的な指摘が出続ける」パターンと同型だが、今回はさらに一段深い——次に必要なのは
「4度目の局所設計案」ではなく、上記ジレンマそのものの解消方針（例えば`TerminalLatchBusy`を
`debug_assert`/panicとして扱う方向に倒し「本当に到達しない」ことをinvariantとして固定するか、
gatewayのterminal-latch記録機構自体を見直すか）という、もう一段上の判断だと考える。これは
row 4/7だけでなく、既にmergeされたrow 1〜3や、今後のfamily cutover全体にも波及しうる判断であり、
狭いaddendum追記で決めるべき重さを超えていると判断する。row 4/7のfailure-boundary設計は引き続き
blockedとし、次の一手は新しい正本文書として起案するか、少なくともこのジレンマ自体を主題とした
専用の調査・設計ラウンドとして扱うべきと考える。

## 2026-08-15 追記（四度目）: 到達可能性の実証に基づく解消

本節は、前三案のようにpost-commit failureを局所的なownershipまたはpolicyで処理する案ではない。
三度目の却下後、本節のために独立して行った二つのreachability調査が、構造的ジレンマを生んでいた二variantの
実行可能性を次のとおり確定したことを根拠とする。三度目節自身は`TerminalLatchBusy`を「主にfailure injectionで観測する
防御経路」と記す一方で「不可達とは主張しない」と明記していたため、本節は三度目節をunreachability evidenceとして
引用しない。以下のproduction-path unreachabilityは、全borrow site、guard lifetime、re-entrancy、thread / async、および
round construction / consumptionを改めて追跡した独立調査で初めて確定した。

1. `TerminalLatchBusy`は、current safe production APIからは到達不能である。唯一のorganic constructorは
   `ensure_query_kernel_active`内の`terminal_failure.try_borrow()` failureだが、同cellのborrow guardをcallback越しに
   保持するproduction APIはなく、gatewayは`&mut ConstraintMachine`をexclusiveに借用して同期的にclosureを実行する。
   query scopeからのre-entrant gateway entryも型で拒否され、thread / async yieldも存在しない。現行testの大半は
   実際の`RefCell` conflictを作らずtest-only failure slotへ`TerminalLatchBusy`を直接injectする。ただし
   `cpk_sv_d_ss1_rf_busy_terminal_latch_uses_exact_proof_failure_surface`は例外であり、test-only
   `query_latch_busy_failure_for_test`内でactual `terminal_failure.borrow_mut()` guardを保持して genuine conflictを作り、
   current implementationがtyped `Err(ProofFailure::TerminalLatchBusy)`を返すことをassertする。このtest-only direct accessが
   存在することと、safe production call graphから同じguard overlapへ到達不能であることは両立する。
2. `ForeignAttemptRoundState`はgeneral API全体では到達可能である。K1で作ったowned roundをK2へ渡すsafe API misuseを
   round型のlifetimeは防がない。一方、rows 2〜4の全production round construction siteは、同じ同期関数内で
   `self.new_*_evaluation_round()`を呼び、直後に同じ`self.with_legacy_*_query(...)`へ渡す。roundをfieldへ保存、return、
   helper parameter化、または別`self`へ転送する箇所はzeroである。row 4の直接entry、
   `defer_scheme_projection_mutation`、row 7 subrow 7-a / 7-bも、このsame-self local construction形で実装でき、
   shared helperへ渡すのはroundではなくHRTB内の`ScopedLegacyPublicationQuery`だけである。

以下の決定は、この二点を「稀だが起こりうる」という推測ではなく、current call graphとborrow lifetimeの全量調査で
確定した事実として使う。どちらかのreachability factを将来の変更が崩す場合、本節の結論も自動的に無効となり、
再査読を必要とする。

### Part 1: organic `TerminalLatchBusy`をrecoverable `ProofFailure` surfaceから除く

`ProofAttemptKernel::ensure_query_kernel_active`のterminal latch readを、次のfallible accessから

```rust
let terminal = self
    .terminal_failure
    .try_borrow()
    .map_err(|_| ProofFailure::TerminalLatchBusy)?;
```

次のinfallible accessへ変更する。

```rust
let terminal = self.terminal_failure.borrow();
```

safe production pathではconflictが到達不能であるため、正常実行のfailure setは変わらない。仮にこの調査が見落とした
re-entrancyまたは将来のunsafeなborrow lifetime拡張があれば、`RefCell::borrow()`のnative panicが即座にinvariant violationを
露呈する。recoverable `Err(TerminalLatchBusy)`としてcall stackを戻り、post-commit callerにcorrectness-sensitiveな
publicationをskipさせる経路はorganic gateway contractから消える。

これはrow 4 / row 7だけの変更ではなく、次の共有gateway全体のcontract変更である。

- `with_projection_query`
- `with_publication_projection_query`
- `with_legacy_projection_query`
- `with_legacy_publication_query`

従って、merge済みrows 1〜3を含む既存callerを再検証する。current productionの
`requires_attempt_terminal()` branchは、上の4 gateway implementation、row 3の
`insert_scheme_projection_live_coverage_state` / `remove_scheme_projection_live_coverage_state`、および未push row 4実装の
`apply_scheme_projection_mutation` / `defer_scheme_projection_mutation`に限られる。Part 1後もこれらのbranch自体は
proof-semantic failureをterminal latchへ記録するために必要であり、削除しない。organic `TerminalLatchBusy`が
`requires_attempt_terminal() == false`側へ入る可能性だけがdeadになる。row 2のようにgateway resultを上位へ返さず
gatewayのautomatic latchへ依存するcallerも、organic failureがproof-semantic terminal failureへ限定されるため、
behavioral contractを失わない。

`ProofFailure::TerminalLatchBusy` variantと`requires_attempt_terminal() == false`分類は、このsliceでは削除しない。
test-only injectionおよびdefensive classification surfaceとして残す。ただし、testの意味は次のとおり明示的に分ける。

1. `inject_query_scope_failure(ProofFailure::TerminalLatchBusy)`を使う既存retryability testは保持する。これはproductionで
   実在するrecoverable borrow conflictの再現ではなく、「到達不能と証明したvariantがtest overrideまたは将来の誤った
   closure resultから入っても、一般gateway / pre-commit row 3 callerがpanicやsticky poisoningを起こさない」という
   defensive robustness testへ改名・再説明する。assertionを緩めない。
2. `busy_terminal_latch_uses_exact_proof_failure_surface`のように、実RefCell conflictがrecoverable
   `ProofFailure::TerminalLatchBusy`になると主張するtestは、その契約がPart 1で消えるため同じ意味では残さない。
   test-only helperでactual `terminal_failure.borrow_mut()` guardを保持したまま`ensure_query_kernel_active`を呼び、
   `RefCell::borrow()`がpanicすることを`#[should_panic]`または`catch_unwind`で固定するinvariant testへ置き換える。

これはincidentalなtest adjustmentではなく、Part 1が意図的に行うcontract changeである。現行の
`cpk_sv_d_ss1_rf_busy_terminal_latch_uses_exact_proof_failure_surface`は、genuine borrow conflictのoutcomeをtyped recoverable
`Err(ProofFailure::TerminalLatchBusy)`としてassertしている。Part 1後、同じgenuine conflictのoutcomeはpanicとなる。
replacement testは「conflictを必ず検出する」という元の目的を保存する一方、assertするoutcomeをtyped `Err`からpanicへ変える。
このoutcome変更こそ、到達不能なinvariant violationをrecoverable production failureとして扱わないPart 1の目的である。

このtest整理により、synthetic defensive behaviorとorganic invariant violationを同じ「retryable production case」として
混同しない。

### Part 2: row 4 / row 7はrow 3の既存branchをpost-commit boundaryへ転用する

scopeとmutationの順序は三度目案で確定した形を維持する。本節の対象は、row 4の直接entryである
`apply_scheme_projection_mutation`、同じread -> commit -> read/evaluate形を持つ`defer_scheme_projection_mutation`、
row 7 subrow 7-a / 7-bの全てである。

1. pre-commit `was_included` readをfresh same-self `with_legacy_publication_query` scope内でowned値へ畳み込み、scopeを閉じる。
   denialは必要最小限の`Result<_, ProofFailure>` signature chainを`?`で伝播し、対象commitへ進まない。
2. pre-read success後、row 4 / deferは`commit_scheme_projection_mutation`を、row 7はclause-link / dependency / index
   mutationをexactly once commitする。rollback、pending receipt、retry ownershipを追加しない。
3. commit後、同じ`self`から作ったfresh local roundで新しい`with_legacy_publication_query` scopeを開く。同じscope内で
   live `is_included` readとdependent-record evaluationを完了し、owned `SchemeProjectionPublicationIntent`だけを返す。
   row 4、defer、row 7 subrow 7-bは一つの`evaluate_record_inclusion_publication_in_scope`相当helperを共有し、
   nested gatewayを呼ばない。
4. post-commit scopeが`Err(failure)`を返した場合、後述のreachability canaryに続けて、row 3と同じbranchをそのまま置く。

```rust
if failure.requires_attempt_terminal() {
    self.mark_proof_terminal_failure(
        proof::ProofOperation::ProjectLowerEvaluation,
        failure,
    );
}
```

completed intentがないためpublication / defer / fence appendは行わず、そのlocal operationをno-opとして閉じる。
新しいfailure wrapper、retry loop、pending state、variant reclassification、call-site-specific terminal escalationはない。

このcode shapeは三度目案と同じだが、soundnessの前提が異なる。Part 1後、real row 4 / row 7 post-commit pathへ
`TerminalLatchBusy`は返らない。`ForeignAttemptRoundState`も、fresh roundを同じ`self`でconstruct/consumeするこの三pathでは
発生しない。従って、real executionでこのbranchへ到達する`Err`は
`requires_attempt_terminal() == true`のproof-semantic failure、または既にterminal latchへ格納済みのfailureに限られる。
gatewayは前者をreturn前にautomatic latchし、callerのrow 3 branchも同じclassificationでidempotentに記録する。
先行調査では、`lower_loaded_files*`とその上位にあるactual in-repo production compiler pathsがterminal latchを必ずgateすることも
確認済みであるため、この場合はpublication skip後のresultを正常attemptとして再利用しない。この主張は全public API surfaceを
対象にしない。terminal latchをcheckしない`lower_binding_bodies`とsingle-file `dump.rs` pathはpre-existingかつ直交するsurfaceとして
残るが、current in-repo production callerはzeroである。本節はその別gapを修正済みとも、全外部callerがgate済みとも主張しない。

三度目案でliveだった「non-terminal denialをno-opへ畳み込むとcorrectness-sensitive publicationを永久に失い、
silent stale-reuseを許す」というpathは、Part 1とsame-self round localityによりreal row 4 / row 7 executionから消える。
source上の`requires_attempt_terminal() == false`側はsynthetic injectionとfuture invariant violationに対するdefensive形として
残るが、production recovery policyとしては使わない。

### Foreign round localityの残余riskとcanary

`TerminalLatchBusy`のunreachabilityはexclusive borrow構造に基づく一方、`ForeignAttemptRoundState`のrow 4 / row 7
unreachabilityはcurrent call graphの事実であり、Rust type systemによるowner bindingではない。round stateはlifetimeを持たない
owned valueなので、将来K1 construction -> K2 consumptionを行うhelper、field、return value、またはcross-self parameterが
追加されれば、本節の前提はコンパイルエラーなしで崩れる。

このdriftを黙って許さないため、row 4の直接entry、`defer_scheme_projection_mutation`、row 7 subrow 7-bの
post-commit error boundaryでは、row 3のbranchの直前に次のrelease-mode invariant canaryを置く。

```rust
assert!(
    failure.requires_attempt_terminal(),
    "row 4/7 post-commit non-terminal denial invalidates the reviewed same-machine round-locality invariant",
);
```

canary後のclassification / mark / no-op branchはrow 3と同じ構造を維持する。これは新しいterminalization logicではなく、
全build profileでreachability premiseの破壊を即座にpanicとして露呈し、査読対象へ戻すinvariant assertionである。
この`assert!`はqueryのhot success pathではなく、post-commit gatewayが既に`Err`を返したfailure pathだけで評価されるため、
通常実行のruntime costはzeroであり、failure時のboolean check costも無視できる。ここで守る対象はperformance hintではなく、
publication欠落によるsilent stale-reuseである。release buildでcanaryを消すriskは、このfailure-path-only checkのcostを上回るため、
debug-only assertionではなく、意図的に全build profileで有効な`assert!`を使う。
既存test-only failure injectionを使って各三pathへ`ForeignAttemptRoundState`を入れ、publication / defer assertionへ到達する前に
このmessageでpanicするregression testを置く。`TerminalLatchBusy` injectionも同じcanaryを通し、Part 1のorganic panic testとは
別に「post-commit boundaryではsynthetic non-terminal denialも正常no-opとして受理しない」ことを固定する。

さらに、production round construction inventoryをgateへ固定する。row 2、row 3、row 4 / defer、row 7の各siteについて、
roundがlocal variableとして同じreceiverから作られ、同じ同期関数内で同じreceiverのgatewayへ渡され、round-typed field、return、
cross-self helper parameterがzeroであることをsource censusまたは明示的review checklistで照合する。新しいproduction constructor site、
round forwarding、machine attempt resetを追加する変更は、本節の`ForeignAttemptRoundState` reachability proofを無効化するためstopし、
独立再査読を必要とする。

### 既存invariantとの整合

1. **terminal classification**: `ProofFailure::requires_attempt_terminal()`とvariant分類は変更しない。
   `TerminalLatchBusy`はsynthetic defensive surface上non-terminalのまま残る。Part 1はorganic constructorだけをpanic invariantへ変える。
2. **shared gateway scope**: Part 1はgatewayのterminal latch readだけを変え、HRTB lifetime、nonce authentication、
   SealingIncomplete、scope-local memo、post-scope recheckの順序を変えない。
3. **rows 1〜3 compatibility**: four gatewayとrow 3 callerのexisting classification branchを残す。
   organic proof-semantic failureのterminal behavior、owned result、production outputを変えない。
4. **pre/commit/post boundary**: pre-scopeをdropしてからauthoritative mutationをcommitし、commit後にfresh scopeを開く。
   reference、facade、memo、override、visiting/cycle stateをmutation越しに保持しない。
5. **publication correctness**: post-commit successで得たcompleted owned intentだけをpublish / defer / fence appendする。
   real post-commit failureはattempt terminalとなり、`lower_loaded_files*`を通るcurrent in-repo production compiler pathを
   通過しない。non-gatedだがin-repo production caller zeroの`lower_binding_bodies` / single-file dump public surfaceは
   この保証の対象外であり、本節と直交するpre-existing gapとして残る。
6. **single evaluator**: row 4直接entry、`defer_scheme_projection_mutation`、row 7 subrow 7-bは同じscope-local evaluatorを使う。
7. **no recovery machinery**: pending receipt、cross-call pending state、retry loop、call-site-specific failure wrapper、
   call-site-specific terminal escalationを作らない。release-mode invariant canaryはreachability assertionであり
   recovery pathではない。

### Gate / stop

実装gateを次のとおり置き換える。

- `ensure_query_kernel_active`が`terminal_failure.borrow()`を使い、organic pathに
  `try_borrow().map_err(|_| ProofFailure::TerminalLatchBusy)`または同等のrecoverable conversionがzeroであること。
- actual conflicting `RefCell` guardを使うtestがnative panicを確認し、test-only variant injectionをactual borrow conflictの
  evidenceとして扱わないこと。
- rows 1〜3について、structural-kernel query tests、row 2 generalization tests、row 3 liveness tests、既存constraints baselineを
  Part 1変更後に実行し、既存`requires_attempt_terminal()` branchがcompileし、semantic resultとpass/fail baselineが不変であること。
  synthetic `TerminalLatchBusy` injection testsはdefensive testへ改名・再説明した上でassertionを維持すること。
- row 4直接entry、`defer_scheme_projection_mutation`、row 7 subrow 7-aでpre-commit denialを注入すると、
  `Result::Err`が上位へ伝播し、対応するcommit、publication、defer、fence appendがzeroであること。
- pre-read success後のauthoritative commitがexactly onceであり、pre/post scopeが別invocation、別fresh local roundであること。
- row 4直接entry、defer、row 7 subrow 7-bのpost-commit error boundaryで、全build profileで有効な`assert!` canaryの直後にrow 3と同じ
  `if failure.requires_attempt_terminal() { self.mark_proof_terminal_failure(...) }` branchが同じ構造で存在すること。
- release build相当のconfigurationでも上記canaryがcompile outされず、non-terminal failure injectionが指定messageでpanicすること。
- 三つのpost-commit pathへtest-only `TerminalLatchBusy` / `ForeignAttemptRoundState`をinjectすると、canaryが指定messageでpanicし、
  publication / defer / fence appendがzeroであること。proof-semantic failureではcanaryを通過し、attempt terminal latch set、
  publication zeroとなること。
- row 4直接entry、defer、row 7 subrow 7-bが一つのscope-local evaluator implementationを共有し、nested gateway、
  direct `proof_store` fallback、duplicated dependent-record evaluatorがzeroであること。
- production round construction censusが全siteでsame-self immediate consumptionを示し、round-typed field / return /
  cross-self parameter、またはround constructionとconsumptionの間のattempt resetがzeroであること。
- pending-receipt type、retry loop、cross-call pending storage、Phase B専用terminal escalation、`TerminalLatchBusy`のglobal
  terminal再分類がzeroであること。

次のいずれかを検出した場合は実装を停止し、本節を再査読する。

- safe production APIからactual terminal latch conflictへ到達するborrow guard、re-entrancy、thread、async yieldが見つかる。
- row 4 / defer / row 7でroundがsame-self local construction以外の経路から供給される。
- post-commit queryから`requires_attempt_terminal() == false`のfailureがtest overrideなしで観測される。
- terminal latchをcheckせずattempt resultを利用する新しいin-repo production consumerが追加される。
- release-mode invariant canary以外の新しいfailure recovery / escalation mechanismが必要になる。

本節が許可するのは、organic terminal-latch conflictをpanic invariantへ変更する共有gatewayのPart 1と、実証済みの
same-self round localityを前提にrow 4 / row 7 / deferへrow 3 idiomを適用するPart 2だけである。他のcaller row、
proof family authority、sealed reuse、snapshot、cache、visibility、publication meaning、既存terminal classificationを
再開または緩和しない。

追記著者: Codex gpt-5.6-sol（xhigh）が起案、Claude (Sonnet 5) が独立査読・確定

追記状態: 確定・ユーザ承認済み（2026-08-15）。独立査読SOUND（一切文脈のない別セッションによる確認reviewを含め計2ラウンド、
findings完全ゼロ）。Claude (Sonnet 5) が全文を直接通読し、既存正本群（CPK-SV-D sealed gateway、CPK-SV-C Phase A/B先例、
DPN/MPCのmutationを跨がないmemo規律）との整合を確認済み。row 4 / row 7 / `defer_scheme_projection_mutation`の
failure-boundary設計として、上の三度の却下（pending-receipt propagation案、単純attempt-terminal案、row3 idiom直接転用案）を
すべて置き換える正本として確定する。

## 2026-08-15 追記: row 1残りsubrow（witness collection / compaction）のscoped facade read surface拡張

### 発見した不足と本節の範囲

§4.0.2 row 1 subrow 1-a〜1-dの実装前inventoryで、rev.9 §2.1.1が列挙した
`ScopedLegacyProjectionQuery::scheme_projectable_lowers_in_scope`と`pos_var_in_scope`だけでは、
`capture_generalized_witnesses`の再帰walkとscheme-mode `CompactCollector`のwalk全体を一つのHRTB scope内へ
移せないことが分かった。両collectorはprojectable-lower判定以外にも、型shape、upper bound、row/subtract、
constraint-neighbor情報を同じ再帰walk中に読む。gatewayへ`&mut ConstraintMachine`を渡したclosure内から
同じmachineを`&ConstraintMachine`として再borrowすることはできず、それをraw pointerやscope外snapshotで回避することも
本設計のexclusive scope / single authority条件に反する。

本節は、この二traversalのactual codeが現在行うreadだけをowned-return getterとして追加する。
既存scoped getterのsignature、failure classification、round/completion type、publication-side facade、writer authorityは変更しない。
scheme-mode compaction / witness surfaceとそのproduction callerのinfallible signatureも変更せず、denialは後述する
row 2と同じscope-local degradationへ畳む。
general-purposeな`machine()`、`types()`、`bounds()`、`view()`、raw storage referenceは追加しない。

### Actual read inventoryと既存surface照合

lineは2026-08-15 HEADの目安であり、実装時に`rg`で再確認する。

| traversal | current read | current location | existing scoped equivalent | decision |
|---|---|---|---|---|
| witness | positive lower selection | `generalize/provenance.rs:208-212`の`bounds().of(var)` / `scheme_projectable_lowers(var)` | `scheme_projectable_lowers_in_scope` | 既存methodを使う。new getter zero |
| witness | ordered evidence+ordinary upper records | `generalize/provenance.rs:208,263-276`の`generalized_projection_uppers()` | none | owned upper-record getterを追加 |
| witness | full positive node shape | `generalize/provenance.rs:287,615`の`types().pos(id).clone()` | `pos_var_in_scope`はVar caseだけで不十分 | owned `Pos` getterを追加 |
| witness | full negative node shape | `generalize/provenance.rs:398,640`の`types().neg(id).clone()` | none | owned `Neg` getterを追加 |
| witness | full neutral node shape | `generalize/provenance.rs:499`の`types().neu(id).clone()` | none | owned `Neu` getterを追加 |
| scheme compact | full positive node shape | `compact/collect/mod.rs:272,876`の`types().pos(id).clone()` | `pos_var_in_scope`は不十分 | witnessと同じowned `Pos` getterを共用 |
| scheme compact | full negative node shape / effect-family match | `compact/collect/mod.rs:338,731,868,909`の`types().neg(..)` | none | witnessと同じowned `Neg` getterを共用 |
| scheme compact | full neutral node shape | `compact/collect/mod.rs:403`の`types().neu(id).clone()` | none | witnessと同じowned `Neu` getterを共用 |
| scheme compact / type node recursion | positive node shape | `compact/collect/type_nodes.rs:9,201,205,266,412`の`types().pos(..)` | `pos_shape_in_scope`（本節で追加） | 同じowned `Pos` getterを再帰helperから共用。追加getter zero |
| scheme compact / type node recursion | negative node shape | `compact/collect/type_nodes.rs:109,233,296,521,608`の`types().neg(..)` | `neg_shape_in_scope`（本節で追加） | 同じowned `Neg` getterを再帰helperから共用。追加getter zero |
| scheme compact / type node recursion | neutral node shape | `compact/collect/type_nodes.rs:323,384`の`types().neu(..)` | `neu_shape_in_scope`（本節で追加） | 同じowned `Neu` getterを再帰helperから共用。追加getter zero |
| scheme compact / negative row tail recursion | cloned upper records followed by negative node lookup | `compact/collect/type_nodes.rs:602-608`の`bounds().of(var).cloned()` / `types().neg(..)` | `projection_upper_records_in_scope` + `neg_shape_in_scope`（本節で追加） | full `VarBounds` getterは追加せず、同じ二getterを共用 |
| scheme compact | role constraint raw vars | `compact/collect/mod.rs:473`の`RoleConstraint::raw_vars(machine.types())` | none | purpose-specific owned set getterを追加 |
| scheme compact | constraint-neighbor closure | `compact/collect/mod.rs:500`の`machine.var_neighbors(var)` | none | owned neighbor vector getterを追加 |
| scheme compact | bounds presence / positive and negative projection bounds | `compact/collect/mod.rs:636-660`の`bounds().of(var).cloned()` | positive側は`scheme_projectable_lowers_in_scope`、negative側はnone | full `VarBounds` cloneは公開せず、positiveは既存method、negativeは同じowned upper-record getterを使う |
| scheme compact | pre-pop effect families | `compact/collect/mod.rs:695-705`の`pre_pop_effect_families(var)` | none | owned family vector getterを追加 |
| scheme compact | subtract facts | `compact/collect/mod.rs:801`の`subtracts().facts(source)` | none | owned fact vector getterを追加 |

`compact/collect/mod.rs:473,500`はinput formatterのroot compactionだけでなく、
`CompactCollector::new_recording_for_scheme`を使うproduction role-constraint compactionから到達する。
具体的には`compact/surface.rs:503-514`を介して`analysis/session/generalize.rs:77`から呼ばれるため、test-only readとして
除外しない。同様にscheme-mode collectorはinput formattingだけでなく、`compact_type_var_for_scheme`
（`generalize/mod.rs:82`、`lowering/expr/tail.rs:1247`）と
`compact_type_var_recording_merge_constraints_for_scheme`（`analysis/session/generalize.rs:596`）からも使われる。
row 1のold helper production reference zero gateは、これら全てを同じscheme-mode scoped routeへ移した後にだけ成立する。

上表の`compact/collect/type_nodes.rs`行は、reviewで指摘された`9,201,266,109,233,521,608,323,384,602`に加え、
同じ再帰surface上の反復lookupである`205,296,412`も列挙する。これらはgetter数を増やさず、main collectorと同じ
`Pos` / `Neg` / `Neu` / upper-record surfaceへ割り当てる。従って「actual read inventoryに未割当read zero」は
`collect/mod.rs`だけでなく`collect/type_nodes.rs`を含む主張になる。

### 追加するexact safe surface

P0 legacy facadeへ次のmethodだけを追加し、全てexactly `pub(crate)`とする。内部
`LegacyOnlyQueryView`側の対応methodは`pub(super)`、source field / constructorはprivateのままとする。

```rust
impl ScopedLegacyProjectionQuery<'_> {
    pub(crate) fn projection_upper_records_in_scope(
        &self,
        var: TypeVar,
    ) -> Vec<(BoundRecordId, WeightedUpperBound)>;

    pub(crate) fn pos_shape_in_scope(&self, id: PosId) -> Pos;
    pub(crate) fn neg_shape_in_scope(&self, id: NegId) -> Neg;
    pub(crate) fn neu_shape_in_scope(&self, id: NeuId) -> Neu;

    pub(crate) fn role_constraint_raw_vars_in_scope(
        &self,
        constraint: &RoleConstraint,
    ) -> FxHashSet<TypeVar>;

    pub(crate) fn var_neighbors_in_scope(&self, var: TypeVar) -> Vec<TypeVar>;

    pub(crate) fn pre_pop_effect_families_in_scope(
        &self,
        var: TypeVar,
    ) -> Vec<ConstraintEffectFamily>;

    pub(crate) fn subtract_facts_in_scope(&self, source: TypeVar) -> Vec<SubtractFact>;
}
```

返却順序はcurrent readと同じにする。

- `projection_upper_records_in_scope`は`VarBounds::generalized_projection_uppers()`と同じく、evidence upperを先、
  ordinary upperを後にして、各groupのinsertion orderを保つ。record IDと`WeightedUpperBound`をcloneして返す。
- `pos_shape_in_scope` / `neg_shape_in_scope` / `neu_shape_in_scope`はcurrent `TypeArena::{pos,neg,neu}` lookupと
  同じinvalid-ID behaviorを保ち、node enumをcloneして返す。
- `role_constraint_raw_vars_in_scope`はscopeが保持するtype-shape authorityを使い、current
  `RoleConstraint::raw_vars(TypeArena)`と同じowned `FxHashSet<TypeVar>`を返す。この`constraint`はcaller-owned immutable
  inputであり、proof/constraint record storageへのraw accessではない。
- `var_neighbors_in_scope`はcurrent `ConstraintMachine::var_neighbors`のiteration content/orderをそのままowned `Vec`へcollectする。
  current pathはmap-keyのlazy iteratorなので、この`Vec` allocationは新規である。
- `pre_pop_effect_families_in_scope`はcurrent sliceから`ConstraintEffectFamily`のowned `Vec`を返す。current pathは最終
  compact conversion時に各familyをcloneするが、中間`Vec`を作らないため、このgetterはclone時点を早め、追加の
  intermediate allocationを導入する。
- `subtract_facts_in_scope`はcurrent `SubtractTable::facts(source)`からowned `Vec<SubtractFact>`を返す。current pathは
  borrowed sliceをiterateするため、このgetterは`Subtractability`を含む`SubtractFact`全体の新しいdeep cloneと
  intermediate allocationを導入する。

full `VarBounds`、`TypeArena`、`SubtractTable`、adjacency map、pre-pop mapへのreferenceを返すgetterは作らない。
特に`bounds_in_scope() -> Option<&VarBounds>`や`types_in_scope() -> &TypeArena`のようなgeneral escape hatchは禁止する。

この実装のため、private `LegacyOnlyReadSources` / `LegacyOnlyQueryView`内部へ、既存`bounds`とtype-shape authorityに加えて
次のread-only source referenceを追加してよい。

- `var_adjacency: &FxHashMap<TypeVar, FxHashMap<TypeVar, usize>>`
- `subtracts: &SubtractTable`
- `pre_pop_effect_families: &FxHashMap<TypeVar, Vec<ConstraintEffectFamily>>`

これらfield、source bundle、constructor、`LegacyOnlyQueryView`は引き続き`structural_kernel`内部privateとする。
`ImmutableTypeShapeView`にはnode cloneとrole raw-var calculationに必要なprivate/internal methodだけを追加し、
`TypeArena` reference自体は返さない。

`compact/collect/mod.rs:868`のeffect-family判定もcurrent pathでは`&Neg`に対してmatchするが、scoped routeでは
`neg_shape_in_scope`が`Neg`をcloneする。従って本節は、八getterを「current direct traversalが同じ地点で既に行うcloneの
単なる移動」とは主張しない。upper recordと多くの`Pos` / `Neg` / `Neu` lookupはcurrent codeでもcloneする一方、
effect-family `Neg`、subtract fact、neighbor、pre-pop familyには上記の新しいowned intermediate costがある。

このcostは無条件にcold-path costとして受容しない。GWCB
`notes/design/2026-08-10-generalized-witness-claim-bridge-provenance-gap.md` §9は
`scheme_projectable_lowers` payloadを明示的にhot pathと分類し、`std::text::parse`、full lowering、representative corpusの
cold/warm測定をlanding条件にしている。本節もその分類を継承する。

その上でP0では、各allocationが一varのadjacency/fact/familyまたは一nodeに局所化されることと、cloneを避ける
callback/visitor型scoped APIがclosure lifetime、early return、再帰control flowをsafe surfaceへ持ち込むより大きい
API/design変更になることから、owned getterをprovisionalに採る。GWCBと同じstd/full-lowering/corpus測定でwall/RSS、
scope-entry、getter call、owned element countを比較し、既存baseline内である場合だけlandingを認める。regressionが出た場合は
「hot pathではない」として受容せず、visitor APIを別設計・再査読するstop条件とする。

#### Test-only read instrumentation parity

新getterはprivate fieldを直接読むため、旧public/internal getterに付随する次の`#[cfg(test)]` instrumentationを
偶然迂回し得る。

- `var_neighbors`: `constraints/machine/entry.rs:265-266`の`record_owner_neighbor_read(var)`。
- `pre_pop_effect_families`: `constraints/machine/entry.rs:949-951`の`record_owner_pre_pop_read(var)`。
- `subtract_facts`: `constraints/mod.rs:3398-3400`の`record_owner_subtract_read(source)`。

これらは旧call siteだけのobsolete instrumentationとは扱わない。dependency/audit fixtureが観測するlogical readを
scoped routeでも維持するため、新getterまたはその直下のprivate view methodが、owned collect/cloneの直前に同じhookを
exactly once呼ぶ。旧getterを経由して二重発火させず、raw fieldを読む新routeだけが対応hookを一回発火する。
既存fixtureのexpected read owner / countを新実装の出力へ合わせて弱めず、旧routeとscoped routeのtrace parityで検証する。

SS2 final sealed projection cutoverでは、production callerを`ScopedProjectionQuery`へ移す前に、上の八methodと
同じname / owned return shapeをfinal facadeのpurpose-specific safe surfaceへ用意する。P0ではfinal backing familyを
先回りして公開せず、legacy facadeの八methodだけを実装する。final counterpartが用意できない状態でlegacy methodを
削除またはcallerをfinal routeへ移すことはstop条件とする。

### Ownership / HRTB safety

八methodは全てowned valueを返す。返却値に`'query` reference、facade/view、`TypeArena`、`VarBounds`、table/map slice、
evaluator、round、memo、visiting stateを含めない。従って個々のowned cloneはclosure内の再帰処理で保持できるが、
scope-local authorityやevaluation stateをclosure外へ運べない。

既存`scheme_projectable_lowers_in_scope`だけは`SchemeProjectableLower<'scope>`内にborrowed
`WeightedLowerBound`を持つが、HRTB closure内で全消費し、owned resultへ含めないという§4.0.2の既存条件を維持する。
新getterはこのborrowed surfaceを広げない。upper entryと多くのnode lookupはcurrent pathのcloneを移すだけだが、
effect-family `Neg`、subtract fact、neighbor、pre-pop familyには前節で明示した新しいintermediate allocation / deep cloneがある。
それらの受容判断とperformance stop条件を含めてsafe surfaceの一部とする。

新getterはいずれもread-onlyであり、candidate publication、proof write、family write authority、attempt nonce、
query completion、cache hit/miss、round reuseへ触れない。persistent memo、cross-round state、nested gatewayを追加しない。

### Pure-read failure boundary: row 2のscope-local degradationをそのまま転用する

row 2のshipped implementationである`generalize/mod.rs:283-340`の
`expand_positive_aliases_in_scheme_compact`は、外側の`CompactRoot` / role predicatesを保持したまま、

```rust
let _ = machine.with_legacy_projection_query(&mut round_state, |query| { ... });
```

とする。scope entry/authenticationがdenialした場合はclosureが始まらず、pre-scope compactをそのまま後続simplifyへ渡す。
closure途中の`scheme_projectable_lowers_in_scope`がdenialした場合は、それ以前に完了したalias expansionをrollbackせず、
未完の残りwalkだけを行わない。関数signatureは`()`のままで、Err自体は`let _ =`でscope-localに捨てる。

row 1残りsubrowもこの既存precedentを採る。hard `Result` cascadeは採らず、
`generalize_type_var_with_boundaries`、`AnalysisSession::{drain_work,step,take_scc_events}`、`quantify_component`、
`lower_binding_bodies`、dump entry、`check.rs` formatter、yulang hover/completion/server routeのsignatureを変更しない。
各top-level surfaceはfresh roundを同じmachineで作り、一回のscope resultをその関数内だけでsuccess outputまたは
degraded outputへ畳む。raw-mode再実行やnested scopeは行わない。

collectorについてはpartial internal stateをscope外へ漏らす必要がないため、row 2より強いlocal transaction形にする。
collectorをclosure内で完結させ、`query.complete(owned_output)`まで成功した場合だけfull outputを返す。denial時のexact outputは
次のとおりである。

1. `compact_type_var_for_scheme`: `CompactRoot::default()`。これはroot bounds / recursive boundsを一件も主張しない
   empty-equivalent compactであり、raw boundsを代替authorityとして再読しない。
2. `compact_negative_type_var_for_scheme`: 同じく`CompactRoot::default()`。input formatterは従来どおり同じinfallible
   `String` / `PublicTypeDisplay` surfaceを使い、default compactを既存finalizerへ渡す。
3. `compact_type_var_recording_merge_constraints_for_scheme`:
   `(CompactRoot::default(), Vec::new())`。partial compact、partial merge constraint、cache candidateを返さない。
4. `compact_reachable_role_constraints_from_seed_vars_recording_merge_constraints`:
   `(Vec::new(), Vec::new())`。partial role constraint / merge constraintを返さない。
5. `capture_generalized_witnesses`: `(Vec::new(), ProvenanceCompleteness::Incomplete)`。queryから得た親edgeやpartial draftを
   返さず、scheme record全体をincompleteとして保存する。empty witness + incompleteは既存provenance modelが持つ
   fail-open表現であり、complete witnessを捏造しない。

上の五surfaceはcurrent return typeを維持する。実装はscope resultへ`unwrap_or_default`相当を使ってよいが、witnessだけは
`ProvenanceCompleteness::Incomplete`を明示し、default/completeと取り違えない。test-only denial injectionでは各exact degraded
outputとscope entry one / nested zeroを検証する。

このlocal degradationがterminal failureを隠すことはない。本書の「2026-08-15 追記（四度目）」で確定したとおり、
organic `TerminalLatchBusy`はgatewayのreal pathから除かれ、`ForeignAttemptRoundState`はfresh roundを同じ`self`で直ちに
consumeする本migrationのcall shapeでは到達しない。実際に到達し得るproof-semantic failureはgatewayがErrを返す前に
`requires_attempt_terminal()`分類に従ってterminal latchへ記録する。従ってcallerがErrをlocal degradationへ畳んでも、
in-repo production compiler result consumerのterminal gateはfailureを観測する。non-terminal denialのoutput shapeは、
同じtest-only injection / safe-API misuse耐性としてrow 2と同じ範囲でのみ意味を持つ。

`check.rs`のvalue/member/input formattingのexact Result shapeを新設する必要はなく、先行draftのsignature ambiguityは消滅する。
formatterの既存`String` / `PublicTypeDisplay` / `Option` contractとyulang route-error-to-no-hover behaviorは変更しない。

`analysis/session/instantiate.rs`の`quantify_component`も`()`のまま、scheme generalization、scheme insertion、witness recordingを
従来どおり一回だけ実行する。witness denialはempty + `Incomplete` provenanceへ局所化され、scheme自体をpartialにしたり、
quantificationを早期return / retry / 二重実行したりしない。current un-migrated pathでprojectable lowerが正常にzero件のときも
sparse/empty witnessを許し、scheme-level completenessは既に`Incomplete`である。従って
`notes/design/2026-07-13-role-impl-method-two-stage-lifecycle.md`の「ordinary quantification exactly once」invariantと
role lifecycle control flowは変更されない。これより前のscheme compaction自体がproof-semantic denialした場合は
empty-equivalent compactが同attempt内で後続処理され得るが、そのfailureは既にterminal latchへ記録済みなので
in-repo production compiler result consumerへschemeが到達しない。non-terminal denialは上記same-self call shapeでは
到達しない。この二条件をquantify-onceと混同して「partial schemeをproductionへ許す」とは扱わない。

### row 1 migration shape

#### 1-a / 1-b witness collection

`capture_generalized_witnesses`は`&mut ConstraintMachine`を受け、fresh
`ProjectionEvaluationRoundState`を同じmachineで作り、一回の`with_legacy_projection_query`で
collector root、全recursive `collect_var` / `collect_pos` / `collect_neg` / `collect_neu`、draft post-processingを包む。
`WitnessCollector`は`&ConstraintMachine`ではなく`&ScopedLegacyProjectionQuery`とscope-local
`ProjectionEvaluationRound`を使う。positive lowerだけがfallibleなので、collector recursionは
scope内部だけで`Result`をthreadする。closure外へ返すのはowned
`(Vec<GeneralizedWitnessDraft>, ProvenanceCompleteness)`だけであり、scope denialは同じreturn typeの
`(Vec::new(), ProvenanceCompleteness::Incomplete)`へ畳む。

`lowering/expr/tail.rs`のlocal witness captureと`analysis/session/instantiate.rs`のcomponent witness captureは、
各top-level captureごとに既存infallible signatureのままこのowned full/degraded resultを受け取る。scope終了後のancestor
adjustment、generalized witness storage、scheme finalizeはowned resultだけを使う。witness traversal中のscope再entry、
`&ConstraintMachine` fallback、borrowed lowerのescapeはzeroとする。

#### 1-c / 1-dおよび全scheme-mode compaction entry

scheme-mode compact surfaceは`&mut ConstraintMachine`を受け、top-level compact call一回につきfresh roundと一回の
`with_legacy_projection_query`を開く。scheme-mode `CompactCollector`は
`&ScopedLegacyProjectionQuery`と同一scope-local `ProjectionEvaluationRound`を使い、上のowned getterと
`scheme_projectable_lowers_in_scope`だけでroot / recursive bounds / stack-family / subtract / role traversalを完了する。
scheme-mode recursionはscope内部だけで`Result`をthreadし、closure外へ出るsuccess valueはowned `CompactRoot`、または
既存surfaceが要求するowned `(CompactRoot, Vec<CompactMergeConstraint>)` / owned role-constraint vectorだけである。
failure時はpartially built collector outputをdropし、上節でsurfaceごとに固定したempty-equivalent owned resultを返す。

raw-mode `CompactCollector::new` / `new_recording` / `new_recording_owner_dependencies`は本節の対象外で、既存machine readを
変更しない。scheme-mode constructorだけをscoped readerへ切り替える。input completion / hoverでは
`check.rs`の各top-level input formatterが、scopeを所有するscheme compact surfaceを一回だけ呼び、owned full/degraded
`CompactRoot`を既存signatureのままfinalize / formatする。
generalization、local environment compaction、recording scheme compaction、scheme-mode role compactionも、それぞれの
top-level surfaceで同じ一scope形を使い、collector内部でgatewayをnested callしない。どのsurfaceもdenialをraw-mode readや
caller-level Result cascadeへ変換せず、同じ関数内のexact degraded outputへ畳む。

### rev.9 exact safe surfaceとの整合

本節はrev.9 §2.1.1のcross-sibling例外リストへ上の八methodを加える狭い追加である。
method visibilityは`generalize` / `compact` / `check`が`constraints`のsiblingであるため`pub(crate)`、
backing view/source visibilityは従来どおり`pub(super)`以下とする。既存methodやtypeのvisibilityをさらに広げない。

この追加は「legitimate production callerが必要とする目的別safe methodだけを同effective visibilityにする」という
rev.9 invariant 66 / 76の理由を維持する。raw storage layout、constructor、field、mutator、write port、candidate internals、
publication facadeは公開しない。八method以外の追加が必要になった場合は本節を黙って拡張せず、実装を停止して再査読する。

### Gate / stop

- 上のinventory各行を`compact/collect/mod.rs`と`compact/collect/type_nodes.rs`を含むactual call graphで再確認し、
  提案した八getter全てに一件以上のproduction read siteが対応し、unassigned readとspeculative getterがzeroであること。
- `ScopedLegacyProjectionQuery`の新methodがexactly `pub(crate)`、対応する`LegacyOnlyQueryView` methodが
  `pub(super)`、source field / constructorがprivateであること。
- 新getterのreturn typeにreference、facade/view、arena/table/map/slice、round/evaluator/cache stateがzeroであること。
- `projection_upper_records_in_scope`のentry順、node getterのinvalid-ID behavior、neighbor iteration content、pre-pop family、
  subtract fact、role raw-var setがcurrent direct readとsemantic parityを持つこと。
- `var_neighbors_in_scope`、`pre_pop_effect_families_in_scope`、`subtract_facts_in_scope`が旧routeと同じtest-only
  read-instrumentation hookをlogical read一件につきexactly once発火し、dependency/audit fixtureのowner/count traceが
  migration前と一致すること。hook zeroまたは二重発火は不可。
- effect-family `Neg` clone、subtract fact deep clone、neighbor/pre-pop intermediate `Vec`を含む新allocationをwall/RSSで
  bounded測定し、GWCB §9の`std::text::parse`、full lowering、representative corpusのcold/warm baselineから説明不能な
  regressionがないこと。regression時にzero-cost parityを主張せず、visitor APIの別設計・再査読へ停止すること。
- witness 1-a / 1-bで各top-level captureにつきquery scope entry exactly one、nested entry zero、owned draft/completenessだけが
  closure外へ出ること。success時のlocal/component witness outputとcompletenessがmigration前と一致し、denial fixtureが
  exactly `(Vec::new(), ProvenanceCompleteness::Incomplete)`を返すこと。
- input 1-c / 1-dで各top-level formatterにつきscope entry exactly one、success時のowned `CompactRoot`だけがformat phaseへ渡り、
  hover/completion outputがbyte-for-byte一致すること。denial fixtureでは四surfaceが上節のexact default/empty tupleを返し、
  partial compact / merge / role output、raw-mode fallback、nested scopeがzeroであること。
- `new_for_scheme` / `new_recording_for_scheme`を使う全production surfaceがscoped routeへ移り、generalization、local environment、
  role compaction、merge-constraint recordingのsemantic outputが不変であること。
- 四つのscheme compact surface、`capture_generalized_witnesses`、`generalize_type_var_with_boundaries`、
  `quantify_component`、check/yulang formatter/routeの既存infallible return shapeが不変であること。scope Errはtop-level
  traversal内だけでrow 2型local degradationへ畳み、caller chainへ新しい`Result`を追加しないこと。
- terminal proof-semantic denial fixtureでgateway terminal latchがcallerのdegradationより先に設定されること。
  `TerminalLatchBusy` / `ForeignAttemptRoundState` injection fixtureはdegraded outputを検証するが、organic production
  reachabilityを主張する証拠として扱わないこと。
- `quantify_component`がsuccess / witness-denialの双方でordinary quantificationとscheme insertionをexactly once行い、
  witness denial時はempty + incomplete provenanceだけを記録してretry / second quantificationを行わないこと。
- old `ConstraintMachine::scheme_projectable_lowers` / `scheme_projectable_lowers_in_round`のproduction callerがzeroであること。
  test-only callerを残す場合はproduction censusから明確に分離し、旧helperをproduction fallbackに使わないこと。
- `LegacyOnlyReadSources`へ追加するmachine field referenceが`var_adjacency`、`subtracts`、
  `pre_pop_effect_families`の三つだけであり、新しいwrite authorityやmutable referenceがzeroであること。
- inferのconstraints / generalize / compact tests、local/component witness tests、yulangのbounded hover / completion testsを実行し、
  既存baselineとuser-visible output parityを確認すること。

次のいずれかを検出した場合は実装を停止し、本節を再査読する。

- 八getter以外のmachine readがscheme-mode witness / compact traversalに残る、または新たに必要になる。
- full machine、arena、bounds/table/map、raw viewへのreference getterが必要になる。
- borrowed `SchemeProjectableLower`、`WeightedLowerBound`、scope facade、round/evaluator stateがHRTB closure外resultへ現れる。
- one top-level traversalを一scopeで包めず、nested gatewayまたはper-record/per-var scopeが必要になる。
- getter追加がproof/constraint/row writer authority、candidate publication、round reuse、failure classificationを変更する。
- exact degraded outputだけではscope denialを局所化できず、caller-level `Result` cascade、新しいuser-visible error policy、
  raw-mode再実行、retry、またはpartial collector outputのescapeが必要になる。
- owned getter追加によるwall/RSS regressionが既存baselineを超え、八getterのpurpose-specific `Vec` return shapeを維持できない。
- scoped routeでneighbor/pre-pop/subtractのtest-only instrumentationをexactly once維持できず、dependency/audit fixtureの
  coverageを弱める必要が生じる。
- final sealed facadeへ同じpurpose-specific operationを実装できず、legacy routeをSS2後へ残す必要が生じる。

本節が許可するのは、row 1残りsubrowと同じscheme-mode collector production pathに必要な八owned getter、
そのprivate legacy read-source wiring、既存test-only read instrumentationのparity wiring、およびこれらgetterを使うcaller
migrationとrow 2同型のscope-local degraded outputだけである。他row、publication-side API、write authority、caller signature、
cache design、failure classification、pending/retry mechanismを再開または変更しない。

追記著者: Codex gpt-5.6-sol（xhigh）が起案、Claude (Sonnet 5) が独立査読予定

追記状態: **blocked（2026-08-15）**。4回連続で独立reviewがNOT SOUNDと判定した
（1回目: failure boundary完全未設計、2回目: hard Result propagationが実在しない境界を要求、
3回目: row2前例への置換提案自体は妥当だが実装詳細が不十分、4回目: CRITICAL 3件——
(a) scheme-mode compact surfaceが`&mut ConstraintMachine`を要求する一方、`check.rs`のinput
formatterは`&ConstraintMachine`/`&Arena`の共有参照しか持たず、署名を変えないという制約と
両立しない。(b) `CompactRoot::default()`は「情報が無い」ことを表さず、finalizerの規約上
実際に`Pos::Bot`（never）・`Neg::Top`（any）という強い型的主張へ変換される——failureを
正常なsemantic valueへすり替えてしまう。(c) hover/completion/single-file dumpの経路には
lowering完了後のformatter実行前にterminal latchを再確認するgateが無く、degraded output
が誤ったhover text・偽のnever/any表示・空candidateとしてそのままユーザへ届き得る）。

row2の前例（既存compactへのin-place mutationを短く終える）と、本節が対象とする
witness collection/compactionの構造（新しい出力をゼロから作る処理そのものが失敗する）は
根本的にrisk profileが異なると4回目のreviewで指摘された——前者は既存情報を保持するだけ
だが、後者はfailureを「制約なし」「witnessゼロ」という正常に見える意味論値へすり替える。
これはCPK-SV-C episodeと同型の「指摘がエスカレートする」パターン（1回目:設計皆無→
2回目:実現不能な要求→3回目:方向性は妥当だが実装が粗い→4回目:CRITICAL 3件）であり、
次の一手で直る局面ではないと判断し、ここで停止する。row 1残りsubrow
（witness collection: `capture_generalized_witnesses`、compaction:
`compact_type_var_for_scheme`他3surface）は引き続きblockedとし、row 2〜7と
row 7 snapshot-publication loopの既に完走・push済みの成果とは切り離して扱う。
次に着手する際は、この4回で見えた「新規構築の失敗を正常値にすり替えない安全な
degradation」という、まだ解けていない核心の問い自体を主題とした専用ラウンドが必要。

## 2026-08-15 追記（五度目・draft）: attempt-local poisonとfinal-output terminal gateの分離

### 0. 本節の位置づけと戦略変更

本節は、直前のblocked節を削除、修正、または遡及的に承認しない。四案が失敗した履歴と
`CompactRoot::default()`が実際の`Never` / `Any`を表すという指摘をそのまま正本に残した上で、
failure時の内部値を「意味論的に安全なfallback」と証明する課題自体をuser-facing safetyから分離する第五案である。

対象は§4.0.2 row 1の未完部分だけである。

- 1-a / 1-b: `generalize/provenance.rs::capture_generalized_witnesses`を起点とするlocal binding / component witness capture。
- 1-c / 1-d: `compact_type_var_for_scheme`、`compact_negative_type_var_for_scheme`、
  `compact_type_var_recording_merge_constraints_for_scheme`、
  `compact_reachable_role_constraints_from_seed_vars_recording_merge_constraints`を起点とするscheme-mode compaction。
- 上のpure-read traversalが必要とする、blocked節で全量inventory済みの八つのpurpose-specific owned getter。
- formatter実行後にterminal latchを再確認する、current in-repo yulang production hover / completion / member-completionの
  三final-output gate。

本節は、denial時の`CompactRoot::default()`をunknown、neutral、または正しい型と再定義しない。
`CompactRoot::default()`は引き続きfinalizer上の`Pos::Bot` / `Neg::Top`であり、単独ではuser-visible semantic valueとして
安全でない。scope denial後に内部処理を同attempt内で閉じるための**attempt-local poison placeholder**としてだけ許可し、
そのattemptのsemantic outputが外へ出ないことをterminal latchとfinal-output gateで保証する。

### 1. この案を支える確認済み事実

1. 本書の「2026-08-15 追記（四度目）」で確定したとおり、organic `TerminalLatchBusy`はcurrent safe production APIから
   到達不能であり、`ensure_query_kernel_active`のreal pathは`RefCell::borrow()`を使う。actual conflictはtyped denialではなく
   invariant panicとなる。
2. `ForeignAttemptRoundState`はgeneral API上のmisuseとしては可能だが、fresh roundを同じ`self`で作り、同じ同期関数内で直ちに
   consumeするrows 2〜7の形では到達しない。row 1残りも同じsame-self immediate-consumption形を採り、roundをfield、return、
   helper parameter、cross-machine boundaryへ出さない。
3. 従ってrow 1残りのreal call shapeでgateway denialとして有機的に到達し得るのは、
   `requires_attempt_terminal() == true`のproof-semantic failure、または既にterminal latchへ格納済みのfailureだけである。
   `with_legacy_projection_query`は前者をcallerへ`Err`として返す前にterminal latchへ記録する。
4. checked loweringの`run_proof_compilation_attempt` / `body_lowering_attempt`は、lowering終了時に同じmachineのterminal latchを読み、
   failureがあれば`BodyLowering`をdropして`LoadedFilesError::ProofKernelFailed`を返す。witness captureとgeneralization-time
   compactionのdenialはこの既存gateで既にattempt全体を破棄する。
5. 一方、`check_loaded_files`成功後にhover / completion formatterが新たにscheme compactionを行うため、
   `source_hover_from_check`、`source_completion_from_check`、`source_member_completion_from_check`にはformatter後の再checkが必要である。
   current codeにはこの三箇所のどこにもpost-format terminal gateがない。
6. `GeneralizeCompactCache`は`AnalysisSession` fieldであり、`AnalysisSession::new*`ごとに
   `GeneralizeCompactCache::from_env()`から新規作成される。env/global stateが持つのはenable flagだけで、entryは保持しない。
   fresh `SourceTextAnalysis`もfresh `check_loaded_files` / `AnalysisSession`を所有する。従ってterminal-failed attemptでcacheされた
   poison compactは同attempt内でだけ再利用され、後のsuccessful attemptへ移らない。

この六事実のいずれかが崩れれば本案も無効となる。特に3と6はlocal placeholderの意味論を問わず安全性を成立させる
load-bearing premiseであり、推測や「稀」の評価ではなく実装gateとして固定する。

### 2. exact safe read surfaceはblocked節の八getterを継承する

blocked節のActual read inventory、allocation caveat、test-only instrumentation parityはfailure-boundary案とは独立しており、
本節も次の八methodだけを`ScopedLegacyProjectionQuery`へexactly `pub(crate)`で加える。

```rust
pub(crate) fn projection_upper_records_in_scope(
    &self,
    var: TypeVar,
) -> Vec<(BoundRecordId, WeightedUpperBound)>;
pub(crate) fn pos_shape_in_scope(&self, id: PosId) -> Pos;
pub(crate) fn neg_shape_in_scope(&self, id: NegId) -> Neg;
pub(crate) fn neu_shape_in_scope(&self, id: NeuId) -> Neu;
pub(crate) fn role_constraint_raw_vars_in_scope(
    &self,
    constraint: &RoleConstraint,
) -> FxHashSet<TypeVar>;
pub(crate) fn var_neighbors_in_scope(&self, var: TypeVar) -> Vec<TypeVar>;
pub(crate) fn pre_pop_effect_families_in_scope(
    &self,
    var: TypeVar,
) -> Vec<ConstraintEffectFamily>;
pub(crate) fn subtract_facts_in_scope(&self, source: TypeVar) -> Vec<SubtractFact>;
```

対応する`LegacyOnlyQueryView` methodは`pub(super)`、source bundle / field / constructorはprivateとし、returnは全てownedとする。
`TypeArena`、`VarBounds`、table/map/slice、facade、round、evaluator、cacheへのreferenceは返さない。
`var_neighbors_in_scope`、`pre_pop_effect_families_in_scope`、`subtract_facts_in_scope`は旧routeと同じtest-only logical-read hookを
exactly once発火する。effect-family `Neg`、subtract facts、neighbor、pre-pop familyのnew intermediate clone/allocationは
GWCB §9のhot-path分類に従ってbounded performance gateを通し、zero-cost parityとは主張しない。

八getter以外のread、reference-return getter、write authority、nested gateway、persistent memoが必要ならstopする。

### 3. 内部denialの扱い: semantic fallbackではなくattempt-local poison

各top-level witness / scheme-compaction surfaceは、同じmachineでfresh
`ProjectionEvaluationRoundState`を作り、一回の`with_legacy_projection_query`でtraversal全体を包む。
collector、scope-local `ProjectionEvaluationRound`、cache、visiting stateはclosure内に置き、成功時だけowned resultを返す。
gateway `Err`はrow 2のshipped `expand_positive_aliases_in_scheme_compact`と同様にtop-level surface内で畳み、
infallible caller chainへ新しい`Result`を伝播しない。

`WitnessCollector`とscheme-mode `CompactCollector`は、scope facadeへのimmutable handleとscope-local
`ProjectionEvaluationRound`を同じcollector内に持つ。`scheme_projectable_lowers_in_scope`のborrowed lowerはscope内で消費し、
compact recursionへ渡す必要があるboundだけをowned cloneへ変換してからcollectorを再びmutableに借りる。raw-mode collectorは
既存`&ConstraintMachine` routeを維持し、scheme-modeからraw-modeへfallbackしない。

denial時の具体的な内部値は次のとおり固定する。ただし、いずれも正常なsemantic substituteではなく、terminal-failed attemptを
既存同期control flowの終端まで運ぶためのpoisonである。

1. `compact_type_var_for_scheme`と`compact_negative_type_var_for_scheme`は`CompactRoot::default()`。
2. `compact_type_var_recording_merge_constraints_for_scheme`は`(CompactRoot::default(), Vec::new())`。
3. `compact_reachable_role_constraints_from_seed_vars_recording_merge_constraints`は`(Vec::new(), Vec::new())`。
4. `capture_generalized_witnesses`は`(Vec::new(), ProvenanceCompleteness::Incomplete)`。

partial collector output、partial merge/role constraints、partial witness draftsは返さずdropする。raw-mode fallback、retry、second
quantification、cross-call pending stateは作らない。poisonが同attempt内の後続generalization、scheme insertion、cache insertion、
finalizationを通ること自体は許容するが、その意味論的正しさを主張しない。必要な主張は、そのattemptがterminal latchを保持したまま
checked lowering gateまたは後述のpost-format gateに到達し、poison由来のsemantic outputを公開しないことだけである。

このためimplementation testでは、proof-semantic denialを各surfaceへinjectしたattemptがpanic、無限loop、unbounded allocationを
起こさずgateまで到達することも確認する。poisonが内部不変条件を壊してgate到達前にpanicする場合、final-output gateだけでは
解決にならないためstopし、本節を再査読する。

test-only `TerminalLatchBusy` / `ForeignAttemptRoundState` injectionはorganic reachabilityの証拠に使わない。これらはterminal latchを
setしないため、full user-facing routeで「gateが必ず隠す」とは主張しない。real production call shapeからこの二variantを除外する
same-self round censusが本案の前提である。

### 4. mutable-owner cascade

HRTB gatewayは`&mut ConstraintMachine`を要求するため、前案の「caller signature不変」は撤回する。ただし変更は既に`&mut` ownerを
持つ地点までの機械的reborrowで止まり、`Result`、server route、`SourceTextAnalysis` public behaviorのcascadeは作らない。

| surface / call chain | current shape | target shapeとtermination point |
|---|---|---|
| witness collector | `capture_generalized_witnesses(&ConstraintMachine, ..)` / `WitnessCollector { machine: &ConstraintMachine }` | entryを`&mut ConstraintMachine`へ変更し、collectorは`&ScopedLegacyProjectionQuery`を保持する。一scopeがrootと全recursive Pos/Neg/Neu walkを包む |
| local witness | `ExprLowerer::generalize_local_binding(&mut self)`が`self.session.infer.constraints()`を渡す | outer signatureは既に`&mut self`。`constraints_mut()`を短くreborrowし、scope終了後にshared reborrowでfinalizeする。外側cascade zero |
| component witness | `AnalysisSession::quantify_component(&mut self)`が`self.infer.constraints()`を渡す | `self.infer.constraints_mut()`を短くreborrowする。`ancestors` / `scheme`はowned/localであり、scope終了後に`self.poly.typ`とshared constraintsを使う既存finalizeへ戻る。外側cascade zero |
| ordinary scheme compact | `compact_type_var_for_scheme(&ConstraintMachine, ..)` | `&mut ConstraintMachine`へ変更。`generalize_type_var_with_boundaries`は既に`&mut ConstraintMachine`なのでその場で終端する |
| local environment scheme compact | `add_root_vars_connected_to_environment(&ConstraintMachine, ..)`（`lowering/expr/tail.rs`） | helperだけ`&mut ConstraintMachine`へ変更し、既に`&mut self`を持つ`generalize_local_binding`から`constraints_mut()`を渡す。compact scope drop後、同helper内でshared reborrowしてenvironment reachabilityを読む |
| cached scheme compact | `AnalysisSession::compact_root_for_generalize(&mut self)`内の`self.infer.constraints()` | `constraints_mut()`へ変更。cache lookup borrowをscope前に終え、owned compact取得後にcacheを再borrowしてinsertする。`GeneralizeCompactCache`のownership/lifetimeは変えない |
| role scheme compact | `generalize_root_with_prepasses_and_metrics(&mut self)`から`self.infer.constraints()`と`self.roles.for_owner(def)`を同時使用 | `self.infer`のmutable borrowと`self.roles`のimmutable borrowをdisjoint field splitし、role input sliceとseedはscope内で読む。outer signatureは既に`&mut self` |
| input formatter | `check.rs::{format_inferred_input_type_with_path_rewriter, format_inferred_input_type_public_with_path_rewriter}`が`infer: &Arena` | 両方を`infer: &mut Arena`へ変更し、`constraints_mut()`を渡す。これはpublic Rust APIのshared-to-mutable source breakであり、本節が明示的に承認対象へ含める |
| yulang input formatting | `HoverFormatContext::format_input_type(&AnalysisSession, ..)` | `&mut AnalysisSession`へ変更。`hover_for_local_def`は既に`&mut AnalysisSession`、`source_completion_from_check`は既に`&mut PolyCheckOutput`を持つ。completion local metadataをownedでcollect後、sessionをmutable reborrowする |

`source_hover_from_check` / `source_completion_from_check` / `source_member_completion_from_check`は既に
`&mut PolyCheckOutput`を受けるため署名変更しない。`SourceTextAnalysis::hover`、`hover_from_loaded_files`、completion/member route、
`server.rs`までmutable signatureを広げない。`HoverFormatContext`はmodules / path-rewrite inputだけを保持し、whole
`PolyCheckOutput`または`AnalysisSession`のshared borrowを保持しないため、既存row 2のborrow-split形を維持できる。

test-only callerはowned `ConstraintMachine` / `Arena` bindingを`mut`へ機械的に更新する。production caller inventory以外の
signature変更が必要になれば、silent scope expansionをせずstopする。

### 5. inferからyulangへ出すexact terminal-state accessor

`ConstraintMachine::proof_terminal_failure`自体は`pub(crate)`のまま維持し、`ProofFailure`やmachine internalsをyulangへ公開しない。
代わりに`crates/infer/src/check.rs`の`PolyCheckOutput`へ次のread-only boolean accessorを追加する。

```rust
impl PolyCheckOutput {
    pub fn has_proof_terminal_failure(&self) -> bool {
        self.lowering
            .session
            .infer
            .constraints()
            .proof_terminal_failure()
            .is_some()
    }
}
```

このmethodはterminal valueのclone、failure variant、latch clear/mutation、`ConstraintMachine` referenceを公開しない。
`&self -> bool`だけをcross-crate surfaceとし、final formatterがmutable machine borrowをdropした後に呼ぶ。
名前は「diagnosticがある」「lowering errorがある」ではなくproof attemptのterminal latchそのものを問うことを明示する。

### 6. yulangの三final-output gate

gateはformatterの前ではなく**後**に置く。前checkだけでは、その直後のscheme compactionがterminal failureをlatchした場合を
捕捉できないためである。三関数の全non-empty / `Some` returnを次の一箇所ずつへ集約する。実装は、
`has_proof_terminal_failure: bool`と既存outputを受け、terminal時に`T::default()`を返すprivate generic helperを一つ置いてよい。
その場合も三production functionが最後のexpressionとして同helperへ
`check.has_proof_terminal_failure()`を直接渡し、helper後のformat/queryはzeroとする。

1. `source_hover_from_check`（current `source/mod.rs:3149`）は既存の`best`を構築した後、
   `check.has_proof_terminal_failure()`がtrueなら`None`、falseなら`best`を返す。
   `SourceTextAnalysis::hover`とfresh `hover_from_loaded_files`の両routeがこの関数を通るため、outer signatureは変えない。
2. `source_completion_from_check`（current `source/mod.rs:3222`）はsort / dedupまで終えた後、terminalなら`Vec::new()`、
   otherwise `items`を返す。`completion_from_loaded_files`は従来どおり`Ok(Vec<_>)`であり、route error contractを変えない。
3. `source_member_completion_from_check`（current `source/mod.rs:3339`）も全candidate detail formatting、sort / dedup後に同じcheckを行い、
   terminalなら`Vec::new()`を返す。既存early returnは全て既に`Vec::new()`なので安全側であり、non-empty returnだけをfinal gateへ通す。

source APIではterminal failure時にhoverは`None`、completion / member completionはempty vectorとなる。
LSP `completion_items_for_source`はordinary non-member contextでparser keyword fallbackを先に持つため、source completionがemptyでも
最終LSP responseはkeyword-onlyになり得る。これは型由来candidate / detailを公開しない既存fallback behaviorであり、
member contextはemptyのままである。hoverは既存`Option` chainによりno-hoverとなる。いずれも新しい`RouteError` variantや
server signatureを必要とせず、request cacheへ入るのはgate通過後のno-hover / keyword-only / empty resultだけである。

### 7. witness / GWCB completenessとattempt-locality

`capture_generalized_witnesses` denial時のempty + `ProvenanceCompleteness::Incomplete`は、normal-caseの既存Incompleteと値だけでは
区別できず、`quantify_component`もscheme-level completenessを独立にgateしない。この弱点自体は否定しない。本案の保証は値の
区別ではなく、同じdenialがその値を作る前に同じmachineのterminal latchへ記録される因果関係に置く。

- local/component witness、scheme record、occurrence provenanceが同attempt内でempty/incomplete witnessを参照しても、checked
  `lower_loaded_files*`はattempt終了時にterminal latchを見て`BodyLowering`全体をdropする。
- `quantify_component`はordinary quantification、scheme insertion、witness recordingを従来どおり一回だけ行い、retryや二重schemeを
  作らない。role lifecycleのquantify-once invariantを変更しない。
- same `SourceTextAnalysis` / `PolyCheckOutput`を複数回読む場合もterminal latchはstickyである。現行reuse surfaceである
  `SourceTextAnalysis::hover`は呼出しごとに`source_hover_from_check`のgateを通り、fresh completion/member routeも各自のgateを通る。
- `GeneralizeCompactCache`、generalized scheme table、witness table、occurrence provenanceは全て同じ`AnalysisSession`に所有され、
  later attemptへ移送されない。
- serverはhover requestごとにfresh `SourceTextAnalysis`を作り、completion routeもfresh `check_loaded_files`を行う。
  LSP request cacheは`AnalysisSession`やcompact/witnessを保存せず、final gated resultだけをdocument version付きで保存する。
- persistent compiled-unit artifactのcurrent in-repo production writerはchecked `lower_loaded_files`またはそのtyped-act wrapperを使い、
  terminal-failed `BodyLowering`からartifactを作らない。artifact自体も`ConstraintMachine`、`AnalysisSession`、
  `GeneralizeCompactCache`を保存しない。

従ってcurrent in-repo production graphには、terminal-failed attemptのpoison compact / degraded witnessをlater successful attemptが読む
channelは見つからない。ただし、公開されている`compiled_unit_artifact_from_lowering*`へexternal callerがunchecked
`BodyLowering`を直接渡す組合せや、後述のsingle-file unchecked dumpはこの保証に含めない。新しいin-repo production callerが
これらを使う場合は本案のattempt-isolation proofが崩れるためstopし、checked gateを追加して再査読する。

### 8. single-file dumpの扱い

`dump_loaded_file` / `dump_loaded_file_raw` / `dump_source` / `dump_source_raw`は`lower_binding_bodies`を直接使いterminal latchをgateしない。
workspace-wide caller censusではinfer自身のtest / characterization以外のin-repo production callerはzeroであり、real yulang / CLI dumpは
checked `dump_loaded_files*`を使う。本節はrow 4 / row 7確定節と同じく、このpublic unchecked surfaceをpre-existingかつ直交するgapとして
明示的に範囲外へ置く。

ただし新しいriskはzeroではない。migration後、このunchecked pathがwitness / scheme compaction denialを通ると、poison compactや
degraded witnessを含む`BodyLowering`をterminal recheckなしでdumpし得る。現行production caller zeroだから本sliceのuser-facing
correctnessを破らないが、将来callerを追加する前にsingle-file APIをchecked `Result` surfaceへ移すか、dump直前にterminal gateを
追加する必要がある。この制約をdoc commentとproduction caller census test / review gateに残す。

### 9. test impactと追加regression

current yulang hover / completion testsにterminal failureを意図的に作るcaseはなく、正常系expected outputの変更は不要である。
mutable signature化により、inferのgeneralize / compact / proof / bounds test fixtureにあるowned `ConstraintMachine` / `Arena`を`mut`へし、
callをmutable reborrowへ変える機械的compile fixは必要になる。assertionやexpected type、hover text、completion itemは変更しない。

実装時には次を追加する。

1. 各witness / scheme compact surfaceのsuccess parity、top-level scope entry exactly one、nested zero、old direct helper read zeroを
   infer側で検証する。
2. existing structural-kernel failure injectionでproof-semantic terminal failureをscopeへ入れ、gatewayがplaceholder returnより前に
   terminal latchをsetすること、partial output zero、gate到達までpanic / loopしないことを検証する。
3. `PolyCheckOutput::has_proof_terminal_failure`がclean attemptでfalse、terminal-latched machineでtrueを返すことをinfer unit testで
   実machineに対して検証する。setterやfailure variantをproduction public APIへ追加しない。
4. yulang側では三final-output functionのlast expressionが、actual
   `check.has_proof_terminal_failure()`とoutputを同じprivate gate helperへ渡す形であることを固定する。helperをterminal predicate
   true / falseの双方で直接testし、trueなら`None` / empty / empty、falseなら既存outputをbyte-for-byte保持することを検証する。
   infer側のactual-latch accessor testと組み合わせ、production setter、cross-crate test-only latch setter、feature、environment
   switchは追加しない。
5. `SourceTextAnalysis::hover` route、fresh hover route、ordinary completion、member completionをbounded targeted testで通す。
   ordinary LSP completionのterminal caseはtype-derived item/detail zeroかつkeyword-only、memberはzero、hoverはNoneを確認する。
6. infer側で同じterminal-latched `PolyCheckOutput`への複数回のaccessor readが全てtrueであることを固定し、yulang側では
   `SourceTextAnalysis::hover`が呼出しごとに同じfinal gateへ到達するcall-graph test / code assertionを置く。
7. existing yulang source/server、infer generalize/compact/constraints suiteを実行し、正常系output parityとbaselineを維持する。

boolean helperだけをtestして三production return siteがそのhelperを使わない、actual accessor testがない、またはgate後に別の
format/queryが走る場合はtest gate不合格とする。

### 10. invariant

1. **No semantic claim for poison**: denial placeholderをUnknown、Never、Any、constraint-free correct resultとして正当化しない。
2. **Latch-before-poison**: organic denialはplaceholder生成前にsame-machine terminal latchへ記録済みである。
3. **Attempt isolation**: poisonを保持するcache、scheme、witness、provenance、arenaはsame `AnalysisSession`から出ない。
4. **Checked initial output**: witness/generalization-time denialは既存`lower_loaded_files*` gateが`BodyLowering`ごと破棄する。
5. **Checked post-format output**: post-check formatter denialは三source final-output gateがtype-derived outputを破棄する。
6. **Same-self round locality**: roundは各top-level surface内でsame receiverから作り、同じreceiverへ直ちに渡す。
7. **One scope / no fallback authority**: traversalごとにscope one、nested zero、old direct proof read / raw-mode rerun zero。
8. **Exact safe surface**: cross-sibling visibilityは八owned getterと既存rev.9 projection facadeだけに限定する。
9. **No new recovery protocol**: Result cascade、retry loop、pending receipt、call-site-specific terminal escalation、latch clearを追加しない。
10. **Normal-output parity**: denialがない場合のscheme、witness、hover、completion、member completionはmigration前と同一である。
11. **Public-surface scope precision**:保証対象はcurrent in-repo checked compiler / yulang output graphであり、unchecked single-file dump、
    arbitrary external composition、未知のexternal direct formatter callerを安全化済みとは主張しない。

### 11. implementation sliceとGate / stop

implementationは次のreviewable sliceへ分ける。

1. 八owned getter、private read-source wiring、instrumentation parity、success/performance test。
2. witness captureのone-scope migrationとlocal/component mutable reborrow、denial-to-empty+Incomplete test。
3. four scheme-compaction surfaceのone-scope migration、generalize/tail/analysis/check/yulang mutable-owner cascade、success/cache parity test。
4. `PolyCheckOutput::has_proof_terminal_failure`と三final-output gate、attempt-isolation / user-facing suppression test。
5. old `scheme_projectable_lowers` production caller census zero、full infer/yulang bounded regression、public API/doc audit。

各sliceで次をgateする。

- 八getterのactual read inventory、visibility、owned return、logical-read instrumentation、GWCB hot-path wall/RSSがblocked節のgateを満たす。
- witness / compactionの各top-level callがfresh same-self round + scope oneで、round storage / forwarding / cross-self useがzeroである。
- `with_legacy_projection_query`のproof-semantic Errがplaceholder生成より前にterminal latchをsetする。
- checked lowering failureでは`BodyLowering` / compiled artifact / `SourceTextAnalysis`が生成・cacheされない。
- post-check formatter failureでは三source boundaryが必ずterminal latchを再checkし、hover None、source completion empty、member emptyとなる。
- final gateはformatter後にあり、gate check後に型format/queryを再開しない。
- request cacheに保存されるのはgate後resultだけで、document versionを跨ぐAnalysisSession / compact / witness stateがzeroである。
- normal hover/completion/member outputとscheme/witness semanticsがbyte-for-byte / structure-for-structureで不変である。
- public check formatter二関数の`&Arena -> &mut Arena` API breakがrelease note / caller censusで明示され、未知のin-repo callerがzeroである。
- unchecked single-file dumpとarbitrary unchecked lowering-to-artifact compositionに新しいin-repo production callerがzeroである。

次のいずれかを検出した場合は実装を停止し、本節を再査読する。

- `TerminalLatchBusy`がactual safe production pathからtyped denialとして返る。
- row 1残りのsame-self immediate round localityが維持できず、`ForeignAttemptRoundState`がorganicに到達し得る。
- terminal proof-semantic Errがgateway return前にlatchされないvariant / branchがある。
- poisonがgate到達前にpanic、infinite loop、unbounded resource use、process-global semantic mutationを起こす。
- `AnalysisSession`、generalize cache、scheme/witness/provenance、ConstraintMachine、またはungated poison-derived compiled surfaceが
  later successful attemptへ再利用されるchannelが見つかる。
- 三source gate以外にcurrent in-repo production hover/completion/member outputがあり、terminal checkを迂回する。
- final gate後にformat/queryを行うため、checkとreturnの間に新しいterminal failureが発生し得る。
- hard Result cascade、semantic fallbackの正当化、raw direct-read fallback、retry / pending stateが必要になる。
- public API compatibility要件が`check.rs` formatterの`&mut Arena`化を許さず、別のauthority設計が必要になる。
- external/public unchecked dumpまたはartifact compositionまで同じ保証範囲へ含める必要が生じる。

本節が許可するのは、八owned getter、row 1残りpure-read migration、その必要最小限のmutable-owner cascade、boolean terminal accessor、
三つのyulang final-output gateとそのprivate pure helperだけである。`CompactRoot::default()`の意味、proof failure分類、publication、
write authority、cache lifetime、server error contract、row 2〜7の確定設計を変更しない。

追記著者: Codex gpt-5.6-sol（xhigh）が起案、Claude (Sonnet 5) が独立査読予定

追記状態: **draft・未承認（2026-08-15）**。第五案は、四案が失敗した「内部fallback値を正常な意味論値として証明する」問題を
解こうとせず、attempt-local poisonをchecked attempt boundaryと三post-format terminal gateで外部から隔離する案である。
独立reviewが上のattempt-isolation、same-self reachability、三gate completeness、public/unchecked residual scopeを全て確認するまで
implementationへ進まない。
