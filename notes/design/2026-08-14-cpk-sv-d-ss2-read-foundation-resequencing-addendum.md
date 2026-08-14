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
