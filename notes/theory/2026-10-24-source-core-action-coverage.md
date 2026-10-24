# Source から生成する修正核の全制御経路と失敗終端

Assignment **SOURCE-CORE-COVERAGE-20261024/r3**. Authors: `/root/astra_corrected_machine` (r1), `/root` (r2 failure-mode abstraction; r3 arm-result boundary wiring and integration); no descendants. Outcome: independently reviewed candidate-core construction. Revision 2 passed the failure-abstraction review but had one MAJOR arm-result wiring omission; revision 3 repaired it and passed independent delta review. Section 7 closes failure-control/effect coverage by proving absorption and using a failure-only abstraction; exact terminal-world cleanup remains unspecified. This is not a compiler correspondence theorem, semantic adoption or whole-language closure.

Contract SHA-256 `150ae87579a4a3574608d21ecc4188402a846e950b2edbd78034f5f87542e84e`; baseline supplied by primary `987ee3902a12f9c1e972d5db4b876ad60cff89b8`. Requested model/effort Astra/medium; observed model/effort/duration UNKNOWN. The resumed assignment has its own exact output lease; the previous CM artifact remains frozen.

## 1. Parent, scope and exact dependencies

The immediate parent is H5 in `notes/theory/2026-10-24-correlated-handler-observation.md`: given initial-cell coverage, action coverage and adequate finite interfaces, all finite concrete prefixes are included in TABLE. Here initial-cell generation and action locations are constructed from a finite resolved-source derivation, rather than assumed as properties of an arbitrary supplied graph. The larger parent remains source type soundness (`thm:repaired-source`, S:2486–2509), the original approved source domain and all independent A/B, natural inference, principality, termination and foreign-continuation quantifiers.

Frozen inputs checked against the contract:

| Abbreviation / path | SHA-256 |
|---|---|
| CM: `notes/theory/2026-10-24-corrected-machine-simulation.md` | `fffb4f1540739020a0702d4f7b07d41cd9b68a9063f36d24292914b84e6b606d` |
| H: `notes/theory/2026-10-24-correlated-handler-observation.md` | `fd3a901a738f24b18d8c21acdb2dc451fe192da0b54a4aa5b674c3aaea8789f0` |
| R: `notes/theory/2026-10-24-cooccurrence-source-recipes.md` | `ee99b45dbc49c3563220335b350814ed422bf0fbe7edfcb4cfaef476da986cdb` |
| Authority: `notes/design/2026-10-24-cooccurrence-release-clarification.md` | `c9eb9b8d274172f02bc82088896c30dd92e219a02adf6ba22418b2cc34207d12` |
| O: `docs/yulang-operational-type-safety-ja.tex` | `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b` |
| S: `docs/yulang-source-type-safety-ja.tex` | `2c77bbd6f2679ac91ece3bb670152a9dfd16e033aa68545bff6c6dc509d24166` |
| D: `docs/yulang-dot-selection-safety-ja.tex` | `47b7fcec1f501e7c326ab9859885e329aab2730066806ea79212e825ebb32b0b` |

CM revision 1 was authored by this worker; its missing Extend/Fork/Rejoin arguments were repaired by the primary in revision 2 and independently reviewed. Only the corrected dependency is reused. H is by `/root/astra_scoped_join`, R by the primary, with the receipts present in their frozen files. Manuscripts retain their existing authorship. Direct primary messages supplied pointers to eapp and Fail; their conclusions are checked against the pinned text here.

The authoritative co-occurrence correction supersedes the old “choose all inputs or selected inputs” question. Use R's tagged recipe construction when its finite signature graph is present. This note does not adopt arbitrary `A_all`, equate receipts by a common display variable, or assert finite-interface adequacy for nonregular instances without evidence.

## 2. The input is a derivation, not an execution graph

An input d consists of a finite resolved derivation for the thirteen expressions and eleven patterns of S:268–323, Let/Expr/Module statements, ordered roots, finite declaration bodies, and direct boundary/selection evidence from D. Code references and guarded recursive value references may form a finite graph. First register their labels; never recursively expand a reference merely because it is encountered. Evidence variables are either bound by a qualified abstraction or supplied with their own finite direct derivation; arbitrary code of the same endpoint type is not direct evidence.

Finite interface adequacy is an explicit independent hypothesis: each template has finite cell signatures for operands, results, current world and the pending immutable data needed by its actions. This does not bound concrete identities, witness count, target count, stack depth or execution length. It also does not presume the conclusion that generated actions cover concrete transitions.

Define `El(d)` by the syntactic clauses below, using finite body references for recursion and the original evaluation order. Annotate each generated instruction by `(derivation-node, clause, position)`. Each label has entry `in`, exits `ret`, `req`, `fail`, and finitely many internal phase locations. Allocate labels for **all** body instructions, including dormant lambda/delay/eabs bodies, adapter bodies, defaults and guards. Dormant bodies receive no execution seed solely from allocation.

`Gen(d)` is produced by two finite traversals:

1. Elaborate the finite derivation graph, registering labels before children and storing finite capture/recipe templates. Compile references as jumps to registered body entries with formal-input substitution.
2. For each generated instruction, instantiate its administrative template in §4, connecting ordinary child-result exits and seven-frame request productions. Instantiate no edge by consulting a concrete reachable trace, checking safety, or assuming H5. Use CM relations, H's filters/Rejoin/Prep, and finite identity/substitution/control routing on already typed scalar constructors. Those scalar routing relations are explicit constructor-tag alternatives, not metadata oracles.

Locations are finite: expression/pattern/body labels times their finite phase/arm/component indices and tags. Runtime stacks are **not** location indices. Their finite grammar and summary closure are generated separately in §6. All failure exits enter the failure-only channel constructed in §7. The unchosen terminal-world cleanup policy is recorded separately; it is not silently an edge with a chosen normal-world effect.

## 3. All source clauses and finite generation induction

The following clauses fix the structural recursion, including the cases that share administrative templates.

| Source constructor | Finite emitted skeleton and child traversal |
|---|---|
| Lit | Ret of its literal; create root view using CM Extend as appropriate. |
| PrimitiveOp | Finite arity-curried callable containing the fixed primitive instruction; allocate body labels without running them. Primitive result alternatives are those in O:883–925, including allowed Fail tags. |
| Var | Lookup an already bound value, then the recorded finite type/qualified-use applications. Existing computed roots are fetched, never reinitialized. |
| App | Evaluate callee once by bind; construct a delayed argument body; execute complete Call with the supplied direct argument/result adapters. |
| RefSet | Evaluate reference then RHS once; invoke resolved StdRefUpdate protocol code, with its finite recursive/handler body registered. |
| Lambda | Construct closure capturing the exact lexical slots; register entry, parameter-pattern and body labels. Value and Computation entry remain distinct. |
| Tuple | Ordered component binds followed by tuple introduction; delayed components remain values. |
| Record | Ordered Field/Spread RHS binds, then right-biased visible-map construction. Overwritten RHS is still executed; absent optional field does not overwrite. |
| PolyVariant | Ordered payload binds followed by the specified tag/arity introduction. |
| Select | Compile the actual M/R/F evidence tree in D:790–855. M retrieves/instantiates the member then calls Wrap(f,a,r) on Delay(receiver); receiver is not pre-forced. R retrieves its finite dictionary/member plan. F evaluates its receiver and direct boundary then projects. |
| Case | Evaluate scrutinee; use ordered value-pattern/guard/body attempts. Each successful body return enters its supplied direct result boundary before Yes/common result. Adapter Req/Fail use ordinary exits; all-No is MatchFailure. |
| Catch | Register scrutinee and all operation/value attempts, with paired payload/response instances and typed raw continuation formal; use §4 Search/Wait. Any supplied arm-result boundary is executed after that body returns and before Yes/common result. |
| Block | Fold the finite statement sequence left to right, respecting lexical extensions and final result. |

Patterns:

| Constructor | Generated plan |
|---|---|
| Wild | Ret Yes(unit). |
| Var | Ret Yes(input tuple), with actual binder transport/Receive. |
| Lit | Literal kind/value comparison and both Yes/No constructor branches. |
| Tuple | Shape/arity check then ordered child matches; first No stops. |
| List | Finite shape/length check; prefix/suffix child matches and the actual middle rest sequence. |
| Record | Ordered visible lookup; present child or absent default in prior-binder environment; absent without default is No. |
| PolyVariant | Tag/arity test and ordered payload matches. |
| Con | Nominal/constructor/instance test and ordered payload matches. |
| Ref | Retrieve resolved definition instance, execute specified equality code, branch on bool; no new pattern binder. |
| As | Run child, append original input alias only on Yes. |
| Or | Run left; only No invokes right; successful branch transports the common public binders through its direct merge evidence. |

Each pattern's Yes environment feeds its guard; guard true feeds the following explicit result plan, false returns No. For each Case arm, and each Catch value/operation arm whose derivation supplies a direct result boundary b_i from its body type A_i to the common result type B, generate:

```text
let z <- El(body_i) in
let y <- El(b_i, z) in
Ret Yes(y)
```

`El(b_i,z)` is the actual direct-evidence plan from that same arm, instantiated with the same type/family/profile data. If the derivation supplies an identity boundary, its plan is `Ret z`; equality of endpoint types alone does not permit skipping supplied effectful evidence. Register a distinct body-return-to-boundary entry connection and a boundary-return-to-Yes connection. The first bind propagates body Req/Fail; the second propagates boundary Req/Fail and captures its remaining `Ret Yes(y)` suffix on Req. No request or failure from either stage becomes No. For a Catch arm this whole plan runs outside the selected shallow handler; an adapter's genuine source Call still allocates its own ordinary receipt. An earlier pattern/guard No bypasses both body and result boundary. Request and Fail propagate from default/equality/guard/body; neither is converted to No. No discards lexical trial bindings but never rolls back current world. A failing lambda parameter match produces MatchFailure, not a skipped invocation.

Let has two clauses: a guarded value SCC allocates the finite rec graph once; a computation binds its result once and extends the following environment. Expr evaluates and discards only its normal value. Module traverses its resolved value table and ordered root sequence. Root composition is the same ordered bind fold under the root owner; it never admits a fetch from an uninitialized computed binder. The source/linker proof that an actual frontend supplies this resolved environment is outside the input-domain theorem.

Direct evidence is compiled simultaneously: identity/top use Ret, union/intersection use explicit injection/unioncase/choose, tuple/variant use split/switch and child transformations, record uses required field or guarded optional lookup, Function constructs Wrap, thunk constructs a delayed Force-and-adapt body, nominal uses its registered mapper, operation uses paired mapop, and declared cast/accessor uses its finite body. Guarded recursion is a label reference. No transitive direct boundary is fabricated. Type substitution and qualified evidence substitution traverse the same packet, preserving origin identities.

D:153–221 adds `eabs^k p.N` and `eapp(f,d)`. Allocate N's body label. E-beta substitutes d and enters `View(f,admin.effect,N[d/p])`, with separate admin.result transport. Mode g includes all body effects; mode a uses D's restricted acquisition grammar, also traversed structurally. Neither creates a source receiver/receipt. A real source Call in a general body still uses ordinary Call. This closes the instruction gap that would result from compiling O's grammar alone.

**Lemma G1 (finite syntactic generation and source locations).** For every input d, El and Gen terminate; every source/evidence subderivation and every administrative instruction they emit has a registered template and ports. The failure channel is defined in §7 without selecting a terminal-world cleanup policy.

**Proof.** Simultaneously induct on the finite expression, pattern, statement and direct-evidence derivation graph, with a visited-label table for references. Lit/Var/Wild/primitive leaves allocate a bounded finite skeleton. For each ordered aggregate, its finite child list supplies smaller derivations; concatenate the already constructed templates with binds, adding one phase per child. Shape tests add two finite constructor alternatives. Lambda, delay and eabs register a value and a body entry; construction visits the finite body once, not its future executions. App/Select/boundary clauses combine their smaller source/evidence children with the listed finite Call/eapp/wrap templates. Case/Catch combine a finite arm list, each already constructed pattern/guard/body and supplied direct result-boundary child, with Search/Wait. For each arm the two displayed binds explicitly connect body.return to its boundary.entry and boundary.return to Yes; their request/failure exits use the already constructed bind productions. Thus registering the evidence body is accompanied by an actual execution connection. Or adds exactly two child plans and the finite common-binder transports. Statement/root induction adds one finite sequence element and its lexical bindings; a recursive reference adds an edge to an existing label. Recipe construction uses the finite signed signature graph of R, not latent-event enumeration. All clauses reduce the finite traversal measure or terminate at a registered reference. §4 allocates a finite number of phases for every emitted instruction, so it too terminates. ∎

This is structural generation, not an inference termination or runtime termination theorem.

## 4. Administrative templates with all exit kinds

Every active-child invocation receives current world and immutable operands. On normal return its **current** output world is passed to the parent successor. Saved operands in the frame store Imm only; reconnect them by CM Rejoin when execution returns after an effectful child. Relation labels below expand into finite CM operations and H formulas.

**Basic control.** Ret connects to ret; a listed primitive/switch failure connects to fail with its failure tag. Bind-ret substitutes and enters its suffix. Force enters the saved delay body under the force View. Split/field/lookup/unioncase/choose/unroll/type application/graph lookup take precisely their constructor alternatives. Rec allocates a fresh finite graph then enters its body; template application jumps to the registered body with simultaneous parameters. No recursive body is statically unrolled. Emission makes one fresh event with the actual currently executing Views via Extend/Fork; request propagation never reseeds it.

**Call/entry.** Call allocates one owner and enters its scope and complete CallView. Wrap peeling adds a delayed argument adaptation and a result-adapter bind using the same owner. Terminal source entry emits its source receipt/profile actions before any Value force. Value then Force-carrier → parameter plan → body → declared-result consumer → result adapters. Computation binds the retained carrier and invokes only its explicit body/pattern force actions. No unconditional force is inserted. Receipt reservation without protection creates no witness; actual protection/upper-use creates Extend rows. C-Close/alias/captured lookup, F-Seed/F-Owner/N-Transfer use their explicit fresh/lookup/transport actions and the actual receipt recipe. New routes use Fork, never Map from an empty population. A finite unknown-origin observation uses Refresh, not guessed ownership.

**Scope/View.** Normal scope completion uses CM own/borrow completion, restores the previous control slot, and preserves immutable receiver evidence. View-ret transports the result port then restores its outer executing View contribution. Request crossing captures the frame descriptor and uses the current-world suspension action; it is not normal completion. View-request retains the same event, its original Observe evidence and the saved suffix. Failure enters §7's failure-only channel, whose observations do not read a mutable world.

**Search.** Operation search locations are `(handler-label,operation-instance-slot,arm-index)`. Prep builds the current joint query. Both edges `F_0;Next;Prep` and `F_1;Invoke` are generated. The true edge executes the attempt outside the selected handler; its continuation formal is the original K. On exhaustion the operation path forwards `Req(q,p,H_hK)`. Value search has distinct tags and all-No reaches MatchFailure. Its exhaustion never forwards an operation. Inapplicable instance/coverage is a false-search edge, not an untyped arm invocation.

**Wait.** Wait contains Imm(q,p,K), remaining arm descriptors and its active attempt, including the body-result-boundary binds above. A normal body result has not yet reached Wait.Yes: it first enters its own direct boundary. A boundary request captures the bind suffix before the wait frame; its failure enters Wait.fail. Only normal boundary return constructs Yes and returns the current result. No executes Rejoin of Imm and the attempt's **current-world output**, then Next/Prep and both filters. Attempt Req(q',p',K') emits q', while appending the wait frame with the original pending q,p,K to K'. q is not re-emitted or unioned into q'. Attempt Fail propagates Fail without falling through to the next arm; §7 erases the unobservable post-Fail world rather than choosing the pending activation's cleanup. A failing guard is not a false guard.

**mapop.** Ret returns unchanged value. Matching Req runs payload adapter a outside the mapper, then forwards the same event identity at the paired target instance with adapted payload. Its response continuation runs r outside the mapper before the saved suffix under mapop. Nonmatching Req retains payload/instance and captures mapop. a and r are ordinary effectful registered code with all exits; their requests are not automatically remapped by the same mapper. Fail propagates its failure tag. Adapter application is eapp or registered template; arbitrary source-call receipt is not added.

**release.** Target introduction uses the finite tagged recipe and immutable B_t. Ret forks/transport t onto its result and leaves L unchanged. Req performs actual R-Cross, updates only the selected `(s,t)` pairs, forks the transported current packet and captures the same release suffix; underlying event is not fresh. Fail uses S:1822–1823, preserving W,L and its failure tag. Ordinary child transitions run inside the delimiter; no crossing occurs for a request already consumed inside. H/Origin remain route-relative.

**Resume.** Raw Resume enters the captured **suffix entry**, supplies the response and current resumer world, applies Rejoin and reconstructs captured control slots via L-Enter. It never jumps back to the source Call/receipt entry. Public resumption is a separately generated Value callable whose own entry precedes raw Resume. Repeated uses instantiate the same descriptor with fresh control/activation occurrences where required, keeping old allocated evidence, scope and target identity. Foreign bodies require their own introduction/reentry contract; no edge in this construction proves it.

**Failure ports.** Every template has a failure-control exit. Bind discards its suffix; lookup/default/guard/eapp/mapop bodies propagate the same failure; release has the explicit world-identity rule above. Scope, View, handle and wait connect only to the failure channel of §7. The graph never equates this channel with No, Ret or request suspension. Exact terminal-world state is outside its observation interface; all pre-failure worlds and all ordinary No/resume paths still use CM/H joint cells.

## 5. Configuration invariant and transition induction

A runtime configuration is represented by `(ell, phase, environment, current world, stack)` plus saved continuations. Environments are typed substitutions into registered template formals. Each active stack frame is an instance of a generated frame descriptor with its return label; each saved K is a finite word in the generated seven-frame grammar. A pending wait has separate immutable data for q,p,K and a current-world port belonging to its active child. Past mutable query bits are absent from its Imm.

Define `Loc_d(x)` by these syntactic conditions. It does **not** require every owner in world support to be active, identify stack ownership with all historical identities, or claim TABLE membership. In particular no semantic safety or action coverage is hidden in this invariant.

**Lemma G2 (location preservation and explicit administrative coverage).** Starting from El(d), every specified non-failure administrative transition preserves Loc and follows a generated finite administrative path. Failure propagation preserves the syntactic location/stack invariant and reaches the failure-control exit; its abstract relation is proved in G4 below.

**Proof.** Initially the root label and the registered value environment satisfy Loc by G1. Suppose Loc holds. If the active instruction selects a child, the structural skeleton provides its child entry and corresponding frame return label; substitution changes operands, not labels. For a basic redex, §4 lists the literal constructor cases: a normal result reaches ret, a primitive failure reaches fail, a branch reaches its labeled arm, template/rec/type/eapp steps enter already registered bodies. Metadata insertion/transport is the specified Extend/Fork/Map action, followed by current derived observations.

For child Ret, inspect its top frame. Bind chooses its suffix label; in every successful arm-result plan the first suffix is that arm's registered direct boundary and the second constructs Yes. The boundary's own body is covered by the direct-evidence induction, so its Req/Fail also traverse the bind/request/failure templates rather than disappearing between body and Wait.Yes. Scope/View uses its normal-completion/result template. Handle begins the finite value-arm search. mapop returns. Wait distinguishes Yes from No by result constructor; No goes through Rejoin/Prep, rather than reusing its entry cell. Release transports t. These cases exhaust seven frame descriptors. The new active labels and retained frame descriptors remain generated.

For child Req, bind/scope/View/mapop/release append their corresponding descriptor to the saved continuation; handle distinguishes both query outcomes and operation exhaustion; wait saves the original pending data and appends wait around the new request's suffix. Source-order/instance dispatch uses finite arm-index alternatives. H1 ensures the actual query cell belongs to the selected F_b, and both b edges exist by construction. Selecting an arm removes h from its execution context; forwarding inserts h into H_hK only. Every resulting continuation remains a word in the grammar, proved separately below.

For child Fail, the structural propagation rule O:331–334 supplies the parent failure-control exit, and it never enters the parent's normal suffix. Release has an explicit unchanged-world transition. Stateless bind/control routing has no ownership update. For a world-owning frame, the syntax still reaches fail and Loc's label invariant is preserved, and §7 gives a failure-only relation without claiming an exact world update. No assertion about that update is used in this induction.

Raw Resume uses the saved grammar word and current input; substitution supplies the response only at its hole, never at a source entry. The next labels are therefore exactly the registered suffix labels. This covers the final administrative case. Each case derives its path from a constructor/template already allocated by G1; it does not assume that some graph edge must exist because the step is safe. ∎

## 6. Seeds, frame words and the nested discriminator

Closed initial seeds are constructed by finite value-derivation recursion: literals/empty metadata use their constructor cells, structures combine jointly represented components by their actual constructor relations, closure/delay/eabs construction records code/capture templates without running body ports, and rec introduces the registered immutable graph references. The initial world is the declared empty history followed by the generated root entry. For qualified/formal inputs, enumerate all syntactic joint cells satisfying the supplied finite type/profile equations, including the actual input cell; this is a finite set, not an assumption about safety. Unknown derived observations are all refinements. Initial containment follows from constructor equations and CM Extend/Fork, by induction on this finite value construction. Open foreign-code contract validity remains independent.

**Lemma G3 (capture grammar and finite closure).** Every captured continuation produced while Loc holds has a derivation in the generated seven-frame grammar, and its finite summary is included in CM's simultaneous code/cut closure.

**Proof.** A fresh perform has the empty frame word and Ret-response hole. Induct on the finite number of propagation steps. A crossed bind/scope/View/mapop/wait/release contributes exactly the descriptor from §4; an unselected/forwarded handle contributes handle. A selected handle contributes nothing to the arm's K. G2 supplies every descriptor and suffix label. This builds the grammar derivation, independently of execution safety. At raw resume, induction on that finite word reconstructs each frame with the response hole and present world, so the suffix entry is registered. At every resume repeat the induction for that same saved word; no bound on the number of resumptions is used. CM §6 supplies finite monotone-function closure for the fixed interfaces; induction on the grammar derivation puts its composite in that closure. The extra failure-control ports are finite; their interpretation and closure are supplied by G4, independently of a normal-world cleanup rule. ∎

**Discriminator: attempt → request → resume → No.** Begin at Search_j with q and a true F_1 cell. Invoke saves Imm(q,p,K) and executes the attempt outside h. Suppose the attempt emits q' after changing L. Its Req exit captures `wait_h(q,p,K;[-])` in q''s continuation; the immutable pending q remains distinct from q'. After any finite typed intervening computation, raw resume of that continuation Rejoins the present world, reconstructs the wait descriptor, and executes the saved attempt suffix. If this suffix returns No, its **output** world feeds Rejoin(Imm(q),world), then Next_k/Prep_k and F_0/F_1. This path is generated by the Wait and Resume templates, G2, and G3; no extra source syntax case is assumed.

Take H's concrete-state discriminator: q has one relevant witness with H={t}, initially L(s,t)=0; j has authentic concrete grant. During the attempt an actual crossing changes L(s,t) to 1 while the original receiver remains active. At k, with Base=1 and no concrete/wildcard grant and no other protection, current P=0 gives F_1. A snapshot path would choose F_0. The constructed path supplies the current state at both resume and No. This is a discriminator of the candidate administrative transitions, not a claim that a particular accepted source expression realizes every chosen bit assignment.

Replace the resumed attempt's No by Fail: Wait.fail is reached, no Next_k or pending-q reemission occurs. If Fail then exits scope/View/handler ownership, G4 propagates its failure tag in the failure-only channel. There is no edge from that channel back to a world-query/No path. Thus the proof does not certify the No path by silently treating every abrupt exit as No.

## 7. Fail の吸収性と、全 prefix に対する効果包含

### 7.1 具体的な cleanup と観測対象

O:331–334 は active child の Fail を同じ Fail として伝播すると規定する。O:388 は Scope の **Ret** での owner 終了を明記し、S:409–410 は own/borrow の completion を区別する。一方、Fail 伝播時にどの saved control slot や ambient View を復元するか、pending wait activation をどう退役させるかは明記していない。r1 はここを `FailWorld` という残項にした。

r2 は具体的 cleanup を補って承認済み意味論と呼ぶことをしない。次の制御上の性質を証明し、**失敗して以後読まれない world を抽象表示から消す**。全 source 構文と失敗する実行を対象に残す。外部 host が失敗後の内部 world を読み取り、保存した継続を再起動する意味は本節の定理に含めない。その契約は独立の foreign/reentry 義務である。

### 7.2 失敗吸収補題

active evaluation context を次の七 frame の有限列とする。

```text
E ::= [] | let x <- E in N | Scope E | View E | Handle E
       | mapop E | wait(saved; E) | release E
```

ここで `View E` は O の expose frame を含む。`enter`、`eapp`、template、型適用は redex であり、operand 待機用の追加 frame ではない。lambda/delay/eabs の body や保存済み continuation の内部は、実行されるまでこの active context に入らない。

**補題 G4a（失敗の吸収）。** `E[Fail r]` に達した後、同じ核実行の後続は Fail の伝播だけである。各伝播は frame を一つ除き、有限回で最外の `Fail r` に達する。新たな Ret、Req、Call、Resume、query、guard/default/body の実行へは移らない。

**証明。** frame 数に帰納する。空列では Fail は終端であり適用できる規則がない。非空列では最内の active frame の child が Fail である。bind/scope/expose/handle/mapop/wait の六場合は O:331–334、release は S:1822–1823 の失敗規則だけが適用できる。各規則は同じ r の Fail を一つ外へ渡す。bind の suffix、handler の値 arm、wait の Yes/No、mapop の payload/response adapter、release の Ret/Req 規則は各々別の結果 tag を要求するので適用できない。外側への context 規則もこの同じ一段を持ち上げるだけである。残る frame 列へ帰納仮説を使う。body が以前に実行した効果を取り消す操作も、失敗を No に読み替える規則もない。□

この補題は world 更新の式を使わない。既存の原子的 Fail 伝播規則の制御部分に依存する。失敗を catch して計算を再開する新しい規則や cleanup callback を将来追加するなら、その言語への適用前に補題を再検査する必要がある。

### 7.3 失敗専用の有限表示

非失敗の control location には、従来通り CM/H の全 joint cell を用いる。失敗 mode の location には、有限の failure reason tag だけを置く。記号を `f_r` とし、code location と七 frame の型付き接続は graph/grammar 側に保持する。**world、activity、L、immutable evidence、pending packet の全部をこの mode では忘れる。** world の一部を固定したまま残りを恣意的に更新する操作ではない。

具体的 configuration の抽象化を次で定義する。

```text
Alpha*(x) = (failure location, f_r)  if x = E[Fail r]
            (ordinary location, Alpha_CM(x)) otherwise
```

dynamic stack は引き続き G3 の文法で表示し、有限 cell の添字にはしない。`f_r` の種類は O の列挙済み reason 集合で有限である。各 code/cut の domain を通常 port と failure port の有限直和に拡張する。

生成される追加 relation は次の二つだけである。

1. 既存構文が r の失敗を生成する枝から `f_r` への辺。primitive の列挙された失敗、switch/値 arm/parameter match の不一致末尾が該当する。r を出しうる入力から `f_r` を含め、数値等を cell が決定できない場合は、その primitive に列挙された全失敗候補を残す。
2. 七 frame の child failure port からその frame の failure exit への `f_r -> f_r`。同じ frame の normal/request/No port へ向かう辺はない。最外の failure port は終端である。

外部契約が明示的に許す failure result も、その契約の入口に同じ枝を持つ。外部コードがその契約を満たすことは本稿では証明しない。`Bad` を列挙された failure へ変更する辺もない。Bad の排除は独立の値型保存・canonical forms による。

**補題 G4b（failure step の表示保存）。** 全ての具体的な失敗生成および伝播 step の Alpha* successor は、上記の生成辺に含まれる。Scope/View/handle/wait の内部 world 更新を一意に選ぶ必要はない。

**証明。** 最初の失敗生成は有限の constructor/primitive alternative から r を決めるので、辺1にその `f_r` がある。その world を一切検査しないため、具体的な successor がどの world でも同じ像を持つ。既に `E[Fail r]` なら G4a により次は同じ r を一つ外へ伝播する場合だけである。辺2がその像を含む。これは将来必要な world 観測を捨ててもよいという無前提の抽象化ではない。G4a が、捨てた後にその観測を要求する successor が存在しないことを先に示している。□

**補題 G4c（failure channel の有限 cut 合成）。** 拡張後も code/cut closure は有限の単調系であり、全ての有限 frame 列の失敗伝播を含む。

**証明。** 各 frame は追加 port で reason tag を恒等輸送する有限 relation である。通常側の CM/H relation と直和を取り、失敗生成の辺を加える。全て powerset 上の relation image なので単調である。有限 lattice 上の monotone function と code port の積を取る CM §6 の構成をそのまま適用できる。frame 列の長さへの帰納で、各 `f_r` はその列の外側 failure port に含まれる。これは frame の動的個数の上限を仮定しない。□

### 7.4 親への適用

**定理 G5（生成 graph の全制御経路包含）。** 有限な入力導出 d、適切な有限 interface、与えられた qualified/foreign introduction 契約の下で、Gen(d) の閉包は `El(d)` の全有限実行 prefix の Alpha* 像を含む。ただし Bad に至る raw 不整合の排除には独立の実行型定理を用いる。source を「失敗しない式」に制限しない。

**証明。** §6 の導入帰納法が seed 包含を構成する。通常の各 step は G1/G2 の source/administrative template と CM/H の局所 relation により表示され、capture/resume は G3 による。失敗生成・伝播は G4b/c による。以上から H5 の action coverage 前提を、与えられた graph の未証明な性質として仮定せず、Gen(d) について導出した。ここで初めて H5 の有限 prefix 帰納法を、追加 failure port を含む有限 graph に適用する。まだ失敗していない地点は CM の全 joint cell、失敗後は同じ r の failure cell が各該当 node に入る。□

従って、Gen(d) の mandatory inclusion を満たす証明書があれば、実際の outward request と latent/reentry 実行の対応する効果包含が得られる。失敗後には追加 request が出ないので、空の outward port からの request 不発生も保たれる。この結果は failure reason を保持するが、失敗後の内部 world の equality や lifecycle invariant を主張しない。type preservation/progress 自体、nonregular instance を含む有限 interface 構成、全 surface 展開、foreign code 契約、候補政策と承認済み意味との一致は別の義務である。旧小 annotation の証明書がこの graph に適合することも自動的には得られない。

### 残る義務と反証条件

| ID / owner | 必要な証拠と反証条件 |
|---|---|
| CORE-TERMINAL-WORLD / primary concrete-semantics owner | Scope/View/handle/wait の失敗時の具体的 cleanup を必要とする完全状態意味論・host 契約を確定する。G5 の効果包含とは分離。失敗後の world を読む host continuation は G4a の適用外。 |
| CORE-FINITE-INTERFACE / representation owner | 全 template の有限 signature、nonregular type instance の equality と pending/current joint tuple の対応。必要な endpoint/query を表示できない具体例が反証となる。 |
| CORE-SOURCE-NATIVE / original constructor owners | 実 frontend が同じ順序・template を生成すること。Value force の先行、Computation の無条件 force、eapp の receipt 生成、false filter 欠落、resume の entry replay が反証となる。今回の実装除外を維持する。 |
| CORE-FOREIGN / foreign-continuation owner | imported callable と応答の独立した introduction/reentry 契約。source 内の frame 帰納法だけでは満たせない。 |
| CORE-PARENT / primary | G1–G5 の独立査読後、元の source 定理へこの生成 graph の範囲で適用する。全言語、元の A/B、推論自然性、主型性、停止性をこの局所閉包と同一視しない。 |

## 8. Checks, boundaries and stop receipt

Seven direct dependency hashes and contract hash matched. Source references were inspected directly, including O's failure/context rules, S's lifecycle correction, D's eapp and M/R/F rules, and the accepted CM/H formulas. Mathematical checks are structural induction, administrative case analysis and frame-word induction; no runtime tests or probes were run. Three stages used: finite generator; location/frame construction; parent application and failure obstruction. Grant 190 seconds/three stages; exact observed active duration UNKNOWN, no refund asserted.

The only new/written path is `notes/theory/2026-10-24-source-core-action-coverage.md`; no scratch paths. No production code/tests/configuration/Git/network/children. Prior proofs are reused only in their corrected finite-interface candidate scope; no stale snapshots, witness collapse, swallowed effectful defaults, withdrawn AllowAll bypasses, or source receipt replay are restored. Ordinary Simple-sub generation, accumulation, propagation, levels, extrusion, qualifying intrusion and generalization remain unchanged and unproved by this note.

Revision 1 was frozen at SHA-256 `e5360180508ace0c2881867ab37db8d112d80fe37091f38fa0318b6c8e038e62` with explicit write cessation and zero descendants. Primary acknowledged intake and took the lease before revision 2. Primary added G4a–G5, the failure-mode abstraction and corresponding cross-references; terminal-world cleanup remains unchosen. No extra child resource grant, tests, code edits or semantic adoption resulted. Revision 2 SHA-256 `e87bd34872d728f1c5e498749ff5f048da9bae127f196a30ef224de156c5f360` received an independent review accepting G4 but rejecting full G5 coverage for the omitted successful arm-result adapter connection. Revision 3 adds exactly that connection, its Req/Fail behavior and the G1/G2 induction cases; the reviewer stopped before these edits. Independent delta review of r3 accepted the repair and closed the MAJOR finding. Neither author self-certified it.

Independent review receipt: `/root/astra_semantics_review` accepted r2 G4a–G4c and r3's result-boundary repair, hence G5 for the explicitly generated candidate core under the stated interface/value/foreign premises. Reviewed r3 SHA-256: `fd1d7cf33dd7c317b44694cb131d63fa7cb30368cab4de0ec53f81315c3057fa`. This post-review change updates status and adds this receipt only; mathematical text is unchanged. Reviewer stopped with no writes or descendants.
