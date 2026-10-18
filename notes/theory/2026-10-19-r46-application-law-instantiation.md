# R46: instantiate Application formation at the original `loop y` occurrence

Status: frozen candidate source/native audit and bounded law non-applicability;
not a reviewed theorem, semantic selection or production authority.
Author: `/root/r46_application_law`; no coauthors or descendants.
Assignment: `R46-PROOF`, artifact revision 1. Requested model/effort:
Sol/high under the proof packet; observed effective model/effort: UNKNOWN.
Baseline supplied by Luna: `55ed588e7`; no Git inspection performed.
Contract: `tasks/agent-loop/sprints/source-apply-owner-20261019-r46.md`,
revision 2, SHA-256
`d7d7e1cf123bce1b51eec1bd599f47faac75aa7b75d41f9a1a7030440855ef62`.
Revision 2 was acknowledged before using its five direct formation-law pins.

## 1. Parent application and result

The unchanged parent is the full inference/evaluator theorem and original
Simple-sub A/B, with the original accepted source domain, semantics and
quantifiers; **OPEN, 0 → 0**. All original environments, compatible worlds,
joint valuations, independently admitted challenges, complete observations,
pending/resumed developments, providers and future uses remain required.
F1 and FK1 remain distinct independent obligations. No local frame operation
establishes arbitrary foreign-continuation legality.

This audit closes a documentary uncertainty from R45: the pinned source
constructors do allocate occurrence-owned native Value/Effect coordinates and
retain an occurrence/recipe/operand join into a negative Function demand whose
Result is that original Apply result endpoint. The actual typed Result
consumer preserves its contextual operation and references its parent. This
is a static constructor trace, without a solver run or emitted q artifact.

That trace does **not** derive the source declaration

```text
original q registration and independent operand source derivations
  ⊢ IntroOut_q : Desc(C_q, rho_A, ValueDescription, sigma_A, D_q)
```

including its authentic introduction class, component, original cursor and
exact ordered free-dependency telescope, or the independently formed effect
and complete-result origins. Generalize §3.3 still needs an independently
specified inference introduction; Code-Call §3.4 still consumes the original
symbolic result and result port. The native fields below do not instantiate
those missing premises. This is the first unsupported **output-formation**
judgment after granting independent operand certificates. Responsible owner:
ordinary Application source-formation authority, returned to Luna.

Applied to the parent, the new evidence identifies the concrete producer and
consumer seam at which an approved owner certificate would have to be retained.
It neither constructs that certificate nor reduces the parent's remaining
semantic premise to a solved native endpoint. This is no global nonexistence
claim and no source-qualified counterexample. The first unsupported-owner stop
condition ends this assignment; another conditional reconstruction is not a
next stage.

## 2. Select q by source ownership, not a matching spelling

The pinned fixture `candidate_local_self_recursion.rs:111` contains:

```yu
my outer = { my loop x = { my direct = loop x; my helper y = loop y; my first = helper x; my second = helper x; helper x }; loop }
```

Select the local named group owned by helper's actual `HirLocalId`, its
`terminal_body`, and the Apply at that body. Its callee resolves to loop's
local identity; its argument resolves to helper's parameter identity. Call
these indices `Q,F,Y`, final occurrences `q,f,y`, owner `O`, loop identity
`L`, and helper parameter `P`. These are names for constructor-produced
identities, not guessed numeric IDs or a new runtime receipt.

`local_source.rs:650–696` introduces the temporary self Local identity for a
parameterized initializer, then its Parameter identities, and records the
named group's terminal body. The enclosing loop self binding stays visible
while helper's body is formed; helper's parameter y shadows only its own
spelling. `:789–850` owns indices and occurrence/source registration, and
`:923` stores Apply's exact callee/argument indices. Importantly,
`LocalSource::order_occurrences` at `:101–132`, called by source formation at
`:524`, assigns the **published** occurrence identities in source-owner order.
The earlier provisional `set` occurrence is not an interchangeable q key.

Thus q is distinct from the direct `loop x`, all three `helper x` sites and
the final returned Name loop. The test's assertions and its `solve` call are
not used as proof that these paths execute, typecheck or emit certificates.
No parser or compiler was executed; concrete allocated ID values and an actual
emitted q certificate remain unobserved.

## 3. Forward native join and backward Result join

All line references in this section designate the pinned worktree bytes.
The contract marks `shadow_apply.rs`, `candidate_scheme.rs` and the fixture as
primary-owned overlays. Their observations are worktree-candidate evidence.
HEAD source bytes were not separately supplied or read; agreement/differences
with HEAD are UNKNOWN. Nothing here promotes overlay behavior.

### Forward from the original source

`ConstraintBatch::emit_candidate_source`, `candidate_source.rs:826–899`,
first checks pointer identity with `hir.local_source_for(O)`, validates the
receiver/owner and each occurrence, and retains source owners. It allocates
positions for each original expression by `candidate_component`.
`shadow_apply.rs:1481–1497` calls `occurrence_component` twice; the latter
(`lib.rs:1941`) constructs `ComponentId::Occurrence { occurrence, kind }`.
Write q's positions `Vq,Eq`; these are separate Value and Effect records.
Argument y uses `CandidateEndpoint::Parameter(parameters[P])`, rather than
silently using its unused expression Value position. The Local callee uses
`CandidateEndpoint::Component(Vf)`.

`candidate_source.rs:1316–1362` stores the following exact join, with `r` the
new recipe and `s` the new source input:

| Source input / recipe field | Constructor value |
| --- | --- |
| `owner`, `expression`, `callee`, `argument` | `O,Q,F,Y` |
| `callee_value`, `argument_value` | `Component(Vf)`, `Parameter(parameters[P])` |
| `callee_effect`, `argument_effect` | `Ef,Ey` from the exact operand positions |
| `result`, `application_effect` | `Vq,Eq` |
| `level`, `recipe` | actual source Visit level, `r` |
| `checking`, `cause` | `ConstraintOccurrenceId(q,0)`, its `CauseId::for_occurrence` |
| reciprocal recipe link | `candidate_recipes[r].source_input = Some(s)` |

`admit_candidate_fact`, `shadow_apply.rs:1762–1788`, checks the reciprocal
recipe, q occurrence, endpoint **variant and index**, both operand effects,
result and application effect. In graph-effects mode it then constructs:

```text
v_f+ = candidate_endpoint(Component(Vf), Positive)
v_y+ = candidate_endpoint(Parameter(parameters[P]), Positive)
r_q- = candidate_endpoint(Component(Vq), Negative)
i_q- = fresh invocation-effect row at the application row's level
j_q- = negative original application-effect endpoint Eq
demand_q = NegativeFunction(v_y+, e_y+, i_q-, r_q-)
NativeInterface = (v_f+, v_y+, e_f+, e_y+, r_q-, demand_q, i_q-, row_i, j_q-)
```

The retained input is installed before constraint admission, with an explicit
no-second-install check (`:1856`). Slot 0 admits `v_f+ <= demand_q`. Slots 1
and 2 admit the callee effect and fresh invocation effect into the application
effect (`:1905–1926`). Thus invocation `i_q`, application `j_q`, argument
effect and result Value are not interchangeable. These are constraint
generation facts; they prove neither complete invocation membership nor
the truth of the generated constraints.

`candidate_call::observe_inner`, `:482–575`, checks the original source Apply,
operand indices, q occurrence/cause, occurrence/scope ownership, Function
demand fields, port sorts/polarities and invocation row. It observes an already
retained NativeInterface; it does not independently create source typing.
The stronger source→recipe→port equality is supplied by the producer/admission
join above, not inferred merely from this observer's successful return.

### Backward from the typed Result demand

`InferenceSession::dispatch_live_item`, `lib.rs:12650–12688`, decomposes an
actual Function comparison into four typed children. For any such comparison
whose upper Function is the authenticated original demand_q, its Result child
has the structural equation

```text
TypedPairKey::Value(lower = positive actual producer's field 3,
                    upper = negative demand_q field 3 = r_q-).
```

This identifies the result endpoint **when that actual comparison occurs**;
it supplies no actual producer, comparison or successful execution at q.
Argument and ArgumentEffect reverse direction; ResultEffect and Result keep
direction. `candidate_step_function_dispatch`, `lib.rs:12807–12834`, sends
the actual typed child and field to `candidate_function_port_admit`.

That consumer (`candidate_context.rs:3377–3440`) takes the retained processing
parent, preserves the parent's post-check context for Result, inherits source
provenance and records `Dependency::FunctionPort { child,parent,field:Result,
operation:Preserve }`. For a scoped demand it verifies the exact parent upper
Function root; Result gets no effect transformer, while ResultEffect has its
distinct protection operation. Source seeding (`:3246–3310`) records the actual
`ConstraintOccurrenceId` in `Origin`; later derivation, canonical rewrite,
extrusion, FreshUse and replay require their actual retained parent/transport
edges. Endpoint equality or a source name cannot replace those edges.

The two directions therefore join at the original demand's exact Result port
under explicit source/recipe and retained relation provenance. They do not
join an arbitrary copied upper Function to q merely because its ports match.
No proof of q's full canonical/extrusion/transport path is claimed.

## 4. Instantiate the source laws and expose their first missing input

Generalize §§3.1,3.3 allows y's ordinary Parameter description at its original
scope, preceding invocation challenge. Its Name rule projects that existing
certificate. Loop's active recursive reference retains its registered
monomorphic component relation; lexical visibility alone supplies no complete
semantic world or certificate. Code-input §3.1 gives `Data-Name` from the
actual resolution **and binding interface**; `Code-Result` additionally needs
the original result node/port. Native Local/Parameter registration provides
identities, not all of those source-semantic premises.

Grant those independent operand certificates to isolate output formation.
Typed-core §6's Application row synthesizes the role
`Computation(E_q,A_q)` and `reify(call(n_f,n_y))`; its following paragraph
explicitly keeps symbolic endpoints constrained by complete invocation.
It does not specify a `Desc` introduction, its classification or `D_q`.
Code-Call §3.4 requires the actual Application origins, whole-argument
`ReifyOrigin`, original `Comp(E_q,A_q)` and result port `o_q`, emitted operand
checking origins, and the original provider suffix. It cannot manufacture
its own prerequisites from the completed Check record.

Generalize §3.3 requires Parameter, written hole or **another independently
specified inference introduction** for `Desc`; §4 allocates once per actual
introduction. q is Apply, not y's Parameter or an annotation hole. No such
Application introduction is instantiated by the pinned rules. Source-interface
§§2,4,6 inserts and uses authentic original declarations and forms the complete
Call frame from authentic `Q_q` and original origins. Its finite cyclic graph
construction does not remove those prerequisites. Source-role §4 expressly
establishes template finiteness without a finished inference-rule set.

In particular `ComponentId::Occurrence(q,Value)`, the native level, a lexical
`LocalSourceScope`, a source-reference graph and `FunctionPort::Preserve` do
not specify the ordered telescope
`D_q=(d1:S1,...,dn:Sn[d1,...,d(n-1)])` or its typed inclusion at `sigma_A`.
Native `Dependency::FunctionPort` is an operational relation edge, not that
declaration telescope. Effect ownership and original complete-result-port
formation remain independent missing source judgments; a Function field
named ResultEffect cannot supply the result declaration or complete Call law.

The selected checked-result interpretation is explicitly bounded to
immutable-Name/Unit Call with an unannotated result binding. Here the argument
is the parameter Name y, and q is helper's body. Even if y later receives a
Unit value, that does not change q's source constructor class. Its independently
formed challenge domain `D_c` is also not Generalize's free-dependency telescope
`D_q`. Neither the selected design nor its first-call introduction applies by
renaming their indices. No new rule is proposed here.

## 5. Discriminating attacks and retained obligations

| Attack | What the evidence establishes / exact limit |
| --- | --- |
| Wrong occurrence, even the other `loop x` | Producer/admission checks q and reciprocal recipe/operand fields. A later copied relation additionally needs retained transport/use identity. No actual mutation test was run. |
| Missing/reordered dependency | Port equalities contain no ordered Desc telescope. Substituting `D_q := lexical context`, `[]`, or free variables of a solved result is unsupported. Even `d2:S(d1)` cannot be moved before d1 without a new typing derivation. This is a logical falsifier, not an actual-q counterexample. |
| Result/effect conflation | Value Result, invocation i, application j and argument effect have separate constructors and typed Function fields. The two effect inequalities do not identify i with j or body effect. |
| Invented provider/consumer fields | The lower producer's Result port is not the actual complete return provider/current world. NativeInterface has no whole Call provider/admission/future certificate. A changed W provider needs its own output-dependent guard and future evidence. |
| Scope/live-route mismatch | q's Local callee is an active outer root: `candidate_source.rs:1090–1104,1244–1249` emits `Action::Link`, not `Action::Local`. `authenticate_scoped_apply` (`candidate_call.rs:691–739`) requires a retained authentic `LocalFreshRoute` for Local callees. A link does not itself supply it. No scoped q admission success, runtime failure or general source rejection is inferred. |
| Formal introduction substitution | `formal_names` is populated only for Parameter Names (`candidate_source.rs:922–934`). q's Local loop callee therefore has `formal_name=None`, so the omitted-formal `DirectionalIntroduction` and receiver attachment are absent. Its field is ResultEffect in any case, not the missing Desc output owner. |
| Solver success/new primitive | The fixture's assertions are not proof inputs. Adding an Application primitive, choosing a new interpretation or asserting a completed source certificate would cross the contract. |

The whole Call still needs independent original callee/carrier and actual
receiver/receipt/entry/body/native-return/designated-consumer/complete-return
ports. Callee pending retains its raw response/current-world continuation and
unexecuted receiver suffix; receiver pending retains only remaining tails and
does not repeat receipt. Value entry keeps its designated Force/rebind;
retained entry keeps its different entry. Whole-Call and local/nested W/Z,
licenses, changed-provider admission and final guards remain independent.
The returned provider's latent/future interface, current C2, every independent
future and foreign continuation are unproved. These are source-interface
§§4,7/Code-Call suffix obligations, not fields inferred from native endpoints.

Two incoming helper-use frames and an alias still require authentic owner
records, exact retain/fix closure, scope/dependency maps and commuting native
transport. A shared alias does not allocate another frame; distinct frames
do not merge OneShot/Shared with ViewLogic/EventProof. Residual, provider and
witness lineages remain separate. No q-specific frame maps, F1, FK1, engine
MODEL, source/native theorem, principality or production gate is discharged.
Simple-sub generation, accumulation, propagation, levels, extrusion,
qualifying intrusion and generalization retain their original requirements.

## 6. Reuse, mutual TODO and exact next boundary

R45's reviewed bounded obstruction and dependency/provider falsifiers are
reused only under their pinned premises. This packet changes method/input by
inspecting real producer/consumer code and reading the original laws directly.
It rejects symbolic endpoint names, whole-context dependency assignment,
solver success, assumed transitions and erased proof signatures as source
introduction evidence. Historical proof review does not review this artifact.

`R46-PROOF-OWNER-1` — Luna / ordinary Application source authority: obtain the
authentic q output/effect/result-port introduction, original component/cursor,
class/sort, exact ordered free dependencies and typed inclusions **before**
output-indexed Call headers. Inputs: the actual HIR resolution/registration
and independent operand certificates; output: one independently justified
source derivation, or an owner-specific refusal/counterexample. Falsifier:
wrong occurrence, an unavailable/reordered dependency, later event/provider
used before declaration, or reconstruction from completed Q/solver success.
If this requires new semantics or another governing dependency, Luna must
return it through the existing authority/review/approval path before writing.

`R46-PROOF-NATIVE-2` — later separately authorized source/native implementation
owner, **provisional TODO only**: once OWNER-1 exists, retain its authentic
certificate at `emit_candidate_source`/`ApplySourceInput` and preserve its
ordered dependency/copy provenance through admission, native demand,
Result/Preserve, Context and Dispatch. Inspect active recursive Link versus
FreshUse ownership explicitly. Exact falsifier: wrong-q or sibling-use receipt,
dropped/reordered dependency, effect/result swap, unbacked provider/consumer,
alias freshening, or omitted pending/return/future arm accepted as certified.
No code edit or new behavior is authorized by this TODO.

Luna's independent source map can compare these exact seams. This author cannot
certify the combined result or appoint reviewers. Next in-envelope stage:
none at the unsupported-owner stop; fresh review, any changed input and further
leases belong to Luna. `NO_SAFE_CODE_SLICE` applies to this dependent owner
certificate seam; source registration and typed consumer were both inspected.

## 7. Frozen dependencies, checks, resources and writer receipt

Every direct dependency below matched the contract pin on reading. Historical
transitive hashes quoted inside them are not imported as new authority.
Authors: R45 core `/root/r45_contextual_core`; R45 independent audit
`/root/r45_independent_derivation`; closeout/design selections Luna `/root`;
Generalize researcher; typed-core/role notes primary with architect input;
Code-Call researcher repair with primary review disposition; individual
source-interface and Rust authors UNKNOWN. The contract identifies the three
primary-owned overlays; that ownership does not establish original authorship.

| Direct dependency | SHA-256 |
| --- | --- |
| `notes/progress/2026-10-19-r45-closeout.md` | `6caf736e9d76ebc5c44080d0ad77a92b52b113703aa772c99315cb9a99dc8da5` |
| `notes/theory/2026-10-19-r45-contextual-output-core.md` | `d2982e9bd316f764c9e9709e5843062d5b02b7c5f6f5eea9231fe6a14dd10be0` |
| `notes/theory/2026-10-19-r45-application-derivation.md` | `05530063f72b8df7f989d9c9483b05e56dc2591af9232cee1682900e524ce2c4` |
| `notes/design/2026-10-16-source-application-checked-result.md` | `c9207625887d78aaccef988324e8505f6dd08fdfe076e0f564f8b7dca3c54076` |
| `notes/theory/2026-10-16-first-call-checked-result-construction.md` | `89fb62b1fe9e10d6972a79f17399d4a0332cf57817bb06a07f5e054ecb4b9dfa` |
| `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` | `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/theory/2026-10-07-call-input-construction-proof.md` | `f7c1b1eb23acb33ab98487097ab67617e1af84964b012874b1c951a8805dd9f6` |
| `notes/theory/2026-10-08-call-source-interface-construction.md` | `278034197a90eab6e62a073545c09dd14415a0353f58aa3b3cc122a6af945d98` |
| `notes/design/2026-10-02-source-computation-role-elaboration.md` | `9a230eb023698666f4c3e518a527009d6915e65f658b230e6da6a29914ca3abb` |
| `crates/yu-hir/src/module/local_source.rs` | `ede8b845e1ad19bb1481d7e6337cefa1f117197512975f0f306dc6edb79672e5` |
| `crates/yu-solver/src/candidate_source.rs` | `66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c` |
| `crates/yu-solver/src/candidate_call.rs` | `e038ad0dfc4b12bd0d513d6cd6b34cee6b2b062d8b33368bc1c0dcdef980d479` |
| `crates/yu-solver/src/shadow_apply.rs` | `d5e6b179fd4f6fbca579b0fa4d479d8bd11b520d774acbf27f414451c4691137` |
| `crates/yu-solver/src/candidate_context.rs` | `42f89dcf5fa6d7095db1e220c89308a2a35f4e74b05c3e8821d4fb2e3e32b0ca` |
| `crates/yu-solver/src/lib.rs` | `2300400e87d0a487225f207d414ac71fa4f21c6f80279fea4f793e43c7809aee` |
| `crates/yu-solver/src/candidate_scheme.rs` | `8c370e47d5e8692a618fedf41be07d7ae3ac961f9070bfed6730e2b8e2f1137e` |
| `crates/yu-solver/tests/candidate_local_self_recursion.rs` | `47ced76fe8f0f136c42802b2376ca09f7cadec0fc8e5b1b3d4c6acc7bc613e55` |

Checks: direct text/premise/field inspection and SHA-256 comparison only.
No tests, builds, Cargo, compiler/runtime probes, Git, production edits,
external contact, nested CLI or delegation. No independent review performed.
The initial compact-state read returned ENOENT; Luna then supplied its live
launch record and rev2. No worker state was inferred from the missing file.

Budget: 900 seconds cap; conservatively reserve/charge that allocation, without
renewal. First clock observation: 2026-10-18 15:46:17 UTC; final observation
is recorded in the handoff. Pre-observation launch interval, active CPU and
RSS remain UNKNOWN. No descendant allocation. All new paths are exactly this
artifact and `tasks/agent-loop/inbox/20261019-r46-proof.md`; scratch paths none.
The artifact freezes before its handoff digest is computed. After the single
handoff freezes: **WRITES_STOPPED; NO_DESCENDANTS**. This assignment is terminal,
with review and intake pending; no continuing waiting computation is claimed.
