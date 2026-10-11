# Negative concrete formal: source-owned local call proof boundary

Date: 2026-10-11
Status: unreviewed research derivation; frozen at handoff
Claim class: source-qualified singleton lemma and proposed insertion/consumption invariant; no global hygiene theorem
Primary baseline: `cfab95a2cb64be8f8a58f8e69abee22390042135`
Reference Simple-sub: `9bae772624c23b52a93c1b226157e16898b4d9db`
Oracle: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Lease: this note only; leaf, no delegation or Git mutation

## 1. Frozen objective, statement, scopes and exclusions

Authority is top-level inference principles §§1–5; annotation effect hygiene
integration §§1–5; concrete effect annotation implementation, “Annotation
checking and publication owner” and “Conflict ownership and replay”; contextual
attachment admission §§3–6. Full abnormal-state restoration is superseded by
the top-level principles. Successful suspension must retain accepted facts,
continuation and validity. The admission design does not authorize enabling
negative concrete formals in this packet.

Fix exactly the Oracle source and its complete recorded dump in
[negative-formal-effect-source-audit](../progress/2026-10-11-negative-formal-effect-source-audit.md):

```yulang
pub act tick:
    pub ping: () -> ()
my f(cb:(() -> [tick] ())) = cb ()
```

Let `f` be the sole function owner, `cb` its formal binder, `a` the sole
concrete BracketRow occurrence at the callback Function's result Effect port,
`E` the declaration-resolved nullary `tick`, and `k` the sole application `cb ()`.
The formal starts Negative; its Function result descent preserves Negative.
`a`, `E`, `cb`, `f` and `k` remain separate identities. The callback provider is
the one actually selected for this same application; this source contains no
callback provider body, so no concrete provider witness is silently chosen.

**Required singleton conclusion.** Derive the actual source-owned local
subtraction at `a` along `k`, including the retained concrete check and exact
call/output route, or isolate its missing construction/consumption premise.
An attachment-qualified contribution from that occurrence may be removed;
an independent contribution with the same resolved `E` must survive. The
displayed outer `f` invocation effect is distinguished from declaration
evaluation effect, callback effect, raw row contents and runtime elimination.

**Parent quantifiers retained, not claimed discharged.** For every actually
formed composed-negative concrete formal occurrence in the selected source
envelope, every applicable current/future lower, each correlated symbolic
refinement and every actual fresh use/extrusion/qualifying parent-copy intrusion,
the same original attachment, scope, lineage and complete call provider must
govern insertion and consumption. Generic copies must preserve sharing within
a use and distinct local attachment instances between uses. This singleton
has no symbolic tail, independent second contribution or fresh invocation;
those universal cases remain required obligations, not inferred tests.

Hypotheses: the primary's revisions and recorded Oracle execution identity;
the inspected source bytes; declaration resolution to nullary `E`; successful
fallible source construction where a constructor claim explicitly assumes it.
No supplied attachment transition, independently chosen provider witnesses,
row-equality subtraction law, complete replay/termination, source-to-binary
proof, or runtime discharge premise is assumed.

Excluded: the retracted callback result, `my ans: [E] int`, parameterized
effect variance, Catch/handler selection, generic mixed recursive decision,
production enabling, eager solving, artificial source restrictions, global
family subtraction, full abnormal rollback and promotion of soundness or
principality. The original A/B parent gate stays OPEN.

## 2. What native Simple-sub proves, and where the extension begins

The original [Parreaux paper](https://infoscience.epfl.ch/server/api/core/bitstreams/afe084e0-0050-4542-99c7-c499d2fe1620/content),
§5.3, Theorems 1–2, states soundness for successful inference from empty
context/bounds and completeness against each declaratively typable term,
using positive coalescing and scheme subsumption. Lemma 2 requires consistent
initial bounds and successful constraining; it preserves consistency and
establishes the constrained coalesced subtype relation. Its proof sketch
explicitly needs a stronger cache-sensitive invariant during propagation:
insertion can temporarily break consistency before opposite-bound calls
restore it. These are ordinary-language results, not effect-extension results.
This note uses their generation/propagation structure, not a claimed new proof
of those theorems or an import of their conclusion for Yulang's effect rows.
The paper's ordinary binders/substitutions cannot be replaced by independently
chosen provider witnesses. Its §5 sketches proofs; this packet does not
independently fill the omitted metatheory.

The original reference `shared/src/main/scala/simplesub/Typer.scala` has
`Var`, `Lam`, `App` and `Let` generation in `typeTerm`; `App` generates
`f_ty <: Function(a_ty,res)`. Its `constrain` Function case reverses the
argument and preserves the result. Its variable cases insert a bound and
propagate against the opposite bounds, using extrusion when levels differ.
`typeLetRhs` infers at `lvl+1` and retains `PolymorphicType(lvl,res)`;
`freshenAbove` uses one variable map and preserves variables below the boundary.
There is no effect row, annotation attachment, POP or subtraction constructor
in that reference. Consequently no native-reference theorem silently supplies
the missing effect law. Qualifying parent/copy SCC intrusion is a Yulang
extension with its own owner, rather than a rule present in this reference.

The relevant native generation spine in Yulang's four-port extension is
especially small. Write `P` for cb's registered Value row, `U` for the unit
argument Value, `R` for the call result Value, `J` for the invocation Effect,
`B` for the application Effect, and `O` for f's latent result Effect. The
actual prospective source schedule and normal owners generate:

```text
A+ <: P                         paired annotation exposed edge
P <: A-                         paired annotation checking edge
P <: Fun-(U, argument_effect, J, R)   same source application k
callee_evaluation_effect <: B
J <: B
B <: O                          lambda body result
entry_effect <: O                inferred bare-parameter entry
```

`A+`/`A-` are names for the paired interfaces, not invented attachment witnesses.
The complete actual Y3 interface is currently absent for this source (§4).
The structural edges above are derived from the existing owners conditional
on their admitted action schedule, not asserted to execute past preflight.

Sources: `candidate_formal_annotation` (`candidate_effect.rs:1073–1111`)
emits both annotated Value edges and retains `formal_domains[parameter]`;
`admit_candidate_fact` (`shadow_apply.rs:1301–1447`) builds this exact call
demand, allocates `J` at the application Effect's level, and emits the two
application Effect edges; `admit_lambda_fact` (`lib.rs:11233–11351`) uses the
retained formal domain and joins both entry and body effects into `O`.
The inferred entry certificate authorizes no subtraction operation.

At one fixed level, `A+ <: P` and `P <: demand_k` have exactly the ordinary
lower/upper replay shape. Native Function propagation then transports `A+`'s
result Effect to `J`, followed by `J <: B <: O`. If levels force a different
physical bound orientation, the Simple-sub level and extrusion rules decide
that orientation; annotation permission cannot decide it. This proves the
local transport skeleton, not a rule removing its annotation contribution.
Copying its supports into the covariant Allowance path cannot change this
fact: successful allowance comparison means admitted comparison, not
subtraction from `O`.

## 3. Source-derived Oracle singleton lemma

**Lemma, within the inspected Oracle constructor path.** If this formal is
successfully lowered and its sole local application uses the resolved `cb`
binder, the concrete set constructor allocates one fresh `i`, and the call
predicate reaching f's defined-lambda output uses that same `i` and set `{E}`.
This is source construction evidence for a prospective local cancellation,
not source-wide hygiene, complete replay or runtime discharge.

Derivation:

1. `connect_parameter_computation_detailed` sets
   `parameter_function_boundary=true` (`annotation/constraints.rs:251–260`).
   `lower_value_bounds`' Function case reverses argument bounds and preserves
   result bounds (`363–390`). `lower_ret_effect_bounds` (`424–470`) creates
   the result views through `effect_row_stack` (`657–690`). Resolved concrete
   `E` forms the singleton set; annotation variables are not concrete atoms.
   `fresh_subtract_id` is called here, not reconstructed from row equality.
2. With inner row `q`, the actual result views are
   `Stack+(q,PUSH_i({E}))` and `Stack-(q,FILTER({E}))`. The returned predicate
   is `POP_i` with filter `{E}` (`predicate_weights:921–924`), and the positive
   returned Value also retains it in `NonSubtract` (`363–389,848–851`).
   `register_stack_facts` (`590–599`) records the declared fact on `q`.
   `q` is not claimed to be a unique occurrence identity: closed-row caching
   can share a row (`602–620`); the separate fresh `i` is the cancellation key.
3. `connect_value_detailed` (`124–137`) emits both paired constraints on
   cb's actual Value. Lambda annotation lowering retains the returned weights
   as `call_predicate` (`lambda.rs:1278–1285,1581–1596`). For a Function
   annotation, its immediate parameter output predicate is empty
   (`1571–1578`). Thus merely declaring the formal does not trigger the
   call-local output POP.
4. `mark_lambda_param_call_predicate` (`lambda.rs:919–936`) stores the exact
   returned weights on this binder's local record. `make_source_app` enters
   `make_app_with_origins` (`tail.rs:535–565,629–705`). That call obtains
   `local_callee_call_projection` from cb's record and adds its weights to
   f's current latent frame (`719–725`). The annotation marks the return
   effect Annotated (`lambda.rs:1340`), so
   `unannotated_local_callee_return_effect` returns its bare `J` interface
   (`tail.rs:740–757`); it does not create a second empty-family subtraction ID
   for this call. The local erased-upper check is an additional actual
   constraint (`tail.rs:598–611`), not evidence of a different provider.
5. `lambda_predicate_subtracts` merges the same frame's latent weights
   (`tail.rs:1058–1072`); the defined skeleton wraps both current output Effect
   and Value with them (`lambda.rs:1232–1237`). `step_subtype` consumes
   Stack/NonSubtract wrappers by prefixing the real left operations
   (`propagate.rs:11–38`); Function result children preserve context
   (`210–263`). Thus the normal result-Effect path has `PUSH_i` upstream and
   this same call's `POP_i` downstream, rather than an unrelated nominal-set
   deletion.

For a replayed path reaching that output, `compose_for_replay`
(`constraints/mod.rs:3598–3607`) composes the left operations in path order.
The actual per-ID formula (`directed_weight.rs:399–405`) gives

```text
PUSH_i: (m,n)=(0,1); POP_i: (p,q)=(1,0)
(0,1) ; (1,0) = (0,0).
```

This is a derived cancellation of one matched attachment operation. Its
per-ID lookup (`145–170`) never changes another `j != i` entry. Hence any
already established independent `PUSH_j({E})` on that path is unaffected by
this particular algebraic step even when its family equals `E`. This proves
the local algebraic preservation once those entries and path exist; it does
not prove that all actual independent source contributions use such entries,
that every relevant path is replayed, or that an untagged concrete `E` is
globally removed. No source sibling witness was executed in this lane.

Filters are checks with a different responsibility. Negative Stack normalization
checks before consuming the wrapper (`propagate.rs:38–56`). At bound insertion,
`check_and_erase_upper_left_filter` checks active stacks and registers the filter
on the actual source row; `check_and_erase_lower_left_filter` checks the weighted
incoming lower before erasing its left filter (`bounds.rs:3174–3210`). A new
registration scans current lowers (`3213–3255`); a new lower checks existing
registrations (`3285–3301`). Recursive variable encounters install another
retained check (`3303–3360`). Filters on a Value Function do not traverse its
ports. Keeping a filter on a stored Value bound and replaying it indiscriminately
into latent ports would repeat the repaired historical orientation defect.

The exact observed Oracle scheme is
`(() -> [tick] ()) -> ()`: `[tick]` remains on cb's output, while f's displayed
outer invocation result has no row. This independently observed singleton
outcome agrees with the matched local cancellation path. It does not prove
the printed scheme follows uniquely from this path, eliminate actual runtime
requests, or establish any scheme for an independently selected callback body.
The prior one-run audit remains the execution evidence; no new Oracle run is
claimed.

## 4. Current Yulang3 obstruction and exact consumer coverage

This is an implementation-correspondence obstruction, not a refutation of the
selected source policy. The equivalent Y3 source uses `act`, `our`, and the
parser-required space before the formal. No Y3 execution occurred here.

HIR `local_source.rs:289–300` retains cb's annotation;
`source_annotation.rs:399–480,505–558` retains its Function tree, exact row
position, resolved nullary operand and separate variable list. These provide
the original owner/position facts without reconstructing them from row IDs.

`CandidateInference::solve` (`shadow_apply.rs:92`) invokes preflight first.
`candidate_source.rs:98,117–121` starts this formal with `positive=false`,
preserves that sign into its result, then requires a negative row to have no
concrete members and exactly one variable. This row has one concrete member
and zero variables, so the source returns Unsupported before its annotation
action executes. Independently, `candidate_formal_pair`
(`candidate_effect.rs:1034–1052`) rejects that result; the effect-port owner
(`1054–1070`) has no negative concrete case, and general signature construction
rejects it again (`1507–1509`). Deleting only preflight cannot construct it.

The reached ordinary atom consumer `candidate_check_effect_operand`
(`candidate_effect.rs:888–958`) expands Support into AnnotationMembers/tail,
accepts an allowed member at Allowance, forwards an unmatched operand to its
tail, or emits a mismatch. It has no attachment-qualified subtraction result.
Existing `candidate_context_execute_relation` (`candidate_context.rs:2751`)
calls `candidate_zero_word_filters` (`2615`): source payloads must have empty
left/right words and match an actual closed view, or the helper returns Err.
Its filter discharge retains an actual Allowance registration/replay and the
post-check context (`2770–2860`); this is a live check consumer, not a dormant
negative subtraction implementation. `source_weight` (`2174–2195`) stores
empty words; `materialize_unit_push` (`2200–2222`) is explicitly detached and
emits no live relation, bound or residual recipe. These current mechanisms
cannot instantiate the Oracle singleton lemma for this negative source.

Complete Call remains separate. `candidate_source.rs:194–198,240–243,399–409`
retains cb's registration and the exact application inputs; native admission
records one demand, invocation row and application Effect against that same
source input (`shadow_apply.rs:1301–1400`).
`CandidateSourceCall` (`candidate_call.rs:135–216,390–442`) borrows that source
application and checks its formal binder linkage. It is explicitly pending
construction, not a source typing/provider certificate. The actual source has
no provider body. `shadow_apply.rs:12–48` keeps ApplicationTypingRule,
CompleteInvocationImage, WholeArgumentProviderCompatibility and the original
Gen-Call-0 premise unresolved. An independently chosen allowed provider for
the filter and a different provider for the output cannot discharge them.

## 5. Minimal missing law at the coupled owners

The minimal nonvacuous missing law is **agreement between the actual paired
formal constructor and this binder's actual call/output consumer**. This is
a proposed construction invariant, not a transition already proved emitted.
For the singleton it must establish all of the following together:

- At `candidate_formal_effect_port` under the actual Negative source variance,
  retain one attachment set for `(f,cb,a,local instance)`, member ordinal zero,
  resolved `E` and its original scope. Derive the matching positive/checking
  operands from that occurrence. Creating Support or recording an allowance
  alone supplies no removal authority or emitted event.
- On application `k`, connect that same attachment through cb's lexical formal
  use and this call's generated result-Effect demand to the owning function
  output. Reuse the actual call/provider derivation when one is available;
  do not infer it from a successful negative Function comparison. The Value
  result route must retain latent obligations when the result can later be used.
- When the relevant typed constraint is inserted or replayed, perform the
  authentic retained concrete check before consuming its filter, preserve its
  residual operation/lineage and actual derivation origins, and check all
  current/future lowers at the true receiver. Level-selected physical bound
  orientation stays native. Merely storing the tagged bound is insufficient:
  it must feed the actual opposite replay and output consumer.
- Cancellation may affect only the attachment-qualified operand on that
  path. Independently formed same-family instances and exact residual recipes
  survive; equality of rows/families does not establish attachment eligibility.

For the unchanged parent theorem, symbolic tails must stay connected and all
source-generated generic copies must map the complete relation/filter/residual
graph once per use. Extrusion and qualifying SCC intrusion may identify row
coordinates while preserving distinct occurrence/attachment/recipe identities.
The existing copy/capture machinery supplies owners to inspect, not an automatic
proof for a negative transition that is never constructed. Successful private
suspension keeps these accepted facts and its continuation; ordinary errors may
terminate the affected private attempt without publishing an inconsistent result.
No universal rollback restoration premise is introduced.

This law deliberately leaves representation to the approved carrier/owners.
It is smaller than another reconstructed effect relation: HIR already knows
the occurrence, resolved member, scope and binder; the source action knows the
actual call demand; the bound/consumer owns activation and residual feedback.
It also cannot be reduced to adding a fresh ID alone: an ID with no call/output
activation is the same missing premise under another name.

## 6. Proof-obligation economy and disposition

The prior conditional hygiene proof and repaired transition checker supplied
different methods but left actual negative construction and consumption open.
This attempt therefore stops at the owning seam rather than proposing another
checker with assumed attachments. The missing subtraction/activation law is
A/B: it controls sound effect hygiene and the selected ordinary annotation
behavior. Recovering its source owner from equal rows, supports or successful
queries would add D reconstruction debt. HIR and source formation can retain
their known facts; provider/output completeness must be proved at its actual
source/operational owner. Neither is optional C by reclassification.

Result: a source-derived Oracle singleton constructor/call lemma plus the native
transport spine and a decisive current-Y3 construction obstruction. Not an
established global theorem, runtime elimination proof, source counterexample,
complete replay theorem or principality proof. The negative-formal A/B parent
gate and its dependent admission/implementation gates remain OPEN.

One next action: primary assign/reconcile this exact coupled formal/call/output
law against the retained Simple-sub contextual owner, preserving the original
gate and its admission boundary; obtain independent review before using the
singleton lemma as implementation evidence. A generic model with supplied
attachment/filter transitions cannot answer the remaining source question.

## 7. Checks, resources and runtime

Only the leased note changed. Checks: bounded `cat`/`sed`/`rg` source reads,
the original paper's §5.3 lookup, dependency SHA-256 snapshot/recheck and local
document whitespace/link checks. No executable model, new Oracle run, Y3 run,
Cargo/build/test, timing sample, heavy process, subdelegation, configuration,
compiler, test or shared-record write. The existing Oracle dump is inherited
evidence, not a run by this worker. At most three independent lightweight reads
were batched; there was no CPU-intensive process. Aggregate CPU/RAM/wall time
was not instrumented; the packet had one Sol/high leaf and a 45-minute ceiling.

Requested settings: primary packet `gpt-6.1-sol` / `high`; project prover role
has no model/effort pins and configured defaults agree. Observed effective
runtime model/effort: unknown; no metadata is available in this leaf. No Astra
request, override or reload claim. No further delegation occurred. Fresh
independent review and status adjudication remain primary-owned.

Workflow exception: the initial orientation ran read-only `git rev-parse HEAD`
and `git status --short` despite the packet's no-Git instruction. It reported
the supplied baseline and an empty status at that instant. These are not
counted as compliant checks; no Git mutation occurred and no subsequent Git
command ran. Broad early tool captures were truncated; the decisive owner
excerpts were subsequently read directly. A search for an absent `spec/`
directory returned exit 2; no specification evidence is inferred from it.
The paper's old redirect failed with HTTP 429; the canonical EPFL PDF endpoint
then provided the §5.3 text. This is a bounded paper lookup, not a new full-paper
audit or an independently pinned PDF byte snapshot.

## 8. Dependency snapshot and commit packet

Hashes identify inspected bytes, not Git blob IDs. Oracle hashes match the
earlier source audit's corresponding entries. Comparison of current repository
bytes to the pinned baseline is the primary's integration duty. No dependency
was edited by this leaf. Repeat hash check at freeze found no changes relative
to this snapshot.

| Dependency | SHA-256 |
| --- | --- |
| `rules/agent-orchestration.md` | `3b1e9c5a083ae4257d3d8ad4bacadf55adf07997d0b02c10bcbec4ccda3258be` |
| `rules/research-lab.md` | `3f70daf755fd6af59959fa48a35aa2d5153639621cc18edc58934246f2aabb69` |
| `rules/design-authority.md` | `e4055100f6e75b9c8a6294ec6c68643d8677d7b35b45e430450f7e2c2ad97eb1` |
| `rules/compiler-engineering.md` | `4567cc0f6997c116114cba3322563cb0ddbe5c73ab3403e5272f0e638cb73ed9` |
| `rules/git-concurrency.md` | `2561a7168ba8b2d655cc928c8adac565755ec7e3b6b4175e8ac87be4bcdaa5e6` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` | `503b1aab4205d063d1ab9f97358e8b128f82ee2ff818ad7150d9c7dac284254a` |
| `notes/design/2026-10-10-concrete-effect-annotation-implementation.md` | `3a3186723cd93edd2f767a7e4a481cb6dbed701fc749502e640071f65a4d89ae` |
| `notes/design/2026-10-10-contextual-attachment-admission-design.md` | `717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc` |
| `notes/progress/2026-10-11-negative-formal-effect-source-audit.md` | `8b0c9c7bfa131b9119d82a5a3c7ef6f8eb9636093176a2bd5818b6fe9aa7a538` |
| `notes/progress/2026-10-10-formal-filter-transition-contract.md` | `b18f617be8fad153228bd13578576f957b934d7202a97ba45c3f6618e520a4b2` |
| `notes/progress/2026-10-10-contravariant-effect-conditional-proof.md` | `faeaffecbd2aa6a50e4d82bc8924870148f784448d29aa893e9f5ddb89cb2ef9` |
| `crates/yu-hir/src/module/local_source.rs` | `906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed` |
| `crates/yu-hir/src/module/source_annotation.rs` | `a348a47530e57c2b3475a4c0d9f020e24ba04ea58a06292847892640567e61cb` |
| `crates/yu-solver/src/candidate_source.rs` | `13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49` |
| `crates/yu-solver/src/candidate_effect.rs` | `ae98dd92e2c8eb7e538c4450f250826bf83872f3bb62f1de1b014406313634df` |
| `crates/yu-solver/src/candidate_context.rs` | `4385c96423cd5c6cd1686066b2e6f0581c5cebf47d68bc86476c79e2a2f88987` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0` |
| `crates/yu-solver/src/candidate_call.rs` | `79ca6f226f91109ea43bf7f794211d5b8f1371c2afbd8bbc94d3c823e7c3ba35` |
| `crates/yu-solver/src/shadow_apply.rs` | `230ed70cc8575016967cdf16c6c814544b25e45b0fc687d6c89f0d38e8fb5cd6` |
| `crates/yu-solver/src/lib.rs` | `c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94` |
| `/home/momota1029/rust/simple-sub-reference/shared/src/main/scala/simplesub/Typer.scala` | `f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9` |
| `/tmp/yulang2-oracle-read/crates/infer/src/annotation/constraints.rs` | `3c0482d4549a2bfc7e651a6b2cc15fa4e70488fe8f68fcbfca34c1bfb72920db` |
| `/tmp/yulang2-oracle-read/crates/infer/src/lowering/expr/lambda.rs` | `2e0206bdcfdfbe98d13c12eec7ba8f7964383bc08c92947352ad370754024db9` |
| `/tmp/yulang2-oracle-read/crates/infer/src/lowering/expr/tail.rs` | `ac406b309fbb0ba558a18e37aba63a8e7ffeabbc377a111566b1f97d786f93b8` |
| `/tmp/yulang2-oracle-read/crates/infer/src/constraints/machine/propagate.rs` | `8695fa5d7dfac805cd7d66e9e0760c8c298002b952b0cd8a43dcd1f8eb6f7086` |
| `/tmp/yulang2-oracle-read/crates/infer/src/constraints/machine/bounds.rs` | `c300c8c0c495da46822e1e1df38b833a6bffe5f3707642ae2cd26910b0608df7` |
| `/tmp/yulang2-oracle-read/crates/infer/src/constraints/mod.rs` | `ad3cf5fd60462cb1a08ef1a5d6fc57c4fd640148597bc3b331d09729616d8392` |
| `/tmp/yulang2-oracle-read/crates/infer/src/constraints/directed_weight.rs` | `de71ae7ed5a5aed22f3e5d35ca0ebcd52872ff965fcc22523a662cffdd6f28db` |

Commit packet:

- Exact leased/change path: `notes/theory/2026-10-11-negative-formal-effect-source-proof.md`; writes stopped at handoff.
- Baseline: `cfab95a2cb64be8f8a58f8e69abee22390042135`; reference Simple-sub `9bae772624c23b52a93c1b226157e16898b4d9db`; Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Changed dependency hashes: none between final snapshots; equality to baseline remains primary-owned. No Git mutation.
- Claim/review: unreviewed conditional source-constructor/call lemma and static Y3 obstruction, plus proposed coupled-owner invariant. No independent certification or parent-gate closure.
- Checks already run: exact source reads, bounded paper lookup, SHA-256 stability and leased-document whitespace/local links; no tests/builds/execution probes.
- Proposed checkpoint: `research: derive negative formal effect call constructor lemma`.
- Shared-record deltas left for primary/curator: link the singleton lemma and exact missing coupled formal/call/output source law; retain negative-formal A/B, admission/implementation, complete Call, full hygiene, soundness/principality and F5 gates OPEN. No shared task/index/theory-status record edited.
