# Initialization outward order in the current error-only playground runtime

Date: 2026-10-16
Status: constructive actual-code theorem, independently reviewed CLEAN and
accepted by primary for outward-prefix cardinality/no-observed-pair-inversion.
Baseline supplied by primary: `6b6cafea1`; implementation `739e95630`.
Scope: public playground machine executions and their actual outward-event
prefixes. This is not full source scheduling, admission or materialization
adequacy, and selects no new semantics or implementation.
Exclusive write lease: this note only.

## 1. Frozen authority, statement and exclusions

The exact [approved observation answer](../../questions/2026-10-16-initialization-effect-order-observation/approved-answer.md)
is q1/a1 revision 1, validated and committed by the primary at `6b6cafea1`.
Its clauses 1–4 count effects actually escaping an initializer **after internal
handling**, including escaping handler-arm/resumed effects and effects reaching
an automatic global consumer. They do not count fully internal requests or
infer occurrence from permission/static effect support. The predecessor and
now-transcribed [governing design](../design/2026-10-16-initialization-order-global-effects.md)
retain relative ordering, global handling or error, and the independent timing,
source-construction and implementation gates. Approval selects no detector,
blanket early-entry rule, cancellation or cache-publication alternative.

Fix any `RuntimeProgram` returned by the actual `from_hir`, any successful
public `start(selected, roots)`, and any sequence of public `step`/`run` calls
on that one fresh machine. Include arbitrary finite budget pauses and all
actual internal Call, Force, Catch and raw Resume paths. The CLI supplies the
canonical mixed source plan; the cardinality result below even holds for any
plan accepted by `start`, without claiming such an arbitrary plan is the source
schedule. No external response or host mutation is an admitted transition.

**Actual-code theorem.** For every finite execution prefix, the trace of
distinct requests crossing their current top-level demand boundary has length
at most one. The initialization-only trace is a restriction of this trace and
also has length at most one. A crossing is attributed to the authentic active
demand defined in §2. The same event is counted once even if forwarding takes
several steps, a budget pauses forwarding, or a stopped outcome is polled
repeatedly. On a completed run this trace is empty. No escaping request
publishes its suspended initializer's result or performs its pending Name
consumption.

**Order consequence and exact limit.** There is no pair of actually observed
outward events from different initializer labels in reversed source order.
This proves that pairwise safety fact on current observed prefixes. It does
not establish that a singleton later-initializer event is a prefix of a full
successful source-order computation. Nor does it establish that all earlier
initializers could never subsequently escape. The machine stops before there
can be a second such event. No unobserved/counterfactual earlier event is
deleted or assigned empty support by this argument. Full source trace
refinement, entry timing, admission, automatic global handling and whole
materialization remain OPEN. The approved boundary alone supplies no missing
proof of those stronger conclusions.

## 2. Authentic active-demand labels

Use existing constructor identities, without a new registry or runtime field:

| Demand delimiter | Authentic label | Owning construction |
| --- | --- | --- |
| `GlobalRead { cell, ... }` | Definition at `program.definitions[cell].id` | Empty ModuleDef Name uses the original `globals` cell and original body, `machine.rs:449–477`. |
| `Root { cell, ... }` | Same original definition identity | `begin_root:1458–1499` selects an authenticated scheduled definition or the selected-definition fallback. |
| `ExpressionReturn { root, ... }` | Original expression-root identity | Authenticated root/code join in `start:299–315`, then `begin_root`. |

The active demand is the nearest such live delimiter. If forwarding removes
the outer Root/ExpressionReturn, the crossing is labeled from that pre-step
delimiter; the following pending/terminal request is the **same** event. This
is a trace attribution, not extra execution or a request rewrite.

`GlobalRead.site.source_root` belongs to the demanding read, and the operation
`request.source` belongs to the operation's lexical provenance. Neither is
substituted for the supplying initializer identity. Invocation `current_owner`
also does not identify the initializer: an operation or closure may run inside
its invocation while the same enclosing demand remains pending. The original
source/operation/payload/event and observations stay intact.

The table is authentic for actual constructed programs: `start:317–321` builds
the DefId-to-index map from original `definitions`; empty ModuleDef lookup uses
that map, not an arbitrary local cell. Expression handles have no public field
constructor and `start` checks the original program root/code association and
HIR ownership. This does not certify experimental inference or whole-source
validity. It uses the reviewed mixed-root identity/source formation component,
not a spelling-based identification of source effects.

### Delimiter invariant

Induct on actual transitions from `start`:

1. `start:325–350` creates empty frames/cells/templates and ModuleRun owner,
   then calls `begin_root`. That constructor installs one bottom Root or
   ExpressionReturn before entering source code. Its end-of-plan selection
   either completes an existing cache or installs a selected-definition Root.
2. Calls, Force, local binding, conditionals, handler installation, Name
   consumption and owner/view entry add ordinary frames above this bottom
   delimiter. An empty global Name adds an authentic GlobalRead above the
   current prefix, making that new initializer the nearest demand. A populated
   cache read adds no initializer demand.
3. Ordinary Return removes frames at the top. GlobalRead Return publishes only
   its returned value, restores its pending Name consumption and reveals the
   previous demand. Root/ExpressionReturn normal completion reaches
   `begin_root` only after their inner frames have returned; the former caches
   its returned value and the latter discards it. No request-forwarding branch
   calls `begin_root` or performs these Return actions.
4. Request propagation cannot cross a GlobalRead: it stops at that top frame
   before popping it. Root/ExpressionReturn are bottom delimiters, so once one
   is popped into the pending request suffix no caller Catch can exist below
   it. Only the same request's stack-exhaustion stop can follow.
5. A selected Catch necessarily lies above the nearest live demand: handlers
   are installed during source execution above it; GlobalRead blocks search
   for a handler below itself; no handler lies below the bottom delimiter.
   Therefore a selected raw continuation's saved segment contains no demand
   delimiter. `capture_template:1003–1075` additionally rejects Root/GlobalRead
   frames before publishing a template. Although its generic ordinary-frame
   case does not syntactically reject ExpressionReturn, a reachable selected
   capture cannot contain this bottom frame. `enter_template:1080–1165` rebuilds
   that selected inner segment above the current live prefix; it cannot
   manufacture a new root, GlobalRead or expression demand. Sharing the store
   and borrowing/freshening invocation owners does not change this fact.

During final forwarding a bottom delimiter may already be in the suffix and
no live demand remain. The state then is Request for the same event, not
Evaluate, Return or EnterTemplate. Thus the invariant includes that terminal
forwarding phase rather than falsely requiring a live delimiter in every
state. Abrupt discarding of a selected inner suffix does not remove a demand
delimiter or authorize publication of an arm result into a different cache.

## 3. Exhaustive escape and consumer proof

### Request creation and internal handling

The only production construction of a fresh `State::Request(PendingRequest)`
is `execute:1566–1593`, executing an existing Request carrier. It allocates the
fresh event and obtains observations before any unwind; the suffix starts
empty. Executing Delay instead evaluates its retained code/environment.
Ordinary returns and carrier construction alone are not outward events.

`propagate_request:1222–1344` first considers a top Catch, preserving actual
installation/owner, operation identity, eligibility, payload/OpCompat and arm
selection checks. Selection evaluates the original arm outside that handler;
it either retains the validated raw template or abandons only the discarded
inner suffix. This request has not crossed the enclosing demand delimiter.
An unavailable check stops the machine; it is not silently recategorized as a
successfully handled request, or as a completed outward-boundary crossing.

Handler arms and resumed code can themselves create subsequent requests.
The same constructor and delimiter analysis applies to each. They are counted
if they reach the boundary, regardless of whether their lexical SourceSite is
in the original initializer body, another definition's closure, an arm or a
resumed suffix. No rule omits these events merely because their original
trigger was handled internally.

### All outward paths

There are exactly two calls of `stop_unhandled_request` in production code:

- At `propagate_request:1350–1353`, the nearest pending GlobalRead is topmost.
  The outward request stops **in this step**, before that frame or any caller
  frame is popped/searched. The marker, pending consumption, cell and caller
  owner/view prefix remain live and unmodified by this cut.
- At `:1354–1357`, the frame stack is empty. A scheduled Root or
  ExpressionReturn was previously forwarded through the ordinary-frame case
  `:1395–1399`. That step appends it to this same request's suffix and sets
  `State::Request(request)`. A caller budget may pause between these steps.
  The next effective transition can only stop that same request; there is no
  intervening Evaluate/Return/EnterTemplate or new request creation.

Other forwarding cases preserve the same PendingRequest while recording the
ordinary suffix and performing the existing owner/view exits. They do not
execute caller source code. The boundary cut does not reset an owner, copy or
roll back a store, select another operation, invoke a synthetic global handler
or run `abandon_suffix`.

`stop_unhandled_request:1402–1415` moves the already unwound suffix and original
observations into `SavedContinuation`, and exposes the original source,
resolved operation ID, payload value and event in `UnhandledRequest`. It does
not publish a cache, perform pending Observe, or schedule the next root.
Normal Root/GlobalRead publication remains exclusively at Return:905–928.
Earlier completed caches are retained; they are not rolled back on this stop.

### Terminal absorption and public consumer closure

`step:382–385` returns a Stopped outcome before any mutation. `run:369–379`
uses `step`, and budget exhaustion merely pauses a nonstopped machine. Every
public call after an UnhandledRequest therefore reports the same stopped
event; it cannot create a second crossing. The Root/ExpressionReturn interim
Request phase likewise cannot create a second event even if paused. This
proves cardinality at every finite prefix, including prefixes before the
terminal outcome is returned. Completion after an escape is impossible.

The public surface is closed for this purpose: `value`, `continuation_depth`
and `steps` are read-only; `step` and `run` are the only advancement methods.
`ContinuationHandle` has a private field, is only inspected for suffix depth,
and has no public resume/response/reinjection consumer. Source raw Resume uses
the distinct private TemplateHandle created by a selected internal Catch; it
is not a host continuation API. A second `start` creates a different fresh
machine/store, not a continuation of this event trace.

`runtime/mod.rs` exports no additional advancing/global-consumer operation.
The actual tool consumer, `lib.rs:149–168`, builds a fresh program/machine,
runs it, and converts UnhandledRequest to an error. It never feeds a response
back. `prepare:214` uses `SemanticImports::empty()`. A user-declared Act named
`io` is not thereby an automatic global consumer. This audit establishes the
current error-only scope; it does not claim the approved automatic-global
case has been implemented. The same original continuation contents are kept
privately, without asserting they are externally resumable.

## 4. Nested demands, caches, mixed roots and order

If A awaits an empty B, B's GlobalRead is nearest. A's Catch around Name(B)
cannot handle B's outward request; B's first such request stops before A's
caller prefix is traversed. It is one event labeled B, not an event labeled A
or two nested escapes. If B instead handles all its requests internally and
returns, its cache is completed by the ordinary Return route, and A may
continue. A later escaping request is then labeled A. Prior internally
handled B requests do not enlarge the outward trace.

If B is already cached, its read is ordinary consumption and creates no B
initialization delimiter. Later forcing/calling a cached latent value occurs
under the then-current demand, whose own internal handlers are considered.
Lexical authorship does not retroactively make this B initialization. No
claim of B initializer purity is inferred from this cache behavior.

Mixed definitions and expression roots retain the separate source identities
in §2. A normal expression result is discarded without a Global cache write;
request propagation does not mistake it for normal completion. The stronger
trace over both root kinds has length at most one, so restricting it to
definition initialization does not hide any second initializer escape. The
canonical CLI source plan and successful cache skips are retained, but their
existence is not a proof of early-entry timing adequacy.

For the actual outward trace T, a reversed pair would require indices i<j
with source-order(label(T[j])) < source-order(label(T[i])). By §3 there are
no two such indices. This uses every actual boundary crossing; it does not
filter out the sole outward event because it leads to an error. In particular,
a demanded later initializer's escaping event remains present. The theorem
cannot say what an earlier suspended initializer would have done, whether
that later entry was permissible, or whether this one-event trace refines a
specified successful source trace. Those claims require their original source
and consumer premises. They do not follow from lack of a witnessed inversion.

If a future automatic global consumer handles an outward event and continues,
or a public API resumes the terminal saved suffix, the absorption premise
changes. This proof must then be replaced/extended at that actual consumer;
it is not authority for using cardinality as a detector or scheduler.

## 5. Apply the approved boundary to the reviewed example

The independently reviewed [source-observation calculation](2026-10-16-initialization-effect-order-source-observation.md)
§§2–5 gives the internal active-demand trace
`[(later,ping,payload2), (first,ping,payload1)]`, with each request selected by
its initializer's own handler and both whole initializer outward images
empty. Applying the now-approved observation yields the outward trace `[]`.
The internal `ping2 -> ping1` order alone is consequently no relative-order
violation. These are actual internal Request events, not absent occurrences;
their removal from the **outward** projection is justified by their internal
handling, not by a failure outcome or a pure Name judgment.

This application certifies neither parsing nor experimental inference/full
admission of that spelling, nor the permission to enter later while first is
pending. It does not settle all forward dependencies. The prior note's kernel
and authentic-graph calculation and the approved answer explicitly retain
those distinctions.

## 6. Dependency snapshot, checks and handoff

SHA-256 values read directly for this frozen producer packet, before later
primary review/status metadata:

| Input | SHA-256 |
| --- | --- |
| runtime/machine.rs | `04024174d88223e252e1d093eaee96c17d9f43d4d32bea5c41631017c9da208c` |
| runtime/program.rs | `b9798ac4c5d93e761582d712114615defa913f858d70e91f170471c8b8912748` |
| runtime/continuation.rs | `194e925c2e19816e05e8d0cdf773123f205dce47d36d83a70385daa07a77e2b3` |
| runtime/receiving.rs | `5443c8ca55e58a37b6d003cf5b2985214d37776094f02637adfbe30200cc36bd` |
| runtime/mod.rs | `64d208743793a03501a76f56bc2b511c50ed40cff3f789757a00b7d608fc846b` |
| playground src/lib.rs | `bace98ef2f11c9bb638b4f1f7536178c668ca8b0448fb0276986fbf0772f524b` |
| observation approved-answer.md | `f6bbefc18aa7760d7c5002cb404142ac66d4bc3bb088b2aeb6b667bb69f4ef6a` |
| observation answer-draft.md | `8b097f9d4c5b0e49790dbcb6fdabb7126c8a98eff157dee9a13eac8af6b89526` |
| governing design including approved addendum | `51fbbc5b0c977dc348b5aeaf8d8ed323dee02089ae30ca4948f7087c3c8e8d2b` |
| initializer-handler-boundary-preservation.md | `e13dc828164f3e2cef747fa69d4c70ca46c5478b8f5067481a2fef3a4440871a` |
| initialization-effect-order-source-observation.md | `b1eef34641d0bf3e616be474de7220b9e9242031cfe219bd1be9c542163ebaba` |
| playground-initializer-boundary.md progress receipt | `e9e41e6dc6f44f85a302e1fa4b40b04f07185378bdcbfaf097624885b4adfc29` |

Runtime paths in the table are under
`tools/inference-playground/src/runtime/`. No production dependency was changed.
The primary appended the independent transcription-review receipt to the design
during this pass; the final reread confirms unchanged approved semantic clauses.
Checks: bounded source reads, public-consumer/request-constructor searches,
direct hashes, and note whitespace check. No tests, builds, executable source
probes or Git operations. The primary's 108-test receipt is independent input,
not a run performed or a general proof supplied by this packet. No additional
runtime cost, monitor or state is proposed.

Requested routing: normal configured prover, Sol/high; configuration declares
default subagent `gpt-6.1-sol`/high and no prover model pin. Effective execution
model/effort metadata is unavailable here. One leaf, no delegation.

The original full source initialization/materialization gate remains OPEN.
The concrete proved local result is error-only outward-prefix cardinality and
its no-observed-inversion consequence. The separate source entry-timing/full-trace
and automatic-consumer obligations remain. Do not implement an ordering detector
or global consumer on the strength of this result alone.

## 7. Independent review and primary receipt

`runtime_semantic_review` returned CLEAN at producer SHA-256
`96470065bfb5ed054a6cab04645a3f64401da5fe91e2d17b8b92eff462e58c07`.
Its fresh mathematical/source review covers every current public advancement
path, budget pauses, polling, nested demands, caches, mixed roots, raw Resume
and authentic demand labels. No missing transition or re-entry consumer was
found. The independent `materialization_correspondence` consumer census also
found no counterexample and identified the intermediate Root/ExpressionReturn
Request phase explicitly.

The primary accepts exactly the §1 theorem: at most one distinct crossing per
fresh machine trace, none on completion, hence no observed inverted pair. This
does not close source-prefix refinement, omitted earlier effects, initialization
entry timing, scheduling/admission, automatic global consumers or whole
materialization. Mode M2, one fresh semantic reviewer, static artifact/hash/
link/whitespace checks only; zero new builds/tests/probes or measurement samples.
The existing 108-test runtime checkpoint remains evidence for unchanged code.
