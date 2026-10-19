# R121: unmatched request and the real remaining expression root

Status: **conditional finite source-to-machine derivation; fresh review pending**.
Assignment `R121-PROOF`, revision 1; sole author/writer
`/root/r118_proof_lane`; no coauthors or descendants.
Contract rev1 SHA-256
`33c0c714e08667093732a8abb6ecf22ceed8547cae8459fa978b971996310fa8`;
baseline `0d33b715b9f311674ec7ebf125b9d2f73d70f037`.

## Original parent and exact finite cases

The original unmatched-outward-request-plus-suffix parent retains its original
source domain and quantifiers. This packet applies constructor/control facts
to two exact source cells; it does not replace that parent by a finite theorem.
All six effect parents, original Simple-sub/evaluator A/B, F1/FK1 including
foreign continuations, method/role M/T/A and R85 adoption remain OPEN.

Negative: 159 bytes without final LF, specified source SHA-256
`685aa2465d5a5b47d18447762637107b4cb0da5971d384fad7bc1ad56937448f`:

```yu
act io:
    our tick: int -> int
    our other: int -> int
catch io::tick 7 { io::other(p), _ -> 99 }; catch io::other 23 { io::other(q), _ -> q }; my main = 7
```

Positive: 158 bytes without final LF, specified source SHA-256
`11f811ba795dfc8420aadd0706221fe14f1efa9a192b902bda5b7816d627924f`:

```yu
act io:
    our tick: int -> int
    our other: int -> int
catch io::tick 7 { io::tick(p), _ -> 99 }; catch io::other 23 { io::other(q), _ -> q }; my main = 7
```

The positive cell changes only the first operation pattern. Each source is
prepared into its own authentic HIR; root, binder, declaration and occurrence
identities are compared only within that HIR. Equal text or corresponding roles
across sources/direct-Machine/CLI preparations do not imply equal opaque IDs.

Conditional result: the negative machine stops with the original tick request,
payload integer `7` and its original Apply SourceSite; its saved root completion
still designates the actual unexecuted second expression root. It does not run
that root or selected main. The positive machine completes both expression
roots in order, discards `99` and `23`, then materializes main and completes with
its separate integer `7`. Under successful public I/O the predictions are,
respectively, failure/empty stdout/existing unhandled-request diagnostic and
success/stdout `7\n`/empty stderr. No execution was performed by this author.

## Explicit premises and authority

**H: authentic source formation.** Parsing these exact bytes succeeds with the
intended direct item sequence: Act declaration, first Catch expression, second
Catch expression, separate main binding. The original root keys/occurrences,
resolved operation declarations, own catch binders, literal spellings and
supported LocalSource bodies are authentically retained. The source parser
dispatch/annotation-declaration implementations are not added as dependencies;
successful exact-byte production is an explicit premise, not inferred from
assumed forms or visual text order.

**A: ordinary admission and correspondence.** Candidate preflight/ordinary
solving accepts this same authentic HIR without conflicts; full RuntimeProgram
construction/start succeeds. Source typing/operation compatibility and ordinary
transitions satisfy the reviewed component premises. Static constructors below
preserve these supplied identities; they do not prove full inference soundness.

**P: runtime evidence.** The exact primitive operation signatures, authentic
root/binder graph and whole-program closed-primitive certificate are established
as detailed below, and installation/primitive-view checks succeed. A missing
Grant alone is no negative permission fact. **B:** identity/resource checks and
I/O succeed; each predicted terminal outcome is reached within 30,000 transitions.
No measured fuel count or unconditional source termination is claimed.

Earliest unestablished premise is H's exact parser-to-authentic-item/carrier
production, followed separately by A and actual bounded P/B transitions. This
packet supplies a conditional source-constructor-to-machine correspondence,
not observations that establish those premises for these bytes.

Charter §§14–15 govern exhausted shallow matching/forwarding and outside arm
execution. The approved module-expression owner supplies honest expression
roots, source-order expression demands, discarded expression results and the
separate selected-definition fallback. Approved initialization order does not
authorize a new global handler, demand reorder or future resumable consumer.
This source has no forward global demand, computation-annotated lambda, raw
continuation call or Function-role elaboration requiring an additional §§21–24
law. Its actual operation invocation still uses ordinary declared entry.

## Authentic item order to the live two-root schedule

Name the two expression roots `e1`, `e2`, their code labels `c1`, `c2`, and
main's definition `d_main`. These are symbolic actual identities under H.
The two sources instantiate the same derivation separately.

1. `module::lower_module_with_counters` enumerates direct syntax node children
   into plans in order (1173 onward). `plan_root` (1955 onward) recognizes each
   authentic OperatorChain as DirectExpression and the final BindingStatement
   as Binding. The Act is a declaration placeholder on the opt-in route.
   Neither Catch is a fabricated binding, definition ordinal or Lambda.
2. The same ordered plan loop mints a fresh occurrence and ExpressionRootId
   only for a DirectExpression, records its original source key and stores the
   occurrence/root join (1230–1250). A separate DefinitionRootId is allocated
   only for the actual main binding. `lower_direct_root_expression` (2185 onward)
   preserves the supplied root occurrence even if its ordinary projection has
   unsupported/error metadata; such metadata is not itself proof of admission.
   Item insertion follows the plan loop's order.
3. The expression carrier pass (1309–1326) retrieves the root by that expression's
   original occurrence and calls `form_ordinary` with Expression(root), not a
   selected-definition surrogate. LocalSource `form` accepts DirectExpression,
   and its Catch constructor (1120–1191) retains original scrutinee, ordered arm
   pattern/body, operation resolution and catch binder source. `Builder::set`
   uses the original expression-root occurrence at slot zero (818 onward).
   Supported carrier publication is required by H/A; Unsupported is not success.
4. `RuntimeProgram::from_hir` iterates the HIR item slice in order, gets each
   expression's actual root through `hir.expression_root(occurrence)`, and
   authenticates its retained LocalSource (program.rs 275–301). Label construction
   validates source indices. Code.site retains root/occurrence/range; Operation
   and Catch instructions clone actual resolutions/patterns/body labels.
5. In that same item loop (570–610), every expression inserts its root/body join
   and appends ExecutionRoot::Expression. The Act placeholder contributes no
   demand. Main's body is Integer/transparent Forward, so the existing computed
   binding classifier does not add it to the demand list. Thus the **complete
   actual source schedule** is precisely
   `[Expression(e1,c1), Expression(e2,c2)]`, in this order. This derives from the
   item fold, not iteration order of expression_roots' HashMap.
6. `execution_roots()` returns that actual schedule. `start_source_schedule` uses
   it directly; the public `start(selected,&roots)` control uses the same returned
   vector. `Machine::start` validates each original root against the program/HIR,
   checks its exact code join and uniqueness, then constructs
   `execution_roots = [ScheduledExpression(e1,c1), ScheduledExpression(e2,c2)]`
   (machine.rs 288–340). Arbitrary validated custom root vectors do not establish
   source order; this derivation uses only the authentic complete vector.
7. Fresh machine state is ModuleRun with main's global cell None and no frames.
   `begin_root(0)` increments the cursor and pushes
   `ExpressionReturn { root:e1, next:1 }`, then starts c1 under environment 0
   (1807–1857). It does not create an expression cache cell or execute main.
   `execution_roots[1]` is already the real authenticated `(e2,c2)` record.

This is the source/static identity of the later root, not merely a prediction
that some later text executes. Each direct-Machine/CLI preparation needs its
own authentic e1/e2 join. No cross-artifact identity equality is claimed.

## First operation, literal decoding and request provenance

Under H, LocalSource operation resolution gives declaration IDs `d_tick` and
`d_other`, distinct operations of the same authentic family. The first request
uses d_tick in both cells. Its Operation expression has occurrence `o_tick`;
its enclosing ordinary Apply has a **different** occurrence `a_tick` and
SourceSite `s_tick`. The request's source is s_tick, not a guessed span and not
necessarily o_tick's range.

LocalSource `integer_spelling` (425–432) requires one original Integer token and
retains its exact text. Machine Integer evaluation (531–539) calls the now-pinned
`literal::integer`: nonempty ASCII digits are accepted and leading zeros removed.
The spellings `7`, `23`, `99` therefore decode to exactly those canonical integer
texts. This establishes the native payload representation given H's original
tokens, resolving R113's old unpinned-decoder seam without reusing its fixture.

Apply obtains the Operation, makes the entire payload expression an inert Delay,
creates its real operation invocation and evaluates the declared Value argument
inside that invocation (880 onward, 1013–1065). The retained Frame::Callee site
is s_tick. OperationPayload calls make_request_carrier with that same site;
ReceiverReturn ends the operation invocation; OperationResultConsumer then
executes the returned carrier under ModuleRun. `execute(Request)` (1929 onward)
mints event q and PendingRequest with that embedded original declaration,
received payload and source. Temporary operation-entry frames have all returned.

At this point the stack is exactly
`[ExpressionReturn(e1,1), CatchReturn(h1,env0,ModuleRun)]`. Catch h1 was installed
when evaluating c1. Its installer is the dynamic ModuleRun owner, distinct from
static root e1. There are no pending views, global reads, local suffixes or
receiver frames above/below h1 other than that one expression completion.

## Negative: exhausted match, original request and saved cursor

1. `propagate_request` validates h1's actual ModuleRun installation, then scans
   its sole arm (1531–1579). Its resolved declaration is d_other, while q has
   d_tick. The ID inequality takes `continue` **before** candidate Grant/payload
   checks. Same family does not convert this into a match or permission failure.
   No arm is selected, no p binding is installed, and `99` is not evaluated.
2. The exhausted-handler transition pops h1 and appends
   `SavedFrame::HandlerBoundary { handler:h1.code, environment:0,
   installation:h1.installation }` to q.suffix (1702–1759). It preserves the
   same declaration, payload, source, event and observations and returns Request.
   This is forwarding the original request; no replacement request is emitted.
3. The next propagation step pops the remaining expression completion through
   the `ordinary => SavedFrame::Ordinary(ordinary)` branch. The saved frame is
   exactly `ExpressionReturn { root:e1, next:1 }`, unchanged. Consequently
   q.suffix, in next-return-first order, is
   `[HandlerBoundary(h1), Ordinary(ExpressionReturn(e1,1))]`.
4. The stack is now empty; stop_unhandled_request (1763–1774) stores that suffix
   and observations in SavedContinuation, then publishes UnhandledRequest with
   q's original source s_tick, operation d_tick, payload handle for integer `7`
   and event q. Neither propagation nor publication changes these identities.
5. The saved frame contains **root/cursor only**. Machine.execution_roots remains
   the same live two-record schedule; its index 1 is `(e2,c2)`. No root schedule
   is copied into SavedContinuation, HandlerBoundary or ExpressionReturn. The
   continuation handle is an opaque saved outward suffix, not a source raw-k
   template or evidence that any external resumer is available.
6. Request propagation never called ExpressionReturn's normal return branch,
   whose only advance is `begin_root(next)` (1199–1205). Therefore c2 has never
   been scheduled, its `io::other 23` and arm have never executed, and main's
   fallback has not been reached. No code in the first root reads a module
   definition, so main's cell remains None. `Machine::step` on terminal Stopped
   returns that outcome; run does not execute the saved suffix.

This proves the exact cursor/live-schedule relation conditional on H/A and the
reached bounded request. There is a genuinely nonempty unexecuted schedule tail,
unlike the old R113 fixed case. The later root's different catch is not already
installed and cannot retrospectively handle q.

## Positive: closed primitive matching, both roots, then main

The positive first pattern resolves to d_tick. Both positive catches execute in
ModuleRun, so a positive invocation-local Grant is not available merely by
family equality (`receiving::local_grant` rejects ModuleRun). The required
matching route is the whole-program closed primitive certificate.

`primitive::closed_primitive` (31–217) examines all code and all arm patterns,
then visits **every definition body and expression-root body**, and rejects
unvisited orphan code. Under H's exact supported source graph: there are no
Lambdas, recursive locals, global dependencies or bound continuations; all
operation signatures are primitive int→int with absent outer effects; p/q
are distinct authentic catch binders owned by their roots; both continuations
are wildcard; q's Name is Observe of its registered catch binder; every Apply
has a direct resolved Operation callee and literal ground argument. Each Catch
and its complete arm/scrutinee graph is visited. Literal main is also visited.
Transparent Forward/empty-block wrappers retain those traversal edges.
All classifier branches therefore accept that graph, subject to H/A's actual
authentic body/code coverage; this is the conditional P certificate derivation,
not an observed boolean from running this source. The negative graph is likewise
primitive, but its mismatch branch does not need that certificate to forward.

1. On first q, h1's ID matches d_tick. With P and primitive Value payload `7`,
   selection pops h1 before arm code, uses no continuation template, binds p to
   the payload, and evaluates `99` outside h1 (1580–1680). No saved inner suffix
   exists to execute here. Returning `99` reaches ExpressionReturn(e1,1).
2. That completion discards `99`, checks e1 is still in the immutable program's
   expression map, and calls begin_root(1). It schedules the already-existing
   second slot, pushes ExpressionReturn(e2,2), and starts c2 under ModuleRun.
   It has published no expression/global result.
3. Second catch h2 is installed now. Its ordinary operation request has a fresh
   event, declaration d_other, integer payload `23` and its own original Apply
   SourceSite. The sole arm's d_other matches; its own installation, certificate
   and primitive checks succeed. Selection removes h2, binds original q to its
   own payload, and evaluates the arm's original Name q in that environment.
   The Name returns `23` by catch-binder identity. No request/identity from root1
   is substituted for this root2 event.
4. ExpressionReturn(e2,2) discards `23` and calls begin_root(2). Only now is the
   complete source demand list exhausted. Since no prior source code read main,
   its cell is still None. The selected-definition fallback pushes a real
   Root {cell:main,next:2} and evaluates main's own Integer `7`. That separate
   literal value is not root1's request payload despite equal text.
5. Root completion caches main's value and calls begin_root(2) again. It now
   sees main's populated cell and stops Completed with its handle. The completed
   public value is neither discarded expression result `99` nor `23`.

## Public projection and precise evidence limits

`lib::prepare` (266 onward) parses/lowers once, ordinary-solves a clone of its
HIR Arc, checks conflicts and returns that same HIR to execute/from_hir. The
public source-schedule start is the same one traced above; H/A remain actual
source/admission premises. With the exact CLI flags, scoped is false and the
budget is 30,000. Successful positive completion renders main's integer text
and one LF. main.rs prints only on Ok, returning success without error output.

For negative UnhandledRequest, execute returns the existing bounded error
`unhandled runtime request at {s_tick.range:?}`; main prints it with one newline
to stderr and returns failure. It does not reach the stdout print. Its range
must be read from the authentic HIR/LocalSource Apply occurrence, not inferred
by slicing `io::tick 7` or by the operation-name occurrence. Output caps permit
these finite messages; successful input/output remains B. There is no completed
receipt on that branch. A matching CLI status/stream is only external finite
evidence; it does not reveal the private saved cursor by itself.

The source-remaining-root constructor/formalization and its construction proof
refer to a different receive/f/ctrl.choose phase and its complete typed relation.
Their independent phase/maps/provider premises are not provided by these cells.
They are **not used** to identify the live module root schedule, certify this
opaque continuation, or close any foreign-provider quantifier. The relevant
reused root theorem is runtime-module-expression-roots §10's structural/control
result, with its original source/admission/materialization premises. Earlier
binding-only snapshots in that note are not descriptions of current code.

R113's pinned closeout is reused only as reviewed conditional cursor evidence
and its precise missing-decoder/nonempty-tail limitations. R121 supplies a
different two-root input and inspects the now-pinned literal decoder. It neither
repairs nor retries R113 and does not import its unobserved source preparation.
Existing primitive/root/CLI tests are inventory/comparison, not new executions
or proof that actual source constructors emit the assumed graph.

## Mutual TODOs and stop boundary

| Request / owner | First missing evidence and proposed output | Exact falsifier |
| --- | --- | --- |
| `R121-SOURCE-1` / Luna source reviewer and HIR/candidate owners | Establish H/A for both exact sources: original Act/expression/expression/main item order, two distinct source roots, original operation-use plus enclosing Apply, and supported ordinary admission | Missing/reordered expression root, wrong binder/operation/Apply identity, source refusal/conflict, or a fabricated transition carrier |
| `R121-CURSOR-1` / Luna compiler/source reviewer, RuntimeProgram/Machine owners | Verify the constructor fold and exact negative saved ExpressionReturn(e1,1) against the same live schedule's e2 at index1 | A copied root schedule claim, next cursor not naming actual e2, changed original q fields, second-root/main execution on negative, or request source mistaken for operation-token span |
| `R121-PRIMITIVE-1` / compiler/source reviewer, primitive::closed_primitive | Establish exact source graph's whole-code certificate and positive installation/primitive checks | Any unvisited code, nonprimitive/bound continuation/Lambda, foreign binder, failed certificate or assumed ModuleRun local Grant |
| `R121-OBSERVE-1` / Luna implementation/verification lane | Freeze two exact direct-Machine/CLI cells, authenticate each program's own ordered roots and operation/Apply identities, then only the contracted command after three CLEAN reviews | Different source/status/value/streams, ungrounded diagnostic range, exhaustion/failure/non-admission, or output alone presented as private cursor proof |
| `R121-REVIEW-1` / Luna | Fresh compiler/source, spec and regression review after both writers stop | Producer/coauthor certification, general parent closure, semantic adoption or production promotion from these finite cells |

No production implementation TODO or lease is granted. Earliest unresolved H
and all parent source/typing/native quantifiers remain at their original owners.
Generation, accumulation, propagation, levels, extrusion, qualifying intrusion,
generalization and independent residual/provider/witness lineages are preserved.
No ordinary inference or accepted-source restriction is weakened for this trace.

## Frozen dependencies, authors and resource receipt

All 24 contract input pins plus contract SHA-256 were revalidated and matched
before writing. Exact source dependency hashes are the immutable contract's
listed rows; the following proof-defining inputs are used directly:

| Input | SHA-256 |
| --- | --- |
| charter | `547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed` |
| initialization-order decision | `e2f70f535319522261cc6f52592d62b491d9d0e9d32e14310ac5d9fb81ee1bb6` |
| module-expression owner | `ab12b442f4f3d3d11565c89cda82c1cb25b17e943c2851b6bc937252410311e5` |
| runtime-module-root theorem | `915f99eb5cbd9734c3d1e4e0b778682bf1dbb3a8044ea21d5d77cee9d7250694` |
| R113 closeout | `a3dc4937b41bda6fe8570cc329987b584bfb704ded5012bb4fab0d0ac7078e49` |
| runtime/program.rs | `c2363ad42104b895519bb29a8eb9aeda545bd0176cebbd78750d3a2df90849ca` |
| runtime/machine.rs | `fa8dab7f7146f528ad354f336cdfe6e41a728505f9c3dd80c6df64e843dc5b46` |
| runtime/primitive.rs | `97485b9439357497aaf3f19555b1d87eef4aabc955b3a2815f23cf49a65c0153` |
| runtime/literal.rs | `2fff177a7ba0cabb4930251e1facc8f9be701ff3ec7baa695ce4c182fa1da35f` |
| runtime/receiving.rs | `8c81deadc48c4770f25760e9086d2053815785ff16cfd5580fa814fb83af9bd9` |
| HIR module.rs | `153a23ecaa68fd150d8bd0cc0316f3723e1cb5d98a6e3026aadef2bfd08fd907` |
| HIR local_source.rs | `3014628f861840ca8e716b3baf8e6a3c9dd736b1bad318b32e7a7b195ddf8786` |
| playground lib.rs | `bdf996d0264e252e345c05bc77b2adcf625120281244171f0054f1d87a8d1e1b` |
| playground main.rs | `75b38435f4634ee35b3e14a54fb4d021b78bda834b4fd53965302a73309e0100` |
| playground output.rs | `04e99c5bdb562a8edb8a7e17bdcc03f7b46eaca9d8e13b20216b4dcf3032a88a` |

Abbreviated source paths are the exact contract paths. Unused inventory body
hashes and nonapplicable remaining-root inputs are not upgraded to premises.
Historical theorem contributor identities remain UNKNOWN where their header
gives only an assigned prover leaf. Decisions/contract/closeout owner Luna;
compiler/test/charter byte authors UNKNOWN. Present author cannot certify it.

Requested Sol/high; requested exact model version UNKNOWN; observed model/effort
UNKNOWN/UNKNOWN. First clock `2026-10-19 09:42:54 UTC`; pre-clock inventory stays
charged. Cap 600 sec, unexpanded; exact allocation-start/CPU/memory UNKNOWN.
Static text/source/hash inspection only; no executable verification commands,
tests/builds/CLI/probes/Git, code/question edits, external contact or descendants.
Exactly this note and `tasks/agent-loop/inbox/20261019-r121-proof.md` are new;
no scratch/generated paths. Final receipt is in the handoff. Freeze revision 1,
then **STOP**; Luna owns intake, independent reviews and any later command.
