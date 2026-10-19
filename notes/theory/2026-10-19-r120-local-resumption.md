# R120: original pending local through one raw resumption

Status: **conditional finite source/runtime derivation; independent review pending**.
Assignment `R120-PROOF`, revision 1; sole author/writer
`/root/r118_proof_lane`; no coauthors or descendants.
Contract rev2 SHA-256
`6af7d6ad17684de717742586baa3d504adc73da6a37b8ba511b59a2ca327ff68`;
baseline `af551a720`.

## Parent and exact statement

The parent is the original continuation capture/resumption hygiene obligation,
with original source scopes, pending suffix, current cells and owner lifetimes.
R120 establishes only one conditional finite instance. Arbitrary raw resumption,
foreign continuations, original F1/FK1, all six hygiene parents, Simple-sub and
evaluator A/B remain OPEN. R119's M/T/A and R85 adoption remain independent.

For the exact 175-byte contract source, no final LF, specified source SHA-256
`7f3e39f4eb59da052e209bae88cd80cedff00e7158d0818e8b02c5faa70ee25f`:

```yu
act io:
    our tick: int -> int
    our other: int -> int
my relay (thunk:[io] int) = catch thunk { io::tick(p), k -> k 9 }
my main = relay { my result = io::tick 7; result }
```

Under H/S/E/B below, the original pending local completion writes response `9`
into its original local cell, the original final Name reads that cell, and
the completed value propagates through the resumer and relay to main. The
pinned public caller renders `9\n` with success and empty stderr. This author
ran no source, test, build, CLI or executable probe.

- **H — authentic HIR/admission and same-HIR path.** Actual parsing/lowering of
  these exact bytes succeeds, preserving the resolved `io::tick` declaration,
  relay's own `[io] int` parameter/annotation, catch binder identities, original
  block/local/body and lexical resolutions. Candidate inference/preflight and
  whole-module RuntimeProgram admission succeed. No hand-built carrier or
  alternate HIR substitutes for those constructors.
- **S — source correspondence/typing.** Ordinary transitions and annotation,
  payload/response/arm typing satisfy the supporting theorems' actual source
  premises. These notes' reviewed conditional mathematical results do not prove
  compiler soundness or authentic source generation.
- **E — runtime evidence and lifetime.** The same-value/view, annotation-owner,
  concrete `io` permission, authentic receipt/execution/observation, active
  installation and primitive checks succeed. The positive local Grant route is
  explicitly traced below; neither family spelling nor a stored continuation
  alone supplies that route. View reentry must authenticate its original packet.
- **B — finite success.** Resource/identity/I/O checks succeed and completion is
  within 10,000 transitions. No measured count or unconditional termination is
  claimed. Failure withholds a successful public value.

## Governing scope and reused mathematics

Charter §§14–15 supply outside shallow arm execution and absence of automatic
selected-handler reinstallation. §§16–17 supply surviving invocation and whole
argument reification mechanics **subject to §24**: §16's universal classification
of functions as handlers is superseded. §21 assigns `thunk` Computation from its
own explicit outer annotation. Neither `[io]` spelling nor ordinary call entry
introduces an extra handler; this source installs its catch explicitly.
No fresh-receiver law, universal handler classification or target-selection rule
is imported.

The pinned primitive-root receiving theorem supplies a reviewed local theorem
for authentic explicit ground computation formals, original annotation/view
lineage and compatible source transitions. Its global typing/transport premises
remain S. The pinned raw-template theorem §§10–12 supplies the implemented-path
Bind/Owner/View correspondence, borrowed-owner lifetime and current-cell rule,
within its actual typing/current-configuration premises. Its earlier conditional
or obsolete source snapshots are not treated as current implementation facts.
Current pinned source is inspected below, including the flat arena/map/activity
implementation. The progress receipt supplies historical bounded implementation
review/verification only. It is not this public CLI run or general parent closure.

## Source and public entry correspondence

`lib.rs::prepare` (266 onward) constructs one HIR Arc through
`lower_module_with_local_source`, gives a clone to ordinary
`CandidateInference::solve` when scoped is false, rejects conflicts and returns
the same HIR. `execute` (167–204) gives it directly to `RuntimeProgram::from_hir`
with default evidence and starts its own source schedule. This establishes the
same-HIR wiring conditional on successful H; it does not establish that exact
source preparation succeeds. Special operation-v1 entry/evidence is not used.

`local_source.rs::Builder::block` (1236–1366) retains an original HirLocalId for
`result`, its binder key, initializer and final expression. Work::Initializer
forms the original initializer; Work::Publish (700 onward) restores the enclosing
lexical depth and installs that same Local(id). Final Name construction resolves
through that lexical entry. No equality of spelling substitutes for identity.
The original final Name and binder are distinct source occurrences.

`RuntimeProgram::from_hir` retains local initializer labels, original local IDs
and ordered block/final-expression labels (435–447, 515–529). Its recursion walk
only marks a local self-reference active for a parameterized local initializer;
this zero-parameter `result` binding is nonrecursive (346–373). Its Name
instruction clones Local(id) and assigns Observe, whereas relay's own explicit
computation parameter gets Execute consumption (414–475). Lambda construction
passes the same original parameter to RootCompSchema::from_parameter. Candidate
preflight/emission requires authentic source ownership and retains body/local/
formal identities and ordinary Apply endpoints (`candidate_source.rs` 451–504,
826 onward, 1258–1368). These source consumers do not prove H or complete solving.

No concrete opaque ID, environment index, cell index, event number or source
range is fabricated. Use these symbolic runtime identities:

| Symbol | Distinct meaning / constructor |
| --- | --- |
| `l_result`, `b`, `E0` | Original local ID, original block code, and caller lexical environment captured by relay's argument Delay |
| `c` | Pending result cell allocated once by begin_local, initially None |
| `r` | Relay invocation; its ordinary ReceiverReturn remains below the catch |
| `h` | Selected catch installation owned by `r` |
| `q`, `H7` | Original tick request event and its payload integer `7`; payload bound to catch `p` |
| `t` | Immutable raw template retaining q's declaration/event and suffix |
| `a` | Distinct actual invocation created when raw `k` is called |
| `H9` | Handle of evaluated response integer `9`, later stored/read as result; its roles are not identified with each other |
| `x`, `x'` | Original and resumed computation executions: same view/receipt, distinct execution occurrence |

## Exact pending context and capture

Stacks are bottom-to-top. `R_main` is main's publication Root and `RR_r` relay's
ordinary receiver return. Successful callee initialization finishes before its
argument runs, so no pending relay GlobalRead is inside the request suffix.

1. Calling relay obtains its closure, allocates inert Delay(block b,E0), enters
   invocation r, binds its Computation parameter and installs h. `consume` of
   `thunk` records a genuine receipt, opens execution x and pushes its
   RootCompReturn, then executes the Delay (`machine.rs` 880–1008, 1858–1890).
   RootCompSchema's actual owner/outer-effects/Int checks are in
   `receiving.rs` 21–43. The initial argument image may be unknown; entering
   relay adds its own genuine local boundary rather than assuming inherited
   coverage complete.
2. `begin_local` (1891–1928) allocates c=None and pushes
   `F = Local { block:b, next:1, environment:E0, cell:c, recursive:false }`.
   It starts the original `io::tick 7` initializer. The final Name has not run;
   the nonrecursive result binder is not yet linked into runtime E0.
3. The operation invocation evaluates payload `7` and returns its request carrier;
   OperationResultConsumer executes it after that operation invocation returns.
   `execute(Request)` creates q with current observations and empty suffix
   (1013–1065, 1929–1960). Temporary operation frames have finished. The live
   stack is exactly `R_main, RR_r, CatchReturn(h), RootCompReturn(x), F`.
4. `propagate_request` pops F unchanged into the next-return-first suffix, then
   ends/pops x and saves its RootCompReturn. At h, current executable owner r
   is still active. The operation use/pattern IDs agree under H; primitive
   payload and candidate evidence pass under S/E. The suffix is exactly
   `[Ordinary(F), Ordinary(RootCompReturn(x))]`; neither R_main nor RR_r is in it.
   This exact shape avoids pending global/root publication capture; no general
   cache-capture theorem is inferred.
5. For bound continuation k, capture_template (1309–1381) folds that actual suffix
   into `t = Owner(r, View(x, Bind(Hole,F)))`, with original declaration/event q.
   It clones F's same b/next/E0/c/recursive fields and adds the containing r
   because RR_r lies outside the capture bound. Nodes own no store snapshot.
   There is no ForwardHandler node: selected h is still on the stack during
   capture and is outside the suffix.
6. Selection pops h only after its checks, binds p to H7 and k to the template
   callable, and evaluates the original arm outside h (1580–1680). Because a
   template was captured, the suffix is not abandoned. Live prefix is now
   `R_main, RR_r`; r stays active. The arm's lexical environment is the catch
   environment extended by p/k; it is distinct from saved block E0.

Positive Grant justification within E: entry constructed the boundary for r
using the authentic `[io] int` schema; parameter execution opened x on a genuine
entry/read receipt of that same view. q's observations authenticate that exact
execution. At h the owner is r and r is active. `local_grant` (receiving.rs
230–322) checks the schema's concrete family, finds the genuine candidate-owner
receipt for the same view/formal route, and traverses its image to r's boundary.
Thus this route returns true given those authentic construction premises, even
with unknown older coverage. No value of closed_primitive is assumed. This is
an actual conditional producer/query join, not an inference from no negative
certificate. Successful actual H/S/E evidence remains unobserved here.

## Raw k 9, original local completion and output

7. Arm Apply evaluates k, makes the entire `9` argument inert, then the actual
   continuation-call branch creates invocation a and pushes RR_a and
   ResumeArgument(t). It executes that Delay once inside a (880–916). This is
   the ordinary actual call activation, not replacement of r or a general
   fresh-receiver law. Literal evaluation produces H9 as a Value ground view.
8. ResumeArgument (748–817) checks H9 against the **original operation result**
   declaration Int using primitive_matches, independently of request payload
   H7 and root schema Int. It pushes one ResumeReturn and starts t with a fresh
   per-use empty control map. The response is delivered to Hole; no original
   operation call or argument prefix is reevaluated.
9. Entering Owner(r) (1384–1440) finds r still active, assigns current_owner=r,
   records r→r and pushes OwnerReturn { owner:r, owned:false, previous:a }.
   It does not allocate or push another r, does not call receiving.enter,
   and leaves active order `[r,a]` intact. The inactive-owner branch is unused
   for this witness. It is not used to justify expired or foreign continuations.
10. Entering View(x) authenticates x's original view/receipt and allocates x'
    through receiving.execution; x'.occurrence is fresh. It pushes the new
    RootCompReturn and descends. It creates no new receiving boundary or receipt,
    changes no original event q and installs no handler. Bind pushes the exact
    saved F, then Hole returns H9 (1440–1477, receiving.rs 190 onward).
11. The reinstated F consumes that response via the ordinary Frame::Local return
    branch (1094–1162): `cells[c] = Some(Value(H9, its current view))`. Because
    recursive=false it extends **saved E0** with `(Binder::Local(l_result),c)`
    and calls begin_local(b,1,E_result). It allocates no substitute result cell
    and uses neither the catch environment nor a's argument environment.
12. No local initializer remains, so begin_local selects b's original final
    expression under E_result. Its Name resolves to Local(l_result), lookup
    follows that identity to c, and reads H9 (Name branch 550–617; lookup 1962
    onward). Observe validates/records the received view and returns it. This
    is genuine resumed body execution, not a direct jump returning response 9
    from k while bypassing the pending binding or final lookup.
13. RootCompReturn(x') ends that exact new execution and projects a ground view
    for the same value handle H9 (830–833). OwnerReturn's borrowed completion
    checks r remains active, removes no activation and restores current_owner=a.
    ResumeReturn passes the completed suffix result onward. RR_a then retires
    a and restores r; the arm returns through original RR_r, which alone retires
    r and restores ModuleRun (818–833, 1069–1080, leave_owner 1263 onward).
14. R_main publishes the returned H9 as main's completed definition value and
    source-schedule completion selects that cached value (1199–1213, 1807–1857).
    No selected handler is reinstalled at any stage. H9's response, local-store,
    lookup and final-result roles are distinct transitions, even though they
    preserve the same value handle; computation result projection can change
    its view. Payload H7 and the continuation callable are different values.
15. Under B, `lib.rs::execute` sees Completed(Integer("9")), emits `9` plus one LF,
    and main.rs prints it on the successful branch (main.rs 64–94). That branch
    writes no error to stderr. With successful public I/O the exact observation
    is status success, stdout `9\n`, stderr empty. A matching output alone does
    not establish the internal binder/environment or owner simulation above.

## Remaining premises, falsifiers and parent application

The parent application is this finite authentic-context implication: capture
retains the original pending Local and its cell/environment; raw response entry
completes that Local and executes its original final lookup under the borrowed
still-active containing owner; only then does the result return to the resumer.
It contributes this case to the continuation front without replacing its
arbitrary-source/foreign-context quantifiers by this one local frame.

| Request / owner | Missing evidence, inputs and next discriminating output | Falsifier |
| --- | --- | --- |
| `R120-SOURCE-1` / Luna's source reviewer; source/HIR/candidate constructors | Exact bytes, original own annotation/local/operation/catch identities; establish actual H and retain S's independent typing/transition premises | Different binder/scope, operation identity, unsupported source, conflicting candidate, failed annotation/admission, or a transition fixture substituted for actual constructors |
| `R120-EVIDENCE-1` / Luna's compiler/source reviewer; receiving and machine owners | Authenticate the traced local Grant, pending F fields, same original c/E0/b and exact owner lifetime through capture/entry/completion | Expired/replaced r, fabricated receipt, changed cell/environment/cursor, old observation treated as new event, bypassed saved body, or reinstalled h |
| `R120-CLI-1` / Luna's implementation/verification lane | Frozen new exact stdin test and all three CLEAN reviews, then only the one contracted command | Failure, timeout/non-admission, changed bytes, status/value/stream mismatch or steps exhaustion. No retry or old-fixture change is authorized. |
| `R120-REVIEW-1` / Luna | Freeze both lanes; fresh compiler/source, spec and regression reviews, independent of authors | A conditional theorem, prior test or matching output is promoted to general source/native proof, adoption or production authority |

The existing runtime test `raw_response_enters_the_hole_under_the_still_active_containing_owner`
contains the same fixture and asserts integer `9` (runtime_resume.rs 377–384).
This is the prediction's source anchor, not a new run by this author. Its adjacent
reusable-local test has different source and is not used to prove reuse here.
The helper uses 30,000 runtime transitions; its source assertion therefore does
not establish the new public cell's stricter 10,000-transition premise B.
The pinned 2026-10-16 progress receipt is reused only for its actual reviewed
bounded raw-template implementation premises. R111's failed one-shot receipt is
not evidence, is not read or altered here, and neither R111 recipe is substituted.
No theorem is inferred from tests that assume transitions.

No code edit is requested; the minimal already authorized evidence is the other
lane's new test-only public cell. H/S/E/B, arbitrary resumption, foreign
continuations, static/native projection, general permission and handler-priority
theorems remain open at their actual owners. Generation, accumulation,
propagation, levels, extrusion, qualifying intrusion, generalization and separate
residual/provider/witness lineages are preserved; no inference bypass or source
domain weakening is introduced.

## Frozen direct inputs, authors and checks

| Input | SHA-256 |
| --- | --- |
| Contract rev2 | `6af7d6ad17684de717742586baa3d504adc73da6a37b8ba511b59a2ca327ff68` |
| charter §§14–17,21,24 | `547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed` |
| primitive-root receiving theorem | `a043c69eb9fd82127bb7ad59d797abf3f10c5edf83bd80316183074f48c28606` |
| raw-template correspondence | `f3a4c925a197e63e5b7faf1ce1e1caf5736d76f1b86ba162c6acc85bfff8e7dd` |
| raw-resume progress receipt | `fea89067d065178b1fc61eb06ce98cada2c6bde21db46e8f0695b9abb085591c` |
| `tests/runtime_resume.rs` | `449c3ce11ef04fa60a49517c2fc8a7994d1547cb2dee058d6fdcbd0b095f8580` |
| `runtime/program.rs` | `c2363ad42104b895519bb29a8eb9aeda545bd0176cebbd78750d3a2df90849ca` |
| `runtime/machine.rs` | `fa8dab7f7146f528ad354f336cdfe6e41a728505f9c3dd80c6df64e843dc5b46` |
| `runtime/continuation.rs` | `194e925c2e19816e05e8d0cdf773123f205dce47d36d83a70385daa07a77e2b3` |
| `runtime/receiving.rs` | `8c81deadc48c4770f25760e9086d2053815785ff16cfd5580fa814fb83af9bd9` |
| HIR `module.rs` | `153a23ecaa68fd150d8bd0cc0316f3723e1cb5d98a6e3026aadef2bfd08fd907` |
| HIR `module/local_source.rs` | `3014628f861840ca8e716b3baf8e6a3c9dd736b1bad318b32e7a7b195ddf8786` |
| HIR `source_identity.rs` | `7f0ba057a28ec8c42d2b08bcbe698ee9b422819bfde8ea43ce184457ea586bb3` |
| solver `candidate_source.rs` | `66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c` |
| playground `main.rs` | `75b38435f4634ee35b3e14a54fb4d021b78bda834b4fd53965302a73309e0100` |
| playground `lib.rs` | `bdf996d0264e252e345c05bc77b2adcf625120281244171f0054f1d87a8d1e1b` |

Paths abbreviated in the table are under the exact contract's crate/tool paths.
All contract pins, including unused output/test/Cargo inventory, were SHA-256
checked and matched. Unused file bodies are not implied proof dependencies.
Historical theorem authors are identified only by their documents' assigned
prover-leaf attribution; concrete contributor identities remain UNKNOWN here.
The progress/contract owner is Luna; source/charter/test byte authors UNKNOWN.
Present derivation author is `/root/r118_proof_lane` and cannot certify it.

Requested model/effort Sol/high; concrete version and observed model/effort
UNKNOWN/UNKNOWN. First explicit clock `2026-10-19 09:29:55 UTC`; pre-clock work
remains charged. Cap 420 sec, unexpanded; CPU/memory and exact allocation-start
duration UNKNOWN. Final resource receipt is in the handoff. Static source/text
inspection and SHA-256 only; no code/test/build/CLI/probe/Git/question writes,
external contact or descendants. Exactly this note and the assigned inbox are
new; no scratch/generated paths. **Freeze revision 1, then STOP.** Luna owns
fresh review, command admission, central state and any further lease.
