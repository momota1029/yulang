# R97: finite ordinary parameter entry correspondence

Status: candidate source/native correspondence and conditional runtime derivation;
unreviewed, with public preparation and execution UNOBSERVED. Author:
`/root/r97_proof`, assignment `R97-PROOF`, revision 1. Governing contract:
`tasks/agent-loop/sprints/value-computation-entry-20261019-r97.md`, revision 1,
SHA-256 `2a9e65fd973e4d9c7f0916440fe8438eb6e9a8b8cd7969dc8f89025d9cf1b1ce`.
The pre-edit independent spec receipt is CLEAN only for that contract and
baseline; it does not review this proof or certify the forthcoming test.

## Parent and finite domain

Charter §17 requires whole inert argument introduction, followed by entry in
the same receiver activation. Charter §21 fixes `x` and `x:int` as Value and
`x:[] int` as Computation regardless of body usage or solved effect support.
This packet traces that rule through six exact ordinary-call candidate sources.
It contributes only an ordinary-entry premise for later method/role work when
the authentic executable binder and annotation are preserved. It establishes
no method typing, method-member production, lookup, dispatch, role-call
compatibility, full §21 theorem, divergence, effects soundness, original
Simple-sub A/B theorem, R85 adoption or production authority. Independent
parent quantifiers, including foreign-continuation obligations, are unchanged.

The implementation author's fixed fixture recipe is the literal prefix
`act signal:\n    our ping: () -> int\n`, followed by one body below; `\n`
denotes a newline. Each row is a separate source/module and machine.

| Cell | Exact body following the prefix | Role | Candidate prediction |
| --- | --- | --- | --- |
| V0-ping | `my ignore x = 9\nmy main = ignore (signal::ping())` | Value | Unhandled ping, Unit payload |
| V0-loop | `my loop x = loop x\nmy ignore x = 9\nmy main = ignore (loop ())` | Value | ResourceExhausted at fuel 10,000 |
| VI-ping | `my ignore (x:int) = 9\nmy main = ignore (signal::ping())` | Value | Unhandled ping, Unit payload |
| VI-loop | `my loop x = loop x\nmy ignore (x:int) = 9\nmy main = ignore (loop ())` | Value | ResourceExhausted at fuel 10,000 |
| C-loop | `my loop x = loop x\nmy ignore (x:[] int) = 9\nmy main = ignore (loop ())` | Computation | Completed Integer 9 |
| C-ping | `my ignore (x:[] int) = 9\nmy main = ignore (signal::ping())` | Computation | Completed Integer 9 **if preparation accepts** |

These are predictions, not recorded outcomes or new language typing rules.
In particular C-ping is an intentional source-compatibility falsifier. An
unsupported source, CandidateError or candidate conflict fails the contracted
matrix, even if it prevents runtime entry altogether. It must not be replaced
by an effect annotation or a fabricated runtime transition.

## Authentic source constructors

`parse_file`, `scan_header`, and `SyntaxEnvironment::empty` in the existing
`runtime_control.rs:16–40` helper own public parsing and preparation.
`full_parse.rs:317–340` enters ordinary root parsing. Binding inline bodies
use `declaration/binding.rs:328–360`; all displayed definitions are distinct
column-zero binding statements. The pattern parser's colon branch
(`pattern/mod.rs:1173–1194`) retains PatternTypeAnnotation; the type parser
constructs BracketRow (`type_expr/mod.rs:1608`) for the explicit empty row.
These constructor cases identify the paths; they are not observed parses of
the six whole inputs.

`module.rs:3005–3068`'s `plain_binding_header` retains the original identifier
and annotation from the parenthesized parameter pattern. Top-level formal
formation (`module.rs:2100–2138`) mints `HirParameterId(definition_root,ordinal)`
and records its original source node. `local_source::form`
(`module/local_source.rs:596–628`) copies that exact ID, source key, scope and
annotation into LocalSourceParameter and Lambda, and publishes
`x -> Parameter(the_same_ID)` while constructing the original body. For the
loop source, loop's formal and ignore's formal belong to different definition
roots despite sharing spelling `x`; they cannot be substituted for each other.

`source_annotation::parse_annotation_with_marker` (`:359–389`) records the
annotation's owner and original SourceNodeKey. `parse_type_source`
(`:408–440`) maps `int` to Int with `effects=None`, and `[] int` to Int with
`effects=Some(empty_row)`. The empty row is present syntax; emptiness does
not erase its outer computation marker. The unannotated formal has
`annotation=None`.

The original body 9 becomes Integer. In the final calls, LocalSource's
OperatorChain constructor (`local_source.rs:870–954`) retains the original
Apply callee and entire argument child. Parentheses become Group; empty
parentheses become Unit (`:1056–1090`). Thus `signal::ping()` retains an
operation Apply to Unit inside the outer Group, and `loop ()` retains its
Apply to Unit. Name resolution (`:1004–1044`) prefers the lexical formal;
otherwise the unique module definition is retained. The recursive loop body
therefore resolves its callee to ModuleDef(loop) and its argument to loop's
own formal. `source_annotation::declarations` and `resolve_operation` retain
the declaration-owned ping identity and its `() -> int` signature. No body
occurrence of ignore's unused formal is fabricated.

## Candidate generation and independent runtime formation

CandidateInference::solve uses `solve_mode(false,false)` and the actual
LocalSource preflight, constraint collection, InferenceSession creation and
`run_candidate` (`shadow_apply.rs:270–281,385–430`). The helper requires both
solve success and no candidate conflicts before RuntimeProgram construction.
Neither follows merely from the local constructor trace.

`candidate_source.rs:868–883` registers the exact retained formal ID and Lambda
with role Computation iff its annotation has outer `ty.effects.is_some()`;
otherwise Value. Its traversal visits both Apply children, registers omitted
formals for unannotated Lambdas, emits FormalAnnotation for both annotations
and FormalEntry only for the explicit computation annotation
(`:973–1044`). Formal name effects are associated with their actual formal
registration (`:1220–1257`); ignore's body 9 supplies no such name demand.
`Action::FormalAnnotation`/`FormalEntry` dispatch to the real consumers
(`:1661–1662`). `candidate_effect.rs:1449–1462` consumes the outer row at
entry; `:1464–1515` forms annotation endpoint pairs and admits links to the
actual parameter endpoints. Its concrete-row comment says handling permission
is not a closed upper bound on the supplied computation. This source fact
does **not** establish C-ping acceptance, solve success, native inference
correspondence, principality, or general effects compatibility. No constraints,
propagation, levels, extrusion, qualifying intrusion or generalization are
changed or bypassed by this packet.

Independently, `RuntimeProgram::from_hir` reads authentic retained LocalSource
and validates its indices (`program.rs:277–330`). Its role/name tables and
Lambda instruction (`:414–566`) use the same outer-presence predicate and exact
formal ID. Value formals' names Observe; Computation formals' names Execute.
The role does not come from CandidateInference's solved row or body usage.
RootCompSchema::from_parameter (`receiving.rs:21–43`) additionally requires
the annotation owner and formal source root to match the Lambda source root,
an outer row and ground primitive endpoint. Hence only the `[] int` ignore
formal has that schema in this matrix; the unannotated loop formal is Value.
The schema retains the entire original formal and Lambda SourceSite. This is
a separate receiving certificate, not a substitute for candidate typing.
The source fetch classifier (`program.rs:570–600`) classifies Lambda roots as
values, so loop and ignore are not scheduled for body execution merely by
their definitions. main's Apply is a scheduled computation; execution_roots
returns that source schedule (`:246–247`). Fetching a global closure can
materialize/cache the Lambda, while executing an argument Delay is not cached.
Thus defining loop does not itself invalidate the C-loop prediction.

## Finite entry derivation against actual machine branches

Assume public preparation/start succeeds for a row, identities/resources remain
available, and the frozen machine executes the inspected instructions. This
derivation concerns actual constructors/consumers, rather than a separate model
whose transitions assume the desired answer.

1. Evaluating ignore's Lambda stores its exact formal, role, schema, body and
   lexical environment in ExecutableValue::Closure (`machine.rs:630–644`).
   Apply evaluates its callee and saves the entire argument label and caller
   environment in Frame::Callee (`:645–656`). It never evaluates that argument
   while obtaining the callee.
2. Frame::Callee (`:879–902`) allocates one inert Delay with that entire label
   and lexical environment; `receiving.delay` records its view. No ping,
   loop application, Unit payload or source-derived argument prefix executes
   here. `direct_formal_root` only inspects a direct formal reference; neither
   displayed grouped argument is a direct formal reference. This construction
   captures lexical references, not a store/handler snapshot.
3. For the authentic closure, `new_invocation` (`:1248–1267`) creates activation
   a with its actual call/provider SourceSites, marks it active and sets
   current_owner=Invocation(a). ReceiverReturn is installed before the role
   branch (`:917–969`). Thus both entry branches happen after the receiver
   exists. Provider/call identities are retained, not collapsed into a formal
   spelling or an equal solved type.
4. Value (`:969–979`) installs Frame::ValueEntry carrying the original formal,
   closure body and lexical environment, then executes Delay. Delay execution
   (`:1929–1934`) only changes code/environment; it preserves Invocation(a).
   If the argument returns, ValueEntry (`:1081–1099`) binds its returned value
   to that same formal with Value interface and then evaluates body 9. It
   performs no recursive force of returned latent data. ReceiverReturn later
   retires that invocation (`:1070–1080`). Nested argument calls may have their
   own invocations; they do not move ignore's entry before a.
5. Computation (`:980–1009`) enters the schema under a, retaining the inherited
   delay view, authentic schema and original formal entry receipt
   (`receiving.rs:123–175`), then binds the Delay itself to that formal with
   Computation interface and starts body 9. The branch calls no execute on
   Delay. Integer 9 contains no formal read, Force, handler or other consumer;
   returning it therefore does not execute the argument.

The same branches account for all six roles. For either Value-ping row,
executing the whole argument obtains ping and constructs its Unit argument
inertly. Ping's declared Unit payload has Value role; its own invocation
executes that payload before `make_request_carrier`, then the operation result
consumer executes the request (`:1011–1069,1935–1956`). No Catch is present.
Request propagation stores the suspended suffix and produces UnhandledRequest
with the declaration-owned operation ID and Unit payload (`:1762–1778`).
The body 9 cannot run through a pending ValueEntry until the argument returns.
This explains the predicted outward request; authentic ID/payload/range and
continuation observations remain run obligations.

For the Value-loop rows, entry reaches the recursive ModuleDef(loop) closure
and its Value formal; successive applications reenter that body, rather than
reaching ignore's 9 on the inspected path. `Machine::run(10_000)` reports
ResourceExhausted if no stop occurs during that finite budget (`:482–492`).
This packet predicts that finite result and does not prove infinite divergence
or universal nontermination. For both Computation rows, the argument body is
unconsumed on the inspected entry path, so the conditional prediction is 9.
C-ping's preparation compatibility remains a separate premise even though
its conditional runtime branch retains the request unevaluated.

## Application, missing seams and falsifiers

The finite source-to-role and instruction-to-entry trace supplies a candidate
ordinary-entry premise for the original method/role parent: **if** a future
method construction retains this authentic executable binder, annotation,
whole-argument label and same receiver invocation, these entry branches apply.
R95's bounded field/role source identity evidence does not establish those
method consumers; this note creates no method/role theorem and closes no R85
or A/B gate. The first missing evidence for R97 itself remains all six exact
public preparation and bounded runtime outcomes, owned by Luna's one command.

Before that command every row has these UNOBSERVED seams: whole parse and
diagnostics; lower_module_with_local_source completion and retained IDs/forms;
CandidateInference preflight/collection/solve and absence of conflicts;
RuntimeProgram::from_hir/default evidence construction; definition selection,
execution_roots and start; the complete 10,000-step outcome and associated
request/result assertions. No measured internal trace establishes allocation
or same-invocation order for these executions; that part is a source-branch
derivation subject to independent review. A passing outcome test alone would
not independently prove every internal scheduling assertion.

`R97-ENTRY-RUN-1`: Luna owns one exact contracted six-cell command after source/
proof freeze and CLEAN spec delta. Any parser/preparation failure, conflict,
flipped role, eager execution, wrong/missing request, wrong result, unexpected
exhaustion/completion or dependency drift stops R97 without repair/retry.
The implementation author owns only the new matrix test and its freeze. No
minimal production implementation TODO is warranted: the inspected owners
already implement both entry branches; first obtain the authorized evidence.
`R97-METHOD-BINDER-1`: Luna retains the later parent obligation to exhibit an
authentic method executable binder and consumer preserving this entry path;
its falsifier is a lost/replaced formal or annotation, absent executable binder,
or dispatch outside that preserved receiver. That extension requires a separate
lease; no new code or proof packet is authorized here.

Prior evidence reused: existing `runtime.rs:96–112` fixtures identify Value
recursive-entry and unused/consumed Computation cases on their actual sources;
they are source precedent, not newly rerun R97 evidence. R96's finite receiver
ownership trace is reusable only for the same machine owner branches; its
wrong/sibling-permission outcomes do not prove these six inputs. R95 establishes
only its bounded method/role constructor prerequisite. R92's stdout 23 does
not establish any R97 cell. No historical conditional result or green test is
promoted into original parent closure.

## Dependency freeze and provenance

All hashes below were read from actual bytes. Contract pins match. The paired
test's contract baseline is `8fae651ed7d14f4ed25c2aaa7d1d5fd3ba40940414a1995a42ddfcb5fe6d4815`;
the implementation writer supplied an explicit write-stop receipt, and the
following changed test/handoff hashes and exact six fixtures were then read
from its frozen bytes. This adds no implementation coauthorship or review.

```text
2619e4c8bb006e2d98cf81887091ae372cb1ae3731de76e7b707a97db577009c tools/inference-playground/tests/runtime_control.rs
247e66658fbf616046e4e41442f85e280213e23af508aa17f82db0e9acfbe4f3 tasks/agent-loop/inbox/20261019-r97-implementation.md
dcabcae901f0220673da1dc7e93216988c8c5612755220e2e19e6686eebaf39a tasks/agent-loop/inbox/20261019-r97-spec-review.md
547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed notes/design/2026-09-29-scc-intrusion-redesign-charter.md
66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c crates/yu-solver/src/candidate_source.rs
6112343b4014c67dcb7d814a46412b3af3e1d12183924e891df4817a59f58da0 crates/yu-solver/src/candidate_effect.rs
5bbcf27d51906814ba38b2cca2066807d285d0b1817f0ea6e04d70c4a5c8a5cb crates/yu-solver/src/shadow_apply.rs
9f7a80055076a01cbd99a3eb9c5bc8c3f0db512f2e84032a53af0eacdad2375b crates/yu-hir/src/shadow.rs
3014628f861840ca8e716b3baf8e6a3c9dd736b1bad318b32e7a7b195ddf8786 crates/yu-hir/src/module/local_source.rs
8f6e2b688418dbdb4e2c551cbd9b7b58c809623d492f2da6f7d29cc64189d8d8 crates/yu-hir/src/lib.rs
c40ebde1755d300c83aafba0a81a85d19ed5200dfc2163ab72c8a3bb08baf29a crates/yu-hir/src/module.rs
b8462b66eac24a48b6fc5e931a3d8b7c38c19bb8b2f1a7cdc4ecd9a8a7a1117f crates/yu-hir/src/module/source_annotation.rs
8c81deadc48c4770f25760e9086d2053815785ff16cfd5580fa814fb83af9bd9 tools/inference-playground/src/runtime/receiving.rs
484967c20c829344a8abe3aa583f6a65e715fb927b8d6b0ba816f0cc6291ad11 tools/inference-playground/src/runtime/program.rs
fa8dab7f7146f528ad354f336cdfe6e41a728505f9c3dd80c6df64e843dc5b46 tools/inference-playground/src/runtime/machine.rs
24fdbc0f792b748138bcb1b6fded72714dba7f02880f0d395c914fcff546a8d8 crates/yu-syntax/src/full_parse.rs
eb9b7c9b97b999d16b364531fdcfad0bfc0cb377855e86ce6d5b825f5aba3544 crates/yu-syntax/src/declaration/binding.rs
81db2aec4774f2cd1ddc12b64fd9206cf41cdf3eee00ed740676ffc6d7fc5669 crates/yu-syntax/src/expression/operator_chain.rs
1b608422c93ce0f6947125a9b1ea88314a48b3a5e45030ed23e5154492ad7883 crates/yu-syntax/src/pattern/mod.rs
2e08a49960cd4010ba39641ae509afb7cf59711c1464d3349f5f6db590ebf01f crates/yu-syntax/src/type_expr/mod.rs
8ccf273de0d475b999207f216822f35354cdee51a2b00aba3a8be5bafd2bc16e crates/yu-syntax/src/type_expr/variants.rs
f8bebfd4eb4571e2814b83ea8473c035b429fe1eed4e07d26942a096143306ec tools/inference-playground/tests/runtime.rs
f106525812de5a2788b465dfffb4d8a386883aa8d90b631616ea4bdcb5dd9533 notes/progress/2026-10-19-r96-sibling-receiver-permission.md
dfdf5272569db6c41e5b19f817b0f1cb39b35dac185fa2459edc7844d4b8cdf1 notes/progress/2026-10-19-r95-final-source-correspondence-verification.md
```

Requested model/effort: gpt-6.1-sol/high. Observed model/effort: UNKNOWN/UNKNOWN;
no runtime metadata establishes an effective model or effort. Session:
`current-conversation-2026-10-19-r97-value-computation-entry`. Sole note author
`/root/r97_proof`; no descendants/coauthors. Paired fixture author
`/root/r97_implementation` supplied its literal recipe independently; the
pre-edit spec reviewer is a separate read-only author, receipt preserved by
Luna. Historical source authors remain as recorded in their original artifacts;
this note does not claim their authorship or independently certify them.

Resources: proof allocation 600 seconds, Astra 0, no renewal. Actual aggregate
wall-time measurement is UNKNOWN; no budget expansion claimed. Work comprised
source reads, hash reads and the two leased artifact writes. No builds, tests,
compiler CLI, Git, source edits, external contact, scratch files or descendants.
The assignment ends on freezing its note and exact handoff; independent review
and Luna's command remain pending. Writer stops after the handoff hash receipt.
