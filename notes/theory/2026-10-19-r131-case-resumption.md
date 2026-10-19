# R131 — saved Case frame across shallow resumption

Revision 1; candidate conditional source/runtime derivation, NOT independently
reviewed. Author `/root/r131_proof`; no coauthors or descendants. Frozen parent
contract: `tasks/agent-loop/sprints/case-resumption-20261019-r131-rev3.md`,
SHA-256 `3e52328feb18886d81dc14237b5fdaaf7138eefb794dc67c54e866c91ab1dba2`.
Baseline supplied by Luna: `53c313c7b32aa3d7f4f49aacb3b447f9c53ae908`.
Luna's direct assignment grants exactly this artifact and
`tasks/agent-loop/inbox/20261019-r131-proof.md`, 450 seconds, no checks or code edits.

## Parent and precise result

The R131 parent is the finite experimental source/runtime route for these exact
two sources, under successful source formation, candidate inference acceptance,
runtime-program formation, authentic receiver evidence, compatible continuation
response and sufficient execution/identity/allocation resources:

```yu
act io:
    our tick: int -> int
    our other: int -> int
my relay (thunk:[io] int) = catch thunk { io::tick(value), k -> k 9 }
my main = relay { case io::tick 0: 9 -> 91, _ -> 17 }
```

```yu
act io:
    our tick: int -> int
my relay (thunk:[io] int) = catch thunk { io::tick(value), k -> k 9 }
my main = relay { case io::tick 0: 9 -> io::tick 8, _ -> 17 }
```

The derived result is that the positive returns integer 91 and the negative
reaches `RuntimeOutcome::UnhandledRequest` for the second tick, without a
completed result. The Case frame retains its lexical environment and receives
the handler's response value and its associated view. The selected handler is
absent during selected Case-arm execution. This is direct reasoning about the
pinned source machine, not an executed observation or native-backend theorem.

The derivation applies the capture lemma below to the actual two-frame suffix;
it does not merely assume that a generic continuation contains a Case frame.
Public CLI/WASM acceptance and results remain executable evidence owed by Luna,
and independent review remains required. No original Simple-sub/evaluator A/B,
H/A/E/B, six hygiene parents, R85 adoption, method M/T/A, R128 or R129 gate
closes. Their quantifiers/source domains remain unchanged. In particular, this
local sequence proves neither F1 nor FK1 for foreign continuations.

## Authority, retained source and constraints

`rules/design-authority.md` and the Authoritative 2026-10-11 inference principles
preserve generation, accumulation, propagation, levels, extrusion, qualifying
intrusion and generalization. No bypass or inference restriction is proposed.
The 2026-10-16 decision and goal-driven-sprints rule govern scheduling only;
the R131 rev3 contract and explicit Luna grant define this experimental lease.

Only contracted code owners supply the derivation. Successful HIR formation is
an explicit premise, not a proved parser/lowering completeness claim. At
`program.rs:435`, annotations with effect rows produce Execute consumption for
formal Names. At `:516`, the retained annotated Lambda produces
`ParameterRole::Computation`; `RootCompSchema::from_parameter` in
`receiving.rs:22` checks source-root identity, effect-row presence and primitive
result type. `[io] int` fits these tests. `program.rs:559` preserves Case
scrutinee/body labels and source arm order, canonicalizes integer-pattern text,
and retains Wildcard. `:584` preserves the resolved catch operation pattern and
body. Group/Ascription forwarding at `:511` introduces no runtime frame.

The current `candidate_source.rs::emit_candidate_source` Visit(Case), at `:987`,
schedules scrutinee Visit before CaseArms; CaseArms at `:1107` alone schedules
arm patterns/bodies. Finish(Case), at `:1203`, retains the scrutinee effect
bound to the Case effect (slot 51), integer pattern value bound to scrutinee
value (52), scrutinee endpoint bound to int-negative (53), every arm body
endpoint bound to Case value (50), and every arm body effect bound to Case
effect (51). Thus the negative's second tick remains an actual arm effect;
the unused wildcard arm is also inferred. No evaluation/constant folding is
used to remove constraints. FormalEntry/FormalAnnotation construction at
`:1022` and CatchOperation at `:1101` preserve the annotated receiver and
continuation constraints. `initialize_candidate_source_levels` at `:1585`
initializes retained levels and the computation formal's native root/entry
effect. This is owner correspondence, not a proof that every downstream
propagation, extrusion, intrusion or generalization succeeds for these inputs.

`lib.rs::prepare` at `:266` owns the first remaining executable premise: parse,
retained lowering, candidate solve and empty candidate-conflict result. Its
solver implementation and parser are outside this contract's pinned owner set;
they are not imported as new proof dependencies. `execute` at `:167` calls
prepare, then `RuntimeProgram::from_hir`, default RuntimeEvidence, and the source
schedule. Conditional runtime reasoning therefore does not claim unconditional
source acceptance. The precise public probes distinguish that missing premise.

## Values, environments, views and owners

Write R for the relay invocation owner, T for the first native tick invocation,
and K for the invocation of continuation k; these are distinct fresh ordinals,
not source names or handler occurrences. M is `ModuleRun`. Let E be the lexical
environment of main's delayed argument, H the relay closure environment extended
with thunk, and H' the handler environment extended with payload and k. E is
the environment retained by Case; it is not replaced by H'. In these exact
sources E has no local Case binder; preserving E is a structural fact, not a
behavioral stress test of free-variable lookup.

Write d for the delayed argument value, vR for its RootComp view, rR for the
authentic read receipt of thunk, xR for its execution occurrence, and g9 for
the ground view associated with the newly evaluated response integer 9. These
are different objects. The request's payload 0 and its view are retained for
payload matching/binding, never substituted for the continuation response 9.
The captured template retains request declaration and original event lineage,
not a snapshot of the whole active store or an event to replay.

## Event and source-owner trace

Stacks below run bottom to top. P is the module/root prefix and RR(R) the
relay ReceiverReturn. Root cache/GlobalRead frames are outside the selected
handler; none is inside the captured suffix. There are no local initializers
inside either exact argument block.

| Stage | Transition and owner | Retained or removed data |
| --- | --- | --- |
| Receiver entry | `machine.rs::return_value(Frame::Callee)`, `:891–1028`: allocate inert Delay(argument,E), mint R; computation entry calls Receiving::enter and binds thunk | d, vR, genuine R entry receipt; body runs in H; RR(R) remains below body |
| Install catch | `evaluate(Instruction::Catch)`, `:739`: install fresh CatchReturn(h,H,installation owned by R) | selected handler occurrence h is real and live |
| Execute thunk | `consume`, `:1903`: validate view/value, issue read receipt rR owned by R, push RootCompReturn(xR), execute d | xR=(vR,rR,fresh execution occurrence); enter argument code in E |
| Interrupt Case | `evaluate(Instruction::Case)`, `:697`: push Case(case,E); evaluate tick 0 | stack P,RR(R),CatchReturn(h),RootCompReturn(xR),Case(case,E) |
| Native tick entry/return | Callee operation branch, `:1035–1097`: mint T, evaluate primitive payload 0, construct request carrier; ReceiverReturn(T) leaves T; OperationResultConsumer executes carrier | T ends before request generation; current owner returns to R; payload and carrier are distinct |
| First event | `execute`, `:1974`: mint event e0, observe executing_views=[xR], create empty suffix | event declaration is resolved io::tick, payload is 0, source is first tick Apply |
| Propagate | `propagate_request`, `:1577–1806`: pop Case into Ordinary(Case,E); pop RootCompReturn, end xR, save it | suffix in pop order is [Case(case,E),RootCompReturn(xR)]; current owner stays R |
| Select handler | inspect live top CatchReturn before removing it; signature and payload primitive checks plus local grant succeed | capture suffix; pop selected h; bind payload and continuation into H'; selected h is excluded from suffix/template |
| Apply k 9 | continuation Callee branch `:909`: mint K, push RR(K), ResumeArgument; evaluate delayed integer argument 9 | 9 is a fresh Value with ground view g9; H' determines only this handler expression |
| Validate/enter | ResumeArgument `:787–840`: declaration result is Int; primitive_matches validates Value/interface/view; push ResumeReturn; enter fresh per-use control map | exact ReceivedValue(value9,Value,g9) passes inward unchanged |
| Restore | `enter_template`, `:1441–1518`: borrow live owner R from K, restore view execution and Case | stack P,RR(R),RR(K),ResumeReturn,OwnerReturn(R,false,previous=K),RootCompReturn(xR'),Case(case,E) |
| Return to Case | Hole returns response; `return_value(Frame::Case)`, `:1232`: find first matching arm in source order | pattern 9 equals canonical integer 9; wildcard is later; selected body uses E; h is absent |
| Positive | evaluate 91; RootCompReturn ends xR', grounds final value; borrowed OwnerReturn restores K; ResumeReturn passes through; RR(K) leaves K for R; RR(R) leaves R for M | 91 is cached/published only by its ordinary root return; original g9 is not the final 91 view |
| Negative | selected body evaluates tick 8, with a new native owner that returns to R before the request carrier is executed | new event e1 is distinct from e0 and has source second tick Apply and payload 8; there is no h to select |

The receiver grant is source-derived rather than assumed from the operation
name. `receiving.rs::enter`, `:131`, adds a boundary owned by R and its schema
to vR's image. `consume` creates the exact R/vR read receipt. `observe`, `:210`,
authenticates xR for e0. `local_grant`, `:234–327`, checks R still active,
the formal's row contains the request's exact family ID, an authentic e0
observation, an R receipt of that same view, and image reachability to R's
boundary. Here the view's first boundary is R itself. These checks succeed
under authentic formation, independently of whether the alternative
closed_primitive certificate happens to be enabled. Unknown inherited coverage
does not become a negative certificate or a new grant.

The handler checks at `machine.rs:1620–1676` compare exact operation declaration
IDs, require the admitted signature shape, one compatible primitive payload,
and primitive continuation response. `int -> int`, payload0 and binder k fit.
Capture happens before the selected handler is popped; the handler is not yet
in request.suffix. No handler is abandoned and later restored under another ID.

## Finite suffix induction and application

Let S=(s0,...,s(n-1)) be the finite saved-frame sequence in request pop order,
with every capture/entry guard successful. Define C0=Hole. For each si,
`capture_template` appends Ci+1 wrapping Ci: an ordinary admitted frame yields
Bind(Ci,clone(frame)); a RootCompReturn yields View(Ci,execution); receiver or
ambient boundaries yield Owner(Ci,owner); a forwarded handler yields
ForwardHandler(Ci,handler,environment,owner). GlobalRead and Root are rejected;
ResumeArgument handles are validated. Finally Owner(Cn,containing) is added.

Induction on i proves that Ci contains each processed suffix element once in
its original order, with its exact ordinary environment/code handles, and
contains no selected handler boundary absent from that suffix. Base i=0 is
Hole. The induction step makes one wrapper owning exactly the prior root,
copies/retains the si payload, and adds no sibling/context snapshot. Since the
selected handler was inspected as the next live frame after the suffix had
been popped, it is absent from every si. The final containing Owner wrapper
adds executable attribution, not a handler.

For entry, induction from Ci+1 to Ci shows the wrapper pushes the appropriate
frame before entering its inner node. Bind pushes the cloned ordinary frame;
View authenticates its original view/receipt and creates a fresh execution
occurrence; Owner resolves the per-use map, borrows a live owner or creates a
fresh invocation from its descriptor, and pushes the matching OwnerReturn;
ForwardHandler validates the resolved active owner and installs a fresh
occurrence. This establishes entry/stack structure under its stated guards,
not a general theorem that arbitrary saved frame actions preserve responses.
Hole returns exactly the supplied ReceivedValue. Entry visits the outer saved
frame first and the innermost last, so the first subsequent pop is s0's frame.
Owned/borrowed owner brackets and view execution brackets are balanced by their
actual return consumers. Forwarded handler cases remain guarded by actual
owner/control evidence; they do not supply an independent foreign-continuation
theorem.

For the exact R131 route n=2 and S=[Case(case,E),RootCompReturn(xR)]. The concrete
arena is Hole(0), Bind(inner=0,Case(case,E))(1), View(inner=1,xR)(2),
Owner(inner=2,R)(3). R has not unwound: RR(R) is below selected h. K is active
when entry starts, so Owner borrows R (`owned=false, previous=K`), with no new R
activation. View entry calls execution(vR,rR), preserving vR/rR but minting
xR' distinct from xR. Bind pushes the exact Case and E. Hole returns 9/g9.
There is no ForwardHandler node. The Case pop compares integer text and selects
body0, proving the positive 91 route and selecting the negative second tick.

Case's integer-pattern branch keeps E and does not store a new binder; the
response value/view are consumed by the comparison. The general Case binder
branch would bind the same received value/view under Value interface, but that
branch is outside the two witnesses. RootCompReturn later grounds its returned
value into a new view; preservation does not mean every view handle stays equal
through every return. The event observations from e0 are not reused for e1.

## Negative endpoint and discriminating falsifier

At e1 the live suffix above P is RR(R),RR(K),ResumeReturn,
OwnerReturn(R,false,previous=K),RootCompReturn(xR'). Case was already popped;
selected h was removed earlier. The second native tick's own ReceiverReturn and
OperationResultConsumer have also already returned/consumed before e1 starts.
Propagation ends xR', then leaves borrowed R without deactivating R, restoring
K. It saves ResumeReturn ordinarily; RR(K) then deactivates K and restores R;
RR(R) deactivates R and restores M. The resulting saved owner boundaries are
lineage only; request propagation does not enter them as templates. The module
prefix has no CatchReturn in either exact source. GlobalRead, if encountered,
stops the unhandled request without crossing the demand barrier; otherwise the
finite prefix is popped until empty. `stop_unhandled_request`, `:1809`, records
e1, operation ID, payload8 and saved continuation and sets UnhandledRequest.
No return reaches root publication for main, so no Completed result is minted.

`lib.rs::execute`, `:180–200`, formats only Completed values and returns Err
containing `unhandled runtime request` for this endpoint. WASM `run` calls the
same execute with scoped=false and maps Err into JsError. Therefore the public
predictions are positive `91\n` and negative error/no completed output,
conditional on the front-end/runtime-formation/resource premises. Browser
rendering and CLI process stdout/stderr are not proved by this machine trace.

If h were reinstalled around the resumed body, e1's same-family, same-operation
tick with primitive payload8 would match it. Restored xR' still gives R/vR
evidence. Its k would receive 9, the selected Case body would return 9, and the
program would complete rather than raise the unhandled endpoint. The paired
negative thus discriminates handler reinstatement. A different operation such
as io::other would not: a tick-only handler would forward it either way.

## Remaining premises, reuse and mutual TODOs

R130's inspected historical proof is reused only for its identified Case
constraint owners/traversal repair context. Its finite Integer/Name/Case/Group
induction excludes this effectful scrutinee and does not prove this route.
The current repaired owner bytes were read directly. The older receiver CLI
regression is reused as an example of actual public plumbing/annotation shape,
not as a grant proof, Case-resumption proof or execution result for R131. R129
is provisional and supplies no proof premise. No historical hygiene lemma is
imported, weakened or re-certified.

TODO R131-SOURCE-RUN-1, owner Luna, parent R131: establish the exact two source
strings survive `lib.rs::prepare` and RuntimeProgram::from_hir, and the serial
contract verification publishes 91 versus second-tick unhandled/no completion
through CLI and WASM. Inputs: rev3 contract and the pinned owners below;
output: the already leased implementation handoff/test/browser evidence.
Falsifier: unsupported source, conflict, unavailable/HandlerEvidence,
ContinuationResponse, resource exhaustion, wrong value/arm, completed negative,
or negative failure preceding second-tick execution. This requests no new code
lease or runtime change. If it fails, return the exact first owning symbol to
Luna before changing semantics or syntax.

TODO R131-FRESH-REVIEW-1, owner Luna: freeze this artifact, implementation and
direct dependencies and assign fresh eligible review. Falsifier: source owner
does not generate the stated stack/suffix, view/receipt authenticity does not
hold, owner bracket order mismatches, selected h reappears, or any result is
claimed outside the conditional finite domain. Producer is ineligible to
certify this packet. No additional worker stage remains inside this lease;
handoff/review is the stop condition.

## Frozen dependencies and runtime receipt

All code hashes below were read from current bytes and match the contracted
pins. Repository baseline identity is supplied by Luna; no Git command ran.

| Direct code/context input | SHA-256 |
| --- | --- |
| crates/yu-solver/src/candidate_source.rs | cbc39315f4243b0bae1db74976cf94282bc94cd28b9eb463699c085f421065f7 |
| tools/inference-playground/src/runtime/program.rs | 28748da0458da92b9d1190b250bbb84bdecc6643718eacbca95a04f5d6c9aa0d |
| tools/inference-playground/src/runtime/machine.rs | 4fb918732047f61184bc8f89b829bde68a8d1e6649a24d02640ec14500ae0acd |
| tools/inference-playground/src/runtime/continuation.rs | 194e925c2e19816e05e8d0cdf773123f205dce47d36d83a70385daa07a77e2b3 |
| tools/inference-playground/src/runtime/receiving.rs | 8c81deadc48c4770f25760e9086d2053815785ff16cfd5580fa814fb83af9bd9 |
| tools/inference-playground/src/lib.rs | bdf996d0264e252e345c05bc77b2adcf625120281244171f0054f1d87a8d1e1b |
| apps/yulang-wasm/src/lib.rs | 2fc9feb353b3130c4efc888270cec14cba8b2bbcc2fca03d3780c676e0468f8a |
| tools/inference-playground/tests/cli_resumed_receiver_permission.rs | 9a5fd48d1f89ae064960554d8ece36d6b9b437ae6cc91504a1e7c035aec9257a |
| notes/theory/2026-10-19-r130-case-source-progress.md | 3157a90ad1ab9d6b826b0a12f0d909e974f17caf2c80061af6e7b67b7ab31b7e |
| tasks/agent-loop/inbox/20261019-r130-proof.md | 69f0516e82b49f2c77472781c3950da7ccf3e21056f8eada6e2a1a129d899f52 |

Authority/protocol hashes: goal-driven-sprints.md
`e50f5d4f79814c87af56e7dc34ddb6ab968abb523826c72ecdc40a8920397c0a`;
agent-loop README `1379059577f4469ed930c0fc130e5cd169401cf9188dfcbbc482b92b43daebbf`;
design-authority.md `e4055100f6e75b9c8a6294ec6c68643d8677d7b35b45e430450f7e2c2ad97eb1`;
2026-10-11 inference principles
`7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`;
2026-10-16 sprint decision
`2dfeb555c913d3142078de535ee4b7f68e9a27f2b91a5f0bb82d4d867db4fc4e`.
R130 artifact/inbox authorship is `/root/r130_proof`, no descendants, per their
own frozen receipt; its review/integration status is Luna-owned context.
Compiler/runtime code authorship is the existing repository provenance, not
this worker; it was not independently established through Git here.

Actual worker `/root/r131_proof`; session
`current-conversation-2026-10-19-r131-case-resumption`; launch evidence is the
direct parent NEW_TASK and this active source-reading/writing turn. Requested
model/effort Sol (`gpt-6.1-sol`)/high; observed model/effort UNKNOWN/UNKNOWN.
The role/config text is not runtime model evidence and was not changed.
Checks/tests/builds/CLI/formatters/Git: NONE. Read-only source inspection and
SHA-256 inventory only. No executable model or scratch file was created.
Budget: 450 seconds granted; exact launch-to-stop duration is not observable in
this leaf's metadata, so charge the full 450-second reservation conservatively;
no refund/renewal requested. No Astra, descendants, external dependencies or
background processes. All new paths are the two exact leased files above.
Writes stop after the paired handoff is finalized; its frozen hash is sent to
Luna. Worker STOPPED at submission, not RUNNING while review waits.
