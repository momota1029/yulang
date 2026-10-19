# R118: finite nested outside-selection trace

Status: **CONDITIONAL CANDIDATE; NOT INDEPENDENTLY REVIEWED**.
Assignment `R118-PROOF`, revision 1. Sole author and writer:
`/root/r118_proof_lane`; no coauthors or descendants.

## Parent, authority and exact scope

The parent is the ordered-handler/outside-selection front identified in
`tasks/agent-loop/sprints/nested-handler-outside-selection-20261019-r118-rev2.md`,
revision 2, baseline `6caae031058b53545e03a205be2ab1bab9179a44`.
The approved semantic direction is charter §§14–15: the selected shallow
handler is exited before selected-arm execution; a new arm request uses its
actual outer context and its own visibility/compatibility checks. Explicit
shallow reapplication derives deep behavior. This does not itself authorize
compiler implementation or prove source soundness.

The contract supplies a finite witness, not a replacement universal theorem.
This packet applies its trace only to that witness within the original parent.
It does not discharge the parent's other installations, matches, guards,
defaults, permission cases, continuations or source forms. F1 and FK1 retain
their independent quantifiers, including foreign continuations. Original
Simple-sub A/B, the original evaluator, all six effect parents, R100-P2,
R85 adoption and R117-JOIN-1 remain OPEN.

The exact contract source is 235 bytes without final LF, specified SHA-256
`b8ad07fdbb59c06fdd46b9417f92acfe05c954faed34a2d0ca88ba500e58e900`:

```yu
act io:
    our tick: int -> int
    our other: int -> int
my inner (thunk:[io] int) = catch thunk { io::other(p), _ -> io::tick 11 }
my outer (thunk:[io] int) = catch thunk { io::tick(p), _ -> p }
my main = outer (inner (io::other 7))
```

Its operation names are distinct. Each catch has one operation arm. No
duplicate-arm tie-break or general handler-priority rule is assumed.

## Conditional claim and premises

For these source bytes, if the following source/runtime transitions succeed,
the pinned machine follows the finite trace below and completes with integer
`11`; the pinned public caller then succeeds with stdout `11\n` and empty
stderr. No CLI execution or actual HIR dump was performed by this author.

1. **H — authentic construction/admission.** `prepare` parses and lowers these
   bytes into the expected authentic LocalSource forms, resolves the operation
   uses and patterns to the same declaration identities described below, and
   ordinary `CandidateInference::solve` succeeds without candidate conflicts.
   The names `inner`, `outer`, `thunk`, and `p` resolve to their own definitions
   or binders. No replacement HIR or hand-written transition fixture is used.
2. **E — successful runtime evidence.** Program construction/start, receiving
   views, primitive payload compatibility, handler-installation validation,
   owner transitions, and both ordered candidate checks succeed. At each match
   the actual predicate is `program.closed_primitive || receiving.local_grant`
   with that request's observations/event, installation owner, invocation
   state and declared family. Same family spelling alone is insufficient.
   No value for `closed_primitive` is assumed here.
3. **B — successful bounded completion.** Identity/resource checks do not fail,
   the trace completes within the caller's 10,000 transition budget, and public
   input/output operations succeed. This packet supplies no measured step count.

H, E and B are explicit remaining premises, not inferred from a conditional
trace. Their exact owners and falsifiers appear below. The source inspections
establish the transition implications and identity-preserving consumers;
they do not establish that the authentic source constructors emit every premise.

## Source identities and the same-HIR join

Use symbolic identities rather than fabricated concrete IDs or source ranges:

| Symbol | Authentic owner required by H | Pinned consumer |
| --- | --- | --- |
| `d_other` | `io` declaration's `other` operation | `Instruction::Operation(Resolved(declaration))`, then `PendingRequest.declaration.id` |
| `d_tick` | `io` declaration's `tick` operation | The corresponding operation instruction and request declaration |
| `h_i`, `a_i` | Inner catch expression and its sole `other` arm | `Instruction::Catch`, stored `CatchArm.pattern/body/source/range` |
| `h_o`, `a_o` | Outer catch expression and its sole `tick` arm | The analogous outer catch and arm |
| `p_i`, `p_o` | Distinct inner and outer payload binders | `Binder::Catch(binder.id.clone())`; outer `p` resolves to `p_o` |
| `A_i`, `A_o` | Runtime invocations of `inner` and `outer` | `new_invocation`, `ReceiverReturn`, `HandlerInstallation.owner` |

The required equalities are: the main `io::other` use and inner arm pattern
both resolve to `d_other`; the inner-arm `io::tick` use and outer pattern both
resolve to `d_tick`; `d_other != d_tick`. These are HIR identity equalities,
not assertions proved merely by the common `io` spelling.

`lib.rs::execute` (167–204) calls `prepare` once and gives its returned
`Arc<HirModule>` directly to `RuntimeProgram::from_hir` with default evidence.
`prepare` (266–344) constructs that Arc through
`lower_module_with_local_source`, passes `hir.clone()` to the selected solver,
checks conflicts, and returns `(hir, candidate)`. With the exact public flags,
`scoped` is false, so it selects ordinary `CandidateInference::solve`.
There is no reparse, second lowering, or alternate candidate-to-runtime HIR.
The special operation-v1 research entrypoint is not this path.

`program.rs::from_hir` (248 onward) reads each retained LocalSource root,
validates expression indices, and builds labels in that root's code interval.
It clones operation resolution into `Instruction::Operation`; clones each arm's
pattern/source/range and resolves its body label; and retains each expression's
source root, occurrence and range in `Code.site` (536–564). Definition IDs are
retained in `definition_indices` (570 onward). These are inspected consumer
facts conditional on H. Exact byte-range provenance is not derived from source
text shape, especially in view of R109's failed range assertion.

The two own `[io] int` annotations cause `from_hir` to assign computation role
to those lambda parameters and `NameConsumption::Execute` to their parameter
uses (426–503). It requests each `RootCompSchema::from_parameter`; this packet
does not independently establish that constructor's positive result or its
Grant consequences. Outer `p` is a catch binder and receives Observe consumption.

## Finite runtime derivation

Stacks below run from bottom to top. `R` denotes main's source-schedule Root
publication frame. `RR_o/RR_i` are actual `ReceiverReturn` frames; `C_o/C_i`
are the actual `CatchReturn` installations; `V_o/V_i` denote the corresponding
`RootCompReturn` frames when the receiving roots are present. If a receiving
root is absent, omit that view frame; the candidate checks still require E.
These abbreviations retain separate owners and do not identify roots, providers,
views, requests or installations with one another.

1. **Entry.** `program.rs` preserves source order and classifies the Apply body
   of main as a computation root (570–610). Lambda definitions materialize on
   demand as closures. `machine.rs::begin_root` (1807–1857) starts main under
   ModuleRun with `R`; its `Frame::Root` later publishes only main's completed
   value. A closure's own initialization finishes before its caller's delayed
   argument runs, so the requests below are not trapped behind a pending
   `GlobalRead` for `inner` or `outer`.
2. **Install outer before running its argument.** Apply evaluates its callee
   first (641 onward). `Frame::Callee` allocates the argument as inert Delay;
   computation-role closure entry binds that Delay and enters the body without
   first running it (880–1008). Calling outer creates `A_o`, pushes `RR_o`,
   then its Catch instruction installs `C_o` owned by `A_o` (708–738).
   Reading outer's `thunk` executes the Delay, optionally pushing `V_o`
   (`consume`, 1858–1890). The live stack is `R, RR_o, C_o, V_o`.
3. **Install inner before the original operation.** The delayed argument calls
   inner, creates `A_i`, pushes `RR_i`, binds its own Delay for `io::other 7`,
   and installs `C_i` owned by `A_i`. Executing its `thunk` optionally pushes
   `V_i`. The live stack becomes `R, RR_o, C_o, V_o, RR_i, C_i, V_i`.
4. **Produce the first request.** Operation Apply resolves `d_other`, evaluates
   its int argument in value mode, and makes a request carrier. Its temporary
   operation invocation returns before `OperationResultConsumer` executes that
   carrier (1013–1065, 873–877). `execute` (1929–1960) allocates a fresh event
   `e_other`, records observations of the then-current executing views, and
   enters Request with payload integer `7` and an initially empty suffix.
   These temporary operation frames are no longer live at the handler boundary.
5. **Select the inner arm.** `propagate_request` unwinds `V_i`, if present, into
   the saved suffix and ends that execution view. The next top frame is `C_i`.
   Its installation is validated against current owner `A_i`. The sole arm
   pattern has ID `d_other`, so identity matches; E supplies the remaining Grant,
   signature, payload and primitive-view checks (1550–1610). Continuation `_`
   yields `captured = None`: no continuation template is captured or resumed.
   Only after these checks does the machine pop `C_i`, abandon this raw suffix,
   bind `p_i` to payload `7`, and set Evaluate to `a_i.body` (1640–1680).
6. **Outside inner, retain outer.** Before evaluating `io::tick 11`, the live
   stack is `R, RR_o, C_o, V_o, RR_i`. `C_i` is absent. Its owner `A_i` can
   still be active until `RR_i` is unwound; outside-handler execution does not
   mean that all invocation owners disappear. `abandon_suffix` (1776 onward)
   only releases pending materialization markers in the discarded suffix;
   it does not remove retained outer frames. The selected inner handler is
   not automatically reinstalled.
7. **Produce the arm request.** The arm evaluates the different operation
   `d_tick` with value payload `11` through the same operation-carrier path.
   `execute` allocates a fresh `e_tick != e_other` with new observations of the
   currently executing views. The ended inner execution view supplies no new
   observation; the outer view, if present, remains active. An original request's
   observations or successful match are not reused as authority for `e_tick`.
8. **Reach and select outer.** Since `RR_i` is now above `C_o`, propagation first
   unwinds `RR_i`, calls `leave_owner(A_i, true, A_o)`, and saves its receiver
   boundary. It then unwinds `V_o`, if present, ending that view. Next top is
   `C_o`, still installed and now validated with current owner `A_o`.
   Its sole pattern has ID `d_tick`; E supplies its own request-specific
   evidence and primitive checks. The machine pops `C_o`, abandons the new
   suffix, binds the distinct `p_o` to this request's payload `11`, and evaluates
   `a_o.body`. The live prefix is now `R, RR_o`.
9. **Return and publish.** Outer `p` resolves to `p_o`, reads precisely that
   received payload, and returns integer `11` through Observe consumption.
   `RR_o` restores ModuleRun; `R` caches main's value; source-schedule exhaustion
   returns `RuntimeOutcome::Completed` with that cached handle (1199–1213,
   1810–1855). B covers successful completion within the budget. There is no
   suffix resumption and no continuation replay in this witness.
10. **Public stream.** `lib.rs::execute` renders Completed Integer as its integer
    text followed by one LF. `main.rs::run` supplies stdin source, `main`, the
    requested 10,000 steps and false scoped flag, then prints that result.
    `main` returns success on `Ok`; its stderr error branch is not entered.
    Under H/E/B and successful I/O this gives exactly `11\n` and empty stderr.

This application supplies a concrete parent case: the first request is selected
by the installed inner handler, that exact installation is absent during its
arm, and a genuinely new request reaches the retained outer installation after
the real intervening owner/view transitions. It proves no universal priority,
wrong/sibling permission property, unmatched suffix theorem, foreign-continuation
case, general evaluator correctness, or static-to-native projection.

## Remaining premises, mutual TODOs and falsifiers

| Request / owner | First missing evidence and required inputs | Discriminating output / falsifier |
| --- | --- | --- |
| `R118-HIR-1` / Luna's source reviewer; producer entry `lower_module_with_local_source`, solver `CandidateInference::solve` | Authentic parse/lower/admission of the exact bytes; retained own parameter/catch binder identities; operation-use and arm-pattern equality joins | A source audit must establish H against authentic producers, rather than only building assumed LocalSource. Falsifier: missing/unsupported form, conflict, unresolved or mismatched operation identity, wrong parameter role or outer `p` resolution. This author inspected the pinned consumers, not unpinned HIR producer bodies. |
| `R118-EVIDENCE-1` / Luna's compiler/source reviewer; receiving owners `RootCompSchema::from_parameter`, `Receiving::enter/execution/observe/local_grant`; machine `validate_handler_installation`, `primitive_matches`, `propagate_request` | Positive evidence for these two actual requests and surviving owner/view transitions, using their distinct events and actual installations | Establish E or identify the failing predicate. Falsifier: a handler is reached under the wrong owner, inner reappears during arm code, outer is lost, or the exact request lacks its own matching evidence. The full receiving producer bodies are not direct dependencies inspected here; this is a conditional source seam. |
| `R118-RUN-1` / Luna implementation and verification lane | Frozen new test-only stdin cell for these exact bytes; all contracted fresh reviews CLEAN; no repair of R109 | The contract's separately authorized command must assert success, stdout `11\n`, empty stderr. Falsifier: any different result/stream, unhandled request, unavailable evidence, exhaustion, failed command or non-admission. A passing public cell supplies finite execution evidence, not the hidden identity/stack joins by itself. |
| `R118-REVIEW-1` / Luna | This frozen artifact, its direct pins and the implementation's separate frozen outputs | Appoint the contract's fresh compiler/source, spec and regression reviews. This producer/coauthor cannot independently certify the result. Any source or authority contradiction blocks promotion. |

No production edit is requested. The minimal already authorized implementation
evidence is the test-only public stdin cell in the other lane; a missing source
or receiving certificate returns to Luna for a new exact owner/input decision.
It does not authorize instrumentation or enlarged leases here. General
constraint generation, accumulation, propagation, levels, extrusion, qualifying
intrusion, generalization and residual/provider/witness lineages are neither
replaced nor weakened by this witness. No static constraint/native residual
correspondence theorem is inferred from it.

R109's failed range fixture and assertion remain unchanged. Its closeout is
reused only for the fact that its complete outcome failed at range provenance,
and for the warning against invented Apply-tail ranges. Its earlier completed
cells are not a receipt for these different bytes or the public CLI. R116's
closeout is reused only as historical finite public-entry evidence and explicit
parent-open status. Its successful single-arm cell is not this nested trace.
Neither historical conditional proof is imported as a discharged premise.

## Frozen direct dependencies, authors and resources

| Dependency | SHA-256 |
| --- | --- |
| R118 rev2 contract | `7b588d4e5990b142381f2993e4fa49376d5ebdd0efd2311bb3418f42f3879d63` |
| `notes/design/2026-09-29-scc-intrusion-redesign-charter.md` | `547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed` |
| `tools/inference-playground/src/runtime/machine.rs` | `fa8dab7f7146f528ad354f336cdfe6e41a728505f9c3dd80c6df64e843dc5b46` |
| `tools/inference-playground/src/runtime/program.rs` | `c2363ad42104b895519bb29a8eb9aeda545bd0176cebbd78750d3a2df90849ca` |
| `tools/inference-playground/src/lib.rs` | `bdf996d0264e252e345c05bc77b2adcf625120281244171f0054f1d87a8d1e1b` |
| `tools/inference-playground/src/main.rs` | `75b38435f4634ee35b3e14a54fb4d021b78bda834b4fd53965302a73309e0100` |
| `tools/inference-playground/tests/runtime_handler_priority.rs` | `cdcb06ceebcca48cd3ff6fbc1a429243e9013a148c5fc895d9926e5dc2ce07db` |
| `notes/progress/2026-10-19-r109-nested-handler-observation.md` | `86fb0949fd87f66dbebc6c9615e4987607f6590f49655b2b649a8f8cac34da89` |
| `notes/progress/2026-10-19-r116-closeout.md` | `83428c5cc28254d6d7e7acde7c123d64586864331674fdb3fe20ae3a30912622` |

The contract and historical closeouts are Luna-owned. Charter/source byte
authors are UNKNOWN to this packet; no authorship is inferred from filenames.
The present derivation's sole author is `/root/r118_proof_lane`.
Requested routing: `gpt-6.1-sol`, high; observed model/effort: UNKNOWN/UNKNOWN
because this worker received no runtime model observation receipt.

Checks: read-only source and authority inspection and SHA-256 of direct pins.
No tests, builds, CLI, probes, Git, production edits or new dependencies.
Budget: 480 seconds; exact runtime accounting belongs to Luna's launch receipt
(author-side elapsed observation UNKNOWN). No descendants or scratch files.
Only this artifact and `tasks/agent-loop/inbox/20261019-r118-proof.md` are new.
Freeze at handoff revision 1; writes stop after the matching handoff is emitted.
Next step is Luna intake and fresh review, followed only by the contract's
already authorized implementation/verification evidence. Parent remains OPEN.
