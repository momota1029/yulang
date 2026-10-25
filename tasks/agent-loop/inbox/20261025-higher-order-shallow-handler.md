# HO-SHALLOW-HANDLER-20261025 / handoff revision 1

Sprint-ID: HANDLER-RECURSIVE-RHS-THEORY-20261025/r1.
Contract: `tasks/agent-loop/sprints/handler-recursive-rhs-theory-20261025-r1.md`.
Contract SHA-256: `a921540d9539741dcc9dbacb9bd45f0dc086ecb97cdb03dc360dbbda1fd267eb`.
Baseline: `03eb4b672c29f92c7bed0e2b6e4a1fbb53741c82`.
Parent: HO-SHALLOW-HANDLER-1; paper399–456 and1069–1088, original
execution theorem1139–1159 unchanged and OPEN at full-paper/native scope.
Outcome class: CANDIDATE mathematics; UNCHECKED, UNREVIEWED, no production authority.

## Runtime and authorship

Actual worker: `/root/higher_order_handler_astra_r1`, lane A leaf.
Session: HANDLER-RECURSIVE-RHS-THEORY-20261025/root-r1.
Launch evidence: actual NEW_TASK delivered to this identity; primary reports
spawn acknowledgements before07:08:14.918560UTC. Conservative resource start
07:07:26.019051UTC, preceding dispatch. Requested Astra/medium; observed model
UNKNOWN, observed effort UNKNOWN. Sole author at freeze: this worker. No
coauthors, descendants, child spawns, background processes or unresolved leases.

Author freeze/write cessation: `2026-10-25T07:14:09.461690+00:00`. Conservative elapsed
`403.443` seconds of1200; remaining reserved author allowance
`796.557` seconds is unused, not automatically transferred.

## Actual result and parent application

Full recursively extended Value/Comp/Adapter/Handler/ValueArms/OperationArms
syntax and extrinsic typing; all accepted constructors structurally embedded
with typing preservation. Mutual renaming/substitution preserves every code
binder, including lambda consumers outside the lambda parameter binder.

Actual operation attempts use simultaneous payload/K substitution. K is a
concrete value lambda containing the original response body and an identity
adapter, with Callable(Q,A) typing. Forwarded H K separately wraps that body
under the shifted handler, with response-to-B typing. Equality compares the
full OperationInstance through derived constructive DecidableEq suppliers.
All arms are typed independently of their raw eligibility flag.

Raw Step contains no typing/safety oracle. It covers ordered trials, No/Yes,
value MatchFailure versus operation forwarding, effects outside the selected
handler, and request propagation through waits retaining original request,
payload, K and remaining arms. Every base and new transition has a preservation
proof attempt; closed_progress gives only Ret/Request/Fail/next-step; arbitrary
finite internal-prefix safety follows. Response substitution preserves each
independently quantified typed response without consuming K.

Concrete candidate applications: selected_execution executes a real higher-order
call to unit-to-unit K inside a unit-to-bool handler; forwarded_execution_safe
and distinct_continuation_types separate H K; ordered_value_trials_safe handles
No then Yes; wrong_identity/arguments_skipped preserve instance discrimination;
nested_request_restoration_typed and nested_response_restoration_typed preserve
pending waits; nested_lambda_call_safe covers handlers under lambda and adapter
binders; no_after_event retains the event before No in the prefix.

Main verification targets in namespace YulangClosure.HigherOrder.Handler:
`embedValue_typed`, `embedComp_typed`, `embedAdapter_typed`, all six renaming and
substitution typing theorems, `attemptOperation_typed`,
`forwardedContinuation_typed`, `preservation`, `closed_progress`,
`finite_prefix_safety`, `selected_execution`, `nested_request_restoration_typed`,
`nestedLambda_typed`. These are candidate declarations, not checked claims.

## Source/native evidence and missing premises

Frozen runtime audit only: Machine::propagate_request captures selected K before
popping CatchReturn and executes outside that occurrence; HandlerBoundary /
ForwardHandler preserve forwarded handler data, whose replay allocates a fresh
occurrence. No full source/native simulation or actual eligibility proof follows.

HO-HANDLER-VALUE-EMPTY-1: machine.rs1098–1136 returns received when no value arm
exists, unlike paper MatchFailure. Primary semantic/source intake must adjudicate
that exact discrepancy; this packet authorizes no implementation change.
HO-HANDLER-NATIVE-WAIT-1: propagate_request currently selects a restricted direct
arm and does not supply general typed effectful No/Yes attempts/pending waits.
Falsifier for a later bridge: nested response loses original K/payload/remaining
arms or reinstalls the selected handler around attempt effects.
HO-HANDLER-SOURCE-1: source Catch elaboration must construct the exact simultaneous
payload/K binder and full-instance association. Falsifier: wrong binder/instance,
untyped disabled arm, or omitted accepted constructor.
HO-METADATA-ADEQUACY-1: permissions, owner/activation freshening, view/receipt
semantics and rigid polymorphic elaboration remain OPEN with Luna/source intake.
Full-paper omitted forms, graphs and combined arbitrary saved external interaction
remain OPEN. No F1/FK1 or original Simple-sub A/B closure is claimed.

Minimal next evidence request is read-only source-to-raw binder/instance/wait
mapping with the above owners/falsifiers; no production code TODO is authorized.
Any prototype or wider lease requires Luna. The full details and precise source
locators are in the leased note.

## Prior work and checks

Accepted HigherOrder syntax/metadata directly reused. Accepted Substitution,
Entry and Safety structural methods/base proofs are adapted and reproved over
the new syntax; their old theorems are not assumed to cover new constructors.
Interaction's independent-response boundary informed the construction but its
old arena theorem is not promoted to handler safety. Literal-only/history proofs,
assumed transitions and source restrictions are not used to close the parent.

Lean/build/tests/checkers: NOT_RUN by author, as required. Textual inspection and
SHA-256 hashing only. Primary owns compilation and strict transitive axiom checks
(subset{propext,Quot.sound}), then fresh nonauthor review. No axiom/sorry,
Classical.choice or native_decide is intentionally introduced. No producer
certification. Original contract's outcome A is submitted as a full candidate
construction/proof attempt, with acceptance contingent on those independent checks.

## Frozen artifacts (all new paths)

- `notes/theory/lean/YulangClosure/HigherOrderHandlerSyntax.lean` — `2cb1791d5bdb108acd8be4b75683a7d6cb2780592ced1cacbaeb7a5a88730381`
- `notes/theory/lean/YulangClosure/HigherOrderHandlerSafety.lean` — `2496d79d0844dce8e452a92fdc6c150bbcc0ee77cc1414d2340b6a103f5a4397`
- `notes/theory/2026-10-25-higher-order-shallow-handler-theory.md` — `162337d62c6926e9fcfff4990957d62ace6346a05d5295f841dbf21faad3d82a`
- `tasks/agent-loop/inbox/20261025-higher-order-shallow-handler.md` — this exact handoff; its byte hash is sent separately to Luna.

No other new or scratch paths. The handoff itself cannot contain its own hash.
All four exact leases are frozen; no accepted or other worker file was edited.

## Frozen direct inputs and reused/audited sources

- `notes/theory/lean/YulangClosure/HigherOrderSyntax.lean` — `ea727d33692bdcbe6b40245b960d01225b556b5334ffab649eea2699930d5972`
- `notes/theory/lean/YulangClosure/HigherOrderSubstitution.lean` — `19910452c45b20761ec06dc7e15f94c94b95014ff00f3f5296af005b9adf6f30`
- `notes/theory/lean/YulangClosure/CoreSyntax.lean` — `c5a25cb7d935159b62f377b7fa88b3e92e4cdf429118d566e53f7859f6ea5375`
- `notes/theory/lean/YulangClosure/CoreSubstitution.lean` — `ae1dfd4947d9e87c05dfa893b93067175d860ed3b5da000d61257d7789208b55`
- `notes/theory/lean/YulangClosure/HigherOrderEntry.lean` — `c9cb839ff6b34ed97c5d72f9e020437d32175cf517a5841a3a024764747c213b`
- `notes/theory/lean/YulangClosure/HigherOrderSafety.lean` — `16a38dbb649677ed5e6b6371a61228a1724b9e899136eeb2119b755ecab30336`
- `notes/theory/lean/YulangClosure/HigherOrderInteraction.lean` — `45f2b8c74e2837e503db84aed3c9f55767a32d19e4008546e25a01cef1202875`
- `docs/yulang-operational-type-safety-ja.tex` — `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`
- `tools/inference-playground/src/runtime/machine.rs` — `b621ba8ec28d7819db881a4fd5bad0236edbf23e2aa92a879eb1dd211a30c46e`
- `tools/inference-playground/src/runtime/continuation.rs` — `194e925c2e19816e05e8d0cdf773123f205dce47d36d83a70385daa07a77e2b3`
- `notes/design/2026-10-25-higher-order-proof-core.md` — `50eb7ebd2ed2d155dfeca2e3ce99f3f5b990cc4f1bf101663949a04d8d4b748f`

The contract freezes the larger96-pin dependency set; the above are direct
formal inputs and the precise adaptation/source authorities used by this author.
No dependency on lane B's new outputs.

## Mutual TODOs and stop

- HO-HANDLER-CHECK-1 (Luna): elaborate these frozen bytes, inspect public
  quantifiers/transitive axioms and concrete traces; retain failed receipts.
  Falsifier: elaboration failure, nonapproved axiom, omitted constructor/step,
  handler inserted in selected K, or request-through-wait binder corruption.
- HO-HANDLER-REVIEW-1 (Luna-appointed fresh nonauthor): independently review the
  frozen component against outcome A and paper. Producers/coauthors are ineligible.
- Source/semantic intake: consume the four source/metadata TODOs above; do not
  promote the candidate to production or shrink the original full-paper claim.

Next in-envelope step: primary checking and independent review after this STOP;
no remaining author task or implied background work. Writer state STOPPED;
writes STOP at the timestamp above, no processes/descendants. Any repair by the
primary creates coauthorship and a new frozen snapshot for independent review.
Commit/integration readiness: PENDING primary checks and fresh review, not accepted.
