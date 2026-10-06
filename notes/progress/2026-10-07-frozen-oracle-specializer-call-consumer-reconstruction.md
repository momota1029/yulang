# Frozen Oracle: source application consumer reconstruction in Specializer2

Date: 2026-10-07
Status: independently compiler-referee-reviewed bounded historical characterization; two minor scope/locator repairs integrated
Yulang3 baseline: `5afa7643f9bfe85366119a1faacf042bb0f010c6`
Frozen Oracle: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Exclusive lease: this file only
Semantic and implementation authority: none

## Question and result

The open `ORIGINAL_ASSOC` producer needs to connect one original source Call
and its exact callee/argument to a typed whole invocation contribution in the
same original `X` and `xi`. Earlier Oracle traces locate source application
constraint generation and later provenance projection, but not that complete
pre-solve association.

This bounded pass follows a distinct historical consumer: on the ordinary,
non-effect-operation App branch that returns successfully, the second-pass
`Specializer2` reconstructs a typed Function consumer for the retained
`poly::Expr::App`. It consumes the already materialized callee type and
argument contract, adds a callee actual-to-expected subtype obligation, and
types the call result. Direct effect-operation Apps take a separate route.
The consumer's provenance owner is the **callee expression**, while the App's
own `ExprId` is used to record the result and runtime-shape site. This is a
concrete source-oriented reconstruction mechanism, but it is downstream of
inference and cannot supply the missing original source producer.

## Historical mechanism

All paths below are relative to the pinned Frozen Oracle tree.

1. `specialize2/task_solver.rs:479–495` receives the retained App, callee and
   argument expression IDs, handles effect-operation calls separately, then
   obtains and splits the callee's materialized runtime type.
2. For an already decomposable Function, lines 497–519 select a consumer
   argument/effect view from the Function parts and argument materialization,
   then form a complete `Type::Fun` consumer using that argument view and the
   callee's return-effect/return ports. If the callee has no Function shape,
   lines 535–544 synthesize fresh argument, result and result-effect variables
   and form a provisional Function consumer.
3. Lines 520–532 or 545–557 register that consumer on the callee expression,
   materialize actual and expected occurrences owned by that **callee
   `ExprId`**, and submit their subtype relation to the specialization graph.
   The argument is separately consumed against the Function argument contract
   (lines 499–512 or 558); the App result is assembled from call-argument,
   return and evaluation effects (lines 561–565 and following).
4. `task_solver.rs:166–174` obtains provenance through the sidecar key
   `(owner, role, empty path)`. `poly/provenance.rs:69–105` keeps those
   occurrence keys in a table separate from semantic IR. A missing key yields
   empty positions and `Incomplete` in `task_solver.rs:142–164`; it is not
   reconstructed from equal type shape.
5. Later, `specialize2/emit.rs:248–266` emits each App as an `ExprKind::Apply`
   and asks `callee_argument_effect_contract` for a formal-indexed argument
   boundary contract. This is a separate emitter path, after task solving.

On the ordinary non-effect-operation route, this gives a historical sequence
of: retained source App → materialized callee consumer → sidecar-owned
actual/expected subtype → result and emitted Apply. The call's typed
expectation is rebuilt using solved/materialized information; it is not an
original pre-query certificate.

## Boundary against the current obligation

The mechanism resembles a typed consumer for one application and preserves
some source identities. It does **not** establish any of the following:

- an original `OriginalAssocType_X(beta,p0,j_call;s,c)` witness before `Q`;
- a `beta` or exhaustive `Slots(beta)` inventory;
- a complete original invocation footprint over all output and pending rows;
- typed owner/receiver/capture/receipt incidence on the original shared
  `(nu,K,D)`;
- comparison-independent applicability, complete-profile formation, either
  licensing inclusion, or independent admission.

In particular, the App's own expression identity does not become the owner key
for the callee comparison in this routine; the keys shown are the callee's
`ExpressionActual` and `ExpressionExpected`. The later boundary emitter can
recover a source formal by finding the call-spine head and applied argument
index, then walking the declaration's lambda chain and reading its
formal-indexed sidecar (`specialize2/emit.rs:1149–1163,1173–1183,1192–1237`).
That route is a downstream contract consumer, not evidence that the original
source relation exhaustively generated or licensed the contract.

These are historical implementation assignments only. The solver,
materializer, sidecar producer and specializer share one implementation's
assumptions. No Oracle run, printed type, or successful subtype result is used
as semantic evidence. No current semantic rule or implementation permission
is inferred.

## Scope and checks

Read the exact pinned `task_solver.rs`, `emit.rs`, and `poly/provenance.rs`
windows listed above, plus the App dispatch/result registration and the
formal-lookup helper windows cited in the boundary paragraph. The Oracle
checkout resolves to the stated pin and was clean at inspection. SHA-256
digests:

| Oracle file | SHA-256 |
| --- | --- |
| `crates/specialize/src/specialize2/task_solver.rs` | `cc534583e8fd154b51e8c857ef7b17df19fe68e9410fd9acb74c1d13cb1d2f66` |
| `crates/specialize/src/specialize2/emit.rs` | `7318b132cef4217ae089d084577fb28f3abed34a5728474ee8569e4079d71e7c` |
| `crates/poly/src/provenance.rs` | `9b1dc3fa436d92c39c2732ec401f10b3747e3e0f1bb921dc23b96fb19039e519` |

The compiler-referee independently reviewed the frozen claim and found no
blocking or major issue. It confirmed the ordinary App consumer/provenance
route and identified two minor issues, both repaired here: effect-operation
Apps were outside the described branch, and the formal-lookup claim needed its
helper locators. The reviewer also left the full materializer/graph proof,
sidecar production and broader source/production paths uninspected. No build,
test, execution, mutation, timing or performance measurement was performed.
Claim class remains bounded historical characterization; `ORIGINAL_ASSOC` and
all dependent theorem and production gates remain open.
