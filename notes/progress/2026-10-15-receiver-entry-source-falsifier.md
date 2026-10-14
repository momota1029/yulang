# Receiver-entry source bridge: bounded static falsifier

Date: 2026-10-15
Status: unreviewed research checkpoint; bounded source-owner characterization
Baseline: `922edf574d9ad08b0b4d84a31d0d6651673636d2`
Branch assigned: `research/simple-sub-intrusion`
Lease: this file only; frozen on submission
Method: static constructor/fixture audit and literal inspection of the conditional query
Parent gates: H1/H2/U OPEN; H3/P disabled

## Objective and governing premises

Test whether the existing static `(Lambda, formal/root, omission scope, Apply,
ResultEffect)` introduction can itself identify receiving activations, establish
Observe/Receive, and enforce expiry/re-entry. This is complementary falsification,
not the separately assigned constructive proof or review of that proof. No
producer output from that lane was read.

The directional addendum `2026-10-06-directional-inferred-effect-protection-addendum.md`
§§2–4 selects the original upper Function `ResultEffect` only and excludes
provider-output backflow. It explicitly does not establish event receipt.
The typed-boundary Draft `2026-10-02-typed-boundary-realization-draft.md`
§§1–2,6 selects activation-scoped typed transport, receiver expiry, and current
state for raw shallow resumption; its concrete source realization is still open.
Its §4 specifies fresh execution occurrences for resumed views and preserves
the resumer's ambient views. The top-level inference principles §§1,1.1,3
prohibit replacing ordinary source constraint construction with execution or
speculative search.
None of this audit selects another profile position or source meaning.

## Result and first missing mapping

**The static tuple authenticates an introduction template, not an activation.**
The first missing source mapping is from a real receiver entry, under the
original typed invocation, to its exact receiver/boundary instance and the
receipt-bearing typed view used during that entry. The subsequent missing map
is from an actual request emission and executing views to Observe and the
current activation roots. Existing constructor authentication supplies neither.

This is a bounded missing-source witness, not an impossibility theorem or a
runtime compiler misprotection counterexample. No source program was executed.
The proposed use of a static key *alone* as an exact activation identity fails
the lifetime discriminator below; using it as a template paired with separately
established activation evidence remains possible and unproved here.

## Actual static owners

All locations refer to the frozen baseline.

| Owner | Established static fact | Missing fact |
| --- | --- | --- |
| `candidate_source.rs:250–286,382–396` | One registration per source Lambda; omitted formal retains owner, Lambda occurrence, parameter and annotation scope | No dynamic entry or activation occurrence |
| `candidate_source.rs:604–621` | One Apply input per source expression; checking/cause derive from the source occurrence | No execution count, current receiver or receipt |
| `shadow_apply.rs:1497–1525` | Original formal registration joins omission to the original demand's raw `ResultEffect` before constraint admission | No executing view, event or live-owner evidence |
| `candidate_call.rs:341–527` | `observe` validates HIR ownership, raw Function4 ports, original registration/scope and exact introduction | This function observes an inference artifact; it does not emit typed semantic Observe |
| `candidate_call.rs:135–145,269–300` | Pending suppliers include receiver dispatch and complete result/future interfaces | No completed source receiver supplier is certified by successful structural solving |
| `candidate_effect.rs:806–863` | Catch forms monomorphic payload and raw response/continuation ports; continuation returns original scrutinee value and retains conservative full-S effects | No runtime capture/entry, receiver expiry, selected-handler authority or event routing |

The formal's retained native root is intentionally shared by wrapped/captured
uses (`candidate_call.rs:228–234`). FreshUse row copies or distinct source Name
uses therefore cannot simply be renamed receiver activations: the first is an
inference operation, the second a compiled occurrence. No bijection to runtime
entry instances was found at these inspected owners. The fixed packet also
states that the native candidate has no omitted-formal protection classifier;
this note does not rerun the earlier IDENTITY-context attack.

## Small source witnesses and their qualification

### Existing fixture support

These are checked-in fixture assertions inspected statically, not tests run by
this worker and not VM execution results:

* `shadow_candidate_call_formation_crosswalk.rs:23–32,324–329` uses
  `my apply f = { my step x = f x; step }`. It retains a captured call and
  expressly counts one source call: returning `step` adds no invocation. This
  separates a static latent Apply from its later execution.
* The same file's `ordinary_call_use_spine_keeps_each_receiving_root_and_pending_premises`
  uses `my id x = x; my first = id 1; my second = id 2; pub exported = first`.
  Separate typed uses do not duplicate the source body or discharge its pending
  receiver premises.
* `candidate_local_self_recursion.rs:26–51` uses one `loop x = loop x`
  initializer, one open recursive occurrence and two later fresh uses. The
  fixture distinguishes an open monomorphic recursive root from fresh inference
  uses; it does not enumerate the unbounded recursive execution activations.
* `shadow_apply.rs:1736–1762` already includes
  `my apply f = { my first = f 1; my second = (f) 1; my step x = ({ f }) x; step }`.
  Its three directional introductions count source upper demands, not receiver
  calls or event observations.

The smallest collision candidate without capture is:

```yulang
my apply f = f 1
my id x = x
my first = apply id
my second = apply id
```

Under ordinary invocation, the single compiled `f 1` is reached in two distinct
receiver entries. Its source Lambda/formal/scope/Apply/ResultEffect tuple is
identical. This composition is constructor-supported by the fixtures above;
this exact spelling was not parsed, inferred or executed in this assignment.
It witnesses the missing activation distinction, not a bad observable effect.

### Expired capture during a later entry

The next discriminator keeps the first callback capture after its receiver
returns, then invokes it during another entry of the same receiver source:

```yulang
act signal:
    our ping: int -> int

my receiver f = { my step x = f x; my ignored = f 1; step }
my old = receiver signal::ping
my later = receiver old
```

Conditional intended trace: entry alpha receives `signal::ping`, calls it once,
returns `step` capturing that input, and ends. Entry beta later receives `old`;
its `f 1` invokes alpha's returned `step`, which calls the captured operation.
At that second operation emission, alpha has expired while beta is live.

This uses existing Lambda/Block/captured Name/Apply/operation constructors;
the individual constructor shapes occur in the cited fixtures. The exact
composition's admission, typing, concrete execution and typed transport are
**unverified assumptions**. This is a candidate source discriminator, not an
accepted runtime counterexample. It does not require resurrecting alpha;
beta may independently protect the event through its own complete view. The
claim tested is only that alpha's retained profile must not become live merely
because beta shares the same compiled receiver introduction. Establishing which
profile reaches which exact event port is still the missing bridge.

### Shallow-Catch, operations and raw resumption

`candidate_operation_catch.rs` supplies ground operation arms, direct and aliased
raw continuation uses, repeated `resume` calls, response entry effects and an
operation returning a callback. Its header explicitly leaves eligibility and
residual removal open. `candidate_effect.rs:840–863` enforces response-entry
effects and constructs raw continuation Function4 ports with no handler
reinstallation; this is typing construction, not executable context restoration.

An additional unexecuted operation-identity discriminator is:

```yulang
act signal:
    our ping: int -> int
    our pong: int -> int

my result = catch signal::pong 1 { signal::ping(x), k -> k x, v -> v }
```

Both operations share a nominal family, while the single operation arm names
`ping`. The existing operation lookup retains the actual declaration
(`candidate_operation_source.rs`), and Catch retains that declaration for each
arm (`candidate_source.rs:431–457`). Family equality therefore cannot supply
the actual matching operation, an event witness, its Observe port, or a receipt.
This exact composed fixture has not been run; no routing result is asserted.
The packet's raw-resumption obligation cannot be reduced to that family test.
Repeated resumes may re-enter the same compiled Apply with fresh executing
view occurrences; saved scopes are not all currently executing scopes (§6).

## What `query_conditionally` proves and assumes

`yu-core/src/shadow_typed_evidence.rs:14–87` accepts caller-supplied context,
typed-port nodes, profiles, Flow edges, Observe records and Receive records.
It validates pointer-context consistency, port indices and duplicate port
identities. It does not validate source licensing or corresponding typed paths.

At lines 92–149, the query computes the following literal condition:

1. A supplied Observe has the same event-witness pointer as the queried event.
2. A supplied Receive has that exact port and the candidate owner's pointer.
3. Supplied Flow reachability connects the profile port to such an endpoint.
4. Candidate handler, candidate owner, and the profile's original receiver are
   all present by pointer identity in the supplied current activation lists.

The result is always labelled `ConditionalStatus::Assumed`. Boundary identity,
original receiver, event identity, handler/owner identities, active roots,
profile-port licensing, corresponding-path receipt expansion and Flow/Observe
source derivation are supplied assumptions. The query does not infer a
protection seed, grant release or select a handler. In particular,
`AssumedBoundary.witness` and `AssumedProfile.witness` are retained identities;
this query's lifetime test uses `boundary.original_receiver`.

### Minimal conditional identity-collapse derivation

Assume one valid port, a profile at it, one supplied observation for event q at
that port, a receipt for candidate owner c at it, and live candidate h/c. No
Flow edge is needed because reachability includes the starting port. Let
alpha be the profile's original receiver and beta a distinct current receiver
entry sharing its static source tuple. Assume beta live and alpha absent.

Literal evaluation yields `path = true`, `inc_c = false`. If a proposed bridge
replaces alpha/beta by the same static receiver token, the same current-live
lookup instead yields `inc_c = true`. This is a conditional contradiction to
using the static key alone as exact receiver identity. The omitted premise is
the source qualification of the supplied observation, receipt and profile for
an actual alpha/beta execution. It is not proved by this boolean derivation.

The existing helper fixture
`exact_joins_lifetime_and_malformed_inputs_remain_conditional`
(`yu-core/tests/shadow_typed_evidence.rs:104–225`) already inspects this
distinction with equal-valued, different-address tokens, including fresh
receiver re-entry after expiry. That fixture creates its own tokens and
relations; it does not connect them to compiler source activations. Its
three-node closure oracle independently checks finite graph reachability,
while sharing all supplied source-evidence assumptions. Neither oracle proves
the missing source rules. No new checker, mutation or equivalent toy probe was
created or run in this assignment.

## Coverage, limits and next action

Static coverage: original omission/Apply constructor and validator, Function4
introduction, captured/returned callback source fixtures, separate typed uses,
local recursion, ground operation Catch and raw continuation construction,
conditional typed-evidence query and its tests. No full source evaluator,
complete Call elaboration, unknown-shape signature proof, imported clients,
generic operation opening, residual subtraction or source-wide lifecycle proof
was audited. Existing fixtures are evidence of intended constructor coverage;
their assertions were not executed here.

Commands were bounded `git show BASE:path` reads, text selection and `git ls-tree`
for object hashes. Two initial broad outputs were truncated; no exhaustive
scan is claimed. One guessed source path `candidate_operation.rs` was absent;
the actual owner `candidate_effect.rs` was then inspected. Zero Cargo, tests,
builds, probes, measurements, seeds/ranges, executable mutations or Git
mutations. CPU/RSS and exact elapsed time were not measured; this was one
static-only worker under the 15-minute allocation.

Recommended next evidence-producing handoff: map the actual source receiver
entry and returned-capture transport for the alpha/beta discriminator to exact
typed view/boundary/receipt and expiry events, retaining original source
template identity separately. Require the owning constructor evidence before
feeding those records to the conditional query. This needs a source/elaboration
bridge; another supplied-token reachability checker leaves the premise untouched.

## Frozen dependency Git blob IDs

All are at the baseline; current-worktree/HEAD dependency changes were not
assessed. The primary must revalidate before integration.

```text
5e0499e43b3dbf04de0bcdb6c0fa5994224d8a87 notes/design/2026-10-02-typed-boundary-realization-draft.md
a72d434fcc48f71da14f044d006096fdf7fb19d3 notes/design/2026-10-06-directional-inferred-effect-protection-addendum.md
ad10d6f8188325e666121b400686e4fb5682d10f notes/design/2026-10-11-yulang-inference-top-level-principles.md
37f7356eaa6a754540c54dddd1fdcbe6742dba23 crates/yu-core/src/shadow_typed_evidence.rs
ffee7bd17fbebb844c9c9c7d09e635ee6dfadc99 crates/yu-core/tests/shadow_typed_evidence.rs
b3d840d11210b7ba1dc9b0cf80a190dbda6a0919 crates/yu-solver/src/candidate_call.rs
f4271fffd07a7035e41f1885c63b0f78dbd6dbe1 crates/yu-solver/src/candidate_source.rs
5062ddf457158ba1f8c7caa2cab57d21bdb324ee crates/yu-solver/src/shadow_apply.rs
f0536987d66b817c774dae63e51c0e7bde0ca279 crates/yu-solver/src/candidate_effect.rs
7c69b87365e9f11676b8fd6357b7dc4b0d507ece crates/yu-solver/src/candidate_context.rs
7f40fc4e1aa74720ef857134412f08d3b40e633a crates/yu-solver/src/lib.rs
ec44429a159e9b1ac66951107709d669ad2e216d crates/yu-solver/tests/candidate_local_self_recursion.rs
7fa6a6f34201a4940206b9986b8a8101f9dc1da8 crates/yu-solver/tests/shadow_candidate_call_formation_crosswalk.rs
a1fd3d703a540acfb16e517f013215040222210c crates/yu-solver/tests/candidate_operation_catch.rs
405c8b76df55af623264c00bc360e002222f2156 crates/yu-solver/tests/candidate_operation_source.rs
49c028f40558d30a84c3ca90a1bd009805391561 crates/yu-solver/tests/candidate_catch_value_source.rs
efede3fd2a1e96270031b1a3ce4c4c4aa9b7f12f crates/yu-solver/tests/candidate_annotated_function_formals.rs
```

## Commit packet

* Exact leased path: `notes/progress/2026-10-15-receiver-entry-source-falsifier.md`.
* Baseline: `922edf574d9ad08b0b4d84a31d0d6651673636d2`.
* Dependency changes by worker: none; pinned hashes above; current HEAD recheck
  deferred to primary integration.
* Claim/review status: bounded static falsifier and conditional identity-collapse
  derivation; unreviewed, research-only, frozen on submission; no parent closure.
* Checks already run: static source/fixture/query inspection and baseline blob
  lookup only; no executable checks.
* Proposed commit message: `research: characterize receiver activation source bridge gap`.
* Shared-record deltas left for primary/curator: record original receiver entry,
  matching receipt/observation and expiry/re-entry source mapping as the next
  missing bridge; preserve H1/H2/U OPEN and H3/P disabled. No shared record was edited.
