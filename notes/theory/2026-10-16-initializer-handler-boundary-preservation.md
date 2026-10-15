# Initializer handler boundary: pending-frame preservation

Status: independently reviewed local repair theorem and implemented boundary
correspondence. Initialization timing/effect order,
whole materialization and source/runtime adequacy remain OPEN.
Baseline: `885012b42c532134ba0b1b539f93b595732250e9`; runtime `35e87f844`.
Authority: approved forward-definition-initialization-context q1/a1 revision2,
consumed by `2026-10-16-initialization-order-global-effects.md`.
Exclusive output lease: this new note. No code changes or new source policy.

## 1. Frozen local statement

Consider any authentic current-runtime execution prefix from a fresh admitted
RuntimeProgram entry. Fix the original definition d, its empty global cell c,
original Name occurrence u, initializer code, current shared store/cells,
ordered frames and original receiving/effect evidence. The actual empty-global
Name constructor has installed `G = GlobalRead(c, Observe, u)` before entering
d's original body. At a request cut, take G to be the nearest pending such
frame; a nested demand supplies its own nearer boundary. Call handlers below G **read-surrounding** handlers for this
initialization; handlers installed above G remain internal to its actual
execution. This distinction is positional, not equality/inequality of owners.
Both groups can have the same current Invocation owner.

The local theorem to implement is:

1. Existing internal Catch selection/forwarding above G is unchanged.
2. An original request escaping all such internal candidates cannot be selected
   by a Catch below G. With no separately justified global consumer, it yields
   the existing unhandled/error protocol, without crossing G.
3. Original event/source/declaration/payload/observations and shared store are
   retained. No cache publication, Name Observe or caller continuation runs at
   this escaping step; G and its outer caller state remain pending.
4. Normal initializer completion still publishes its actual value once, removes
   its marker and performs original Observe. Subsequent cached reads and
   separately justified latent execution have no old initialization boundary.

Quantification includes nested initializer demands, ordinary calls/Force,
internal shallow handlers, admitted raw templates and all finite execution/
request prefixes. It makes no new whole-source reachability claim, early-entry
scheduling claim, effect detector, global consumer, owner reset or store policy.
No externally supplied execution/resumption API is assumed; the actual public
API is audited in §5. Unsupported source routes remain their existing gates.

## 2. Governing decision and exact construction owners

The approved answer and draft were read and verified equal committed HEAD.
The latest approved ordering clause is that effect-producing lines cannot be
exchanged with one another. It does not say every such line is immovable or
select dependency-first initialization. This proof uses only the independently
specified **escaping-effect boundary**: initializer effects are handled globally
or error, and a handler around a definition value read does not discharge them.
Internal handlers retain ordinary semantics. Automatic consumers still need
actual justification; a source Act named io is not thereby a builtin handler.

The reviewed definition-Name theorem establishes original ModuleDef Observe,
pure Name source/native routing and Delay(original Name). It explicitly leaves
empty-cell materialization open. This packet supplies the local handler-cut
repair at that exact runtime constructor without pretending to settle timing.

Actual `machine.rs:449–481` resolves ModuleDef to its authentic global cell.
For an empty cell it checks/records initializing_globals, pushes GlobalRead
with the original consumption and SourceSite, and enters the original
program.definitions[cell].body in environment0. It does not reset current_owner,
copy cells or reconstruct a provider from the expected argument type.

`execute:1556–1588` emits a Request only from the authentic Request executable.
It retains declaration, payload, original operation SourceSite and a fresh event;
it records observations before unwinding and starts with an empty suffix.
`propagate_request:1222–1404` currently handles a top Catch before forwarding
one frame per step. Its fallback presently pops GlobalRead as an ordinary
saved frame, then can explore caller handlers. That existing step fails the
newly approved local boundary law. The proposed repair below changes that
single crossing, not the initializer entry or the handler eligibility rules.

## 3. Minimal transition to implement

After the unchanged top-Catch inspection/selection block, and **before** the
fallback `frames.pop`, inspect only the actual top frame:

```text
if frames.last() is GlobalRead:
    save request.suffix and request.observations as existing SavedContinuation
    stop with existing UnhandledRequest(
        original source, operation ID, payload value, event, opaque handle)
    return
otherwise:
    use existing no-frame unhandled case or existing single-frame forwarding
```

The stop construction should share the current no-frame unhandled construction
or duplicate it exactly; no new semantic outcome is required. It must not pop
G, scan/validate any lower Catch, call capture_template, execute a global hook
by spelling, publish c, call consume, abandon the retained suffix, or unwind
caller frames to manufacture a globally empty configuration.

Checking only the top is sufficient because each existing propagation step
removes exactly the current top forwarding frame. A nearest pending G becomes
top after, and only after, all above-G forwarding work has run. Checking earlier
by searching the entire stack and stopping immediately would skip internal
handlers. Checking after pop or after inspecting the caller Catch is too late.

This is a proposed transition backed by the theorem below, not a statement
that the frozen production source already implements it. The current source
hash remains the unmodified input listed in §8.

## 4. Stack cut and request preservation proof

Write the live frame stack from outermost to innermost as `C ++ [G] ++ I`.
The pending request suffix S contains frames already unwound from the request's
inner continuation. Because G is nearest, I contains no other GlobalRead; a
nested demand applies the same argument to its own nearer marker. Initially S is empty. Existing single-frame propagation
maintains the following split invariant:

- C and G are untouched while any I frame remains.
- S contains only already removed frames originally above this G; its order,
  original lexical references and handler/owner/view wrappers are preserved.
- Every original ordinary store/cell reference stays shared; no snapshot or
  rollback is performed by request propagation.
- Each popped ReceiverReturn/OwnerReturn performs the existing matching
  leave_owner; each popped RootCompReturn performs its existing matching
  end_execution_view. Thus the live owner/view stack is exactly the remaining
  dynamic prefix, with the removed span represented in S.
- The original request event, operation/source/payload and observations are
  unchanged. Observations retain their original pre-unwind evidence and are
  not recomputed under a caller or made valid merely by a family match.

Induct on the number of above-G forwarding/selection steps.

**Above-G Catch.** When the current top is CatchReturn, all original candidate
checks run before removal: declaration/operation identity, source Grant or
closed-primitive certificate, declared payload kind, pattern/continuation
conditions, installation owner/liveness and capture validation. The repair
branch is not taken. A selected arm executes outside that exact shallow
handler, still above G; an unmatched Catch is converted to its existing saved
HandlerBoundary. No new matching or visibility predicate is introduced.

**Other above-G frame.** Existing fallback pops that frame and performs its
existing owner/view transition, then appends its saved representation to S.
G and C remain live. Calling into other code merely adds ordinary frames
above G; its escaping requests obey the same cut. This proves preservation
through arbitrary supported nested Calls/Force/ordinary execution prefixes.

**At G.** When I is empty, the new test stops without popping G. Therefore no
below-G Catch can be inspected/selected for this event. The original event is
exported through UnhandledRequest, and source-facing execute already reports
that outcome as an error. No invented global consumer is used. G's cell is
still empty and its initializing marker still live; Observe and publication
are Return operations and have not run. C, its owners/views and the current
store remain unchanged at this stop. This proves the required exclusion.

Notice that an actually valid caller-side local Grant is irrelevant here:
the caller Catch is not a candidate on the initializer's escaping search path.
The repair neither changes Grant semantics nor claims every such grant false.
It also does not use current_owner as an initialization territory identifier.

**Nested initialization.** If A's execution installs h_A around Name(B), the
stack is `C ++ [G_A] ++ ... ++ [h_A] ++ [G_B] ++ I_B` (or Root_A below h_A).
B's internal handlers above G_B work normally. If B's request escapes them,
G_B stops it before h_A, even when both handlers share the same owner and store.
Thus A's read-surrounding Catch cannot discharge B's initialization. No search
for the earliest/global marker or source-name heuristic is needed.

## 5. Saved suffix, cache ownership and terminal API

The existing unhandled protocol stores `SavedContinuation { frames:S,
observations }` and exposes only an opaque ContinuationHandle. At the proposed
early stop, G and C remain in the stopped machine, while that handle records
only the already-unwound initializer suffix. This is an explicit **terminal
split representation**: it is not a claim that the saved handle alone is the
whole continuation, or that a future global response may execute it directly.

Actual public readers (`machine.rs:354–363`, runtime mod exports) expose value,
continuation_depth and step/run. No public operation applies an unhandled
ContinuationHandle or reinjects a response. step/run on Stopped return the same
outcome. continuation_depth reports the saved S length, exactly as implemented;
it does not promise the full live-plus-saved depth. Hence retaining the caller
prefix live causes no current execution/resumption to bypass the boundary.
Any future automatic global consumer or external response API must prove how
this split resumes without importing read-surrounding handlers; it is outside
this repair and must not be inferred from the handle's existence.

`abandon_suffix:1406–1418` releases initialization markers only for cache writes
whose suffix is actually discarded on an abortive selected arm. It must **not**
run at the new stop: S is retained and G/C remain live. In particular clearing
G's marker would detach a live pending write from its owner. No arm result is
cached as an initializer's value at the stop. The current machine may retain
pending resources because it is terminal; this is not a leak into another
execution or a newly approved cancellation/reinitialization rule.

Within this repaired fresh-machine execution, a request cannot have crossed a
GlobalRead into S: the new test prevents the first crossing. Previously
admitted raw templates cannot inject one either: capture_template:1003–1067
rejects GlobalRead and Root before publishing a template. Thus an above-G
abortive internal arm may abandon ordinary inner suffix work, but never the
still-live G. Existing outer initialization markers are preserved. This closes
the relevant abrupt-control cache-ownership case, rather than assuming only
normal Return.

## 6. Raw continuations, normal completion and later latent calls

For an internal resumptive handler above G, capture_template receives only the
above-handler S. Its cache-frame exclusion remains unchanged. Its ordinary
Bind/Owner/View/ForwardHandler nodes retain original references; none saves G.
enter_template:1080–1165 reconstructs those admitted nodes above the current
live prefix and uses the current shared state. Resumed owner occurrences and
view delimiters keep their existing validation; no owner is reset to ModuleRun.
A resumed request during the still-active initialization encounters the live G
when its inner handlers are exhausted. A selected caller raw template therefore
cannot contain G, because the caller is never selected across it.

The proof does not permit old A/B repeated cache-write completion. A template
whose result later escapes as a value can be invoked after initialization,
but its saved nodes did not include G. That later latent invocation has its
own actual executing configuration and existing receiving/control obligations.
It is not a rerun or continuation of a captured initialization publication.

Normal completion is unchanged at `return_value:912–928`: only an actual
returned value pops G, is stored in c with Value interface and the original
view, removes the live marker, and reaches the original consume/Observe.
ModuleDef compilation selects Observe; consume authenticates its value/view,
records the genuine current-owner receipt and returns it without executing
latent data. Later populated-cell Name reads use that same branch. Calling a
cached closure or otherwise executing a legitimately designated latent
computation happens after the old G has gone; the repair does not block its
ordinary surrounding handlers. Expected computation formals still retain
Delay(original Name), without substituting initializer code.

Root-only initialization keeps its existing internal handler behavior. Fresh
ModuleRun has no read-surrounding caller Catch below its root scheduler; the
new branch does not change Root forwarding. This local fact is not a proof
that all early forward entries respect the approved effect-producing-line
order, or that every current entry is source justified.

## 7. Exact implementation and verification handoff

A minimal implementation changes only propagate_request's fallback:

- inspect top GlobalRead after unchanged top-Catch handling, before pop;
- use the existing unhandled allocation/outcome fields unchanged;
- retain current live prefix/markers/store and saved S/observations;
- leave normal GlobalRead Return, capture-template guards, owner/view transitions,
  handler checks and Name consumption untouched.

No global registration/spelling dispatch is authorized. The current tool builds
HIR with SemanticImports::empty and uses current source Act resolution; a user-defined io
family is handled like any authentic declaration. The unhandled/error path is
a justified current outcome where no actual automatic consumer exists.

Primary/verification-owner checks to run after authorized code, not run here:
(1) read-surrounding Catch cannot handle an initializer event, including a raw
binder and closed-primitive eligibility; (2) initializer-internal Catch still
handles/discards/resumes normally; (3) nested B excludes A's Catch(Name B);
(4) escaped event identity/payload/source and terminal suffix are retained,
with G and caller prefix live and no published cache/Observe; (5) pure normal
completion and later cached closure invocation remain ordinary. Inspect owner,
view and initialization-marker state at the exact stop, rather than accepting
only a changed diagnostic. Source syntax admission and early-order validity
remain independent requirements for any claimed whole-source fixture.

The existing `tests/runtime_resume.rs:149` test
`captured_definition_materialization_keeps_its_separate_decision_gate_open`
currently expects ContinuationMaterialization for relay's Catch around the
forward Name later. Under this repair, GlobalRead is encountered before the
caller Catch can capture, so the causal outcome is authentic UnhandledRequest,
not that later capture guard. Its expectation/name update requires the primary's
assigned specification prewrite review; no test edit is performed here.
Preserving the old search merely to preserve that output would violate the
approved revision2 boundary. This changed local outcome selects no old A/B
cache publication law and does not certify whole-source early-entry validity.
The inspected test hash is
f892173c928165ce65a57e31ee110613eb3226c1f22b0c18787b6fce235c9099.

Additional cost is one O(1) top-frame test per fallback request step. It adds
no stack scan, global registry, receipt history scan, source cap or successful
ordinary-execution allocation. The unhandled case uses the existing saved
suffix/observation allocation; retained live prefix already exists. This is
structural accounting, not a benchmark.

The proposed transition satisfies the named local theorem by the actual cut
invariant above, subject to independent review and actual repaired-source
correspondence. Whole initialization/effect-order detection, global consumers,
source admission, publication/resume policy and production cutover remain OPEN.

## 8. Frozen inputs and commit packet

```text
approved-answer.md 8e238cdbd185c9f3bdd6042d7bc536bb827e869def34e363b3e79f29d8c77c12
answer-draft.md 5169884bbcbc5fff5b4a6633c69983fdd7bf2f775780645532bb578673069b57
initialization-order-global-effects.md c33d0e601ea5152068d0bd8b52f02747964455d9d2e8518974ca9c83bf15e37b
definition-name-computation-role.md a7f5181c65326c30e47b8288d7af9462c344f6027d23955bd9d0f3be56f96f0d
runtime/machine.rs e30bb19c54b1a4ee07f3b1d2f0a5e88e57f2226fd055071a6d1ca5f1bdfd5e3a
runtime/program.rs b9798ac4c5d93e761582d712114615defa913f858d70e91f170471c8b8912748
runtime/continuation.rs 194e925c2e19816e05e8d0cdf773123f205dce47d36d83a70385daa07a77e2b3
runtime/receiving.rs 5443c8ca55e58a37b6d003cf5b2985214d37776094f02637adfbe30200cc36bd
runtime/mod.rs 64d208743793a03501a76f56bc2b511c50ed40cff3f789757a00b7d608fc846b
```

Question paths are under questions/2026-10-16-forward-definition-initialization-context;
runtime paths under tools/inference-playground/src. Checks: exact approved input
reads and committed equality; bounded actual-source reads; direct dependency
hashes and artifact whitespace. No code/tests/builds/probes/Git mutations,
children/shared-record edits or measurements. Requested normal configured
prover Sol/high; observed runtime model/effort unknown. Independent review
pending; no producer certification or claim of repaired implementation.

Commit packet: sole new path
`notes/theory/2026-10-16-initializer-handler-boundary-preservation.md`; baseline
885012b42c532134ba0b1b539f93b595732250e9. Suggested checkpoint:
`research: prove pending initializer handler boundary preservation`.
Primary shared-record delta: consume the local GlobalRead cut theorem after
review, authorize only its exact fallback repair, and retain original timing/
effect-order/materialization/global-consumer/source-runtime gates OPEN.

## 9. Primary integration and independent review

Compiler-referee `runtime_semantic_review` accepted the frozen local proof CLEAN
at producer SHA-256 `7157da6cd4bd9d74b22cbfd1ff133a4574ff1948e0e9badb2fc103e86c63c61e`.
The actual two-file implementation has CLEAN semantic and specification delta
reviews. The [integration record](../progress/2026-10-16-playground-initializer-boundary.md)
records exact production hashes, the pre-cleared causal expectation change, one
strengthened minor control and primary verification: all 108 playground tests pass.
The local repaired-source correspondence is complete; the whole materialization,
initialization order, source admission, global-consumer and cutover parents remain
OPEN. The preceding dependency table is the original proof's input snapshot,
not an assertion that its pre-repair machine hash is the implemented source.
