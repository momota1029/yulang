# R39 native source-to-Result trace

## Outcome and parent application

**Outcome class:** source-native evidence, candidate-only; no theorem or implementation closure.

At the exact original occurrence `q = loop y` in `helper`, the current candidate path retains an occurrence-qualified negative Value result port from source construction into the Apply demand, authenticates that port during `candidate_call` observation, and exposes it through `native_result()`. The solver's function expansion has an ordered fourth child for that Result port, so it can participate in propagation under q's constraint occurrence. The reviewed source does not show an actual semantic Call Result consumer that consumes q's result as the complete source Call result/Desc. The first missing edge for the requested complete chain is therefore the source-owned Result consumer/typing interpretation after the native observation. The original source-rule owner for `Desc(q, ValueDescription, sigma_R, Delta_R)` remains the proof/source lane's question; this trace cannot supply it.

The unchanged parent remains OPEN: the original Simple-sub A/B claims, quantifiers, source domain, Call/effects, F1/FK1, N-Transport, soundness, principality and termination do not follow from this candidate path. No Result/Desc rule is adopted, no source domain is narrowed, and no code or expected output changes are authorized by this trace.

## Exact source occurrence selection

The original specimen (also recorded in the pinned R38 candidate) is:

```yu
my outer = { my loop x = { my direct = loop x; my helper y = loop y; my first = helper x; my second = helper x; helper x }; loop }
```

Select `q` by source identity, never by vector position: locate the `outer`
definition root, its `helper` local binding, then the Apply expression in that
same LocalSource whose callee resolves to the `loop` local and whose argument
resolves to parameter `y`. This distinguishes q from `t = loop x` in `direct`.
The specimen contains five Apply source occurrences: q, t, the `helper x` calls
in `first` and `second`, and the final `helper x` call. Each is emitted as its
own Apply recipe/input and has its own occurrence and result component. In the
candidate observation API, enumerate `0..source_call_count()`, call
`source_call(index)`, and select the unique observation whose owner and
`source().occurrence()` equal the exact source owner and q occurrence. The API
is indexed rather than occurrence-keyed; this selection rule does not depend on
`calls[0]`. In scoped mode a retained `by_occurrence` map also maps source
occurrence to input index, but it is not the general observation API.

Static identity and construction evidence is in the pinned
`candidate_scheme.rs` unit test `active_outer_root_two_helper_uses`, which finds the helper's `loop y`
using local binding identity and argument spelling and separately retains the
direct `loop x` occurrence. This is code inspection only: the test was not run
and its assertions are not treated as semantic proof or as a substitute for a
source rule.

## Native edge trace

| Stage | Retained edge for q | What this establishes / does not establish |
| --- | --- | --- |
| HIR source | `outer` definition root -> exact helper LocalSource -> q Apply expression, callee `loop` local, argument parameter `y` | Exact occurrence and operands; no inferred type owner |
| `candidate_source.rs::emit_candidate_source` | Every source expression receives Value/Effect positions keyed by HIR occurrence. The Apply arm retains owner/expression/operands/checking occurrence/cause/recipe; `CandidateRelation::Apply.result = pos.value`, `result_effect = pos.effect`; `source_input` points back to that `ApplySourceInput` | q's `result` is a native Value component position, distinct from its Effect position. No sigma/telescope/Desc is stored there |
| `shadow_apply.rs::admit_candidate_fact` | Checks the registered recipe's source input and exact occurrence, endpoints, effects and result positions. Converts q's result component to a negative live Value term. Builds demand `NegativeFunction(argument, argument_effect, invocation_effect, result)` and stores it in `NativeInterface.result` with the same term | The fourth demand port is the exact input result term. Admission establishes a constraint to check, not that it is satisfied or semantically typed |
| Constraint/provenance | Admits occurrence `ConstraintOccurrenceId(q, 0)` with lower = positive callee and upper = q's negative Function demand. Separately admits effect slots 1 (callee effect) and 2 (invocation effect), each with q occurrence identity | Value Result is not either effect port. Occurrence-qualified constraint/provenance edges are retained |
| Propagation representation | `candidate_scheme.rs::Capture::expand_node` expands positive/negative Function terms into ordered children `[argument, argument_effect, result_effect, result]`; child 3 is q's Result. Captured bounds and intrusion parents preserve their source relation/evidence. The R38 source test inspects the exact q result row under the q checking event, separately from its argument row | There is a native structural propagation route for the Result port. A test-only joined capture assertion is not evidence that every semantic Call obligation is closed |
| Observation | `candidate_call::observe_inner` reopens the input's source expression and checks Apply shape, exact operands, owner scopes, checking occurrence/cause, NativeInterface demand fields and native Value/Effect sorts. `CandidateSourceCall::native_result()` returns that retained term | Authentic local native result observation; it does not attach a source `ValueDescription`, introduction scope, dependent telescope, or semantic consumer |
| Consumer boundary | `CandidateValueObservation::source_call(index)` returns the observation; the only Result-facing method found is `native_result()`. Pending construction requests `OriginalGenCall0`, whole carrier and receiver/complete-result/future suppliers, while `UNRESOLVED` remains. The native constraint solver consumes the Function demand structurally, but no source-owned Call consumer uses q's Result to construct the complete source result/Desc | **First missing edge:** an actual source-owned Result consumer/typing interpretation joining q's `ApplySourceInput.result` to the complete Call output's ordinary `Desc` owner, sort, introduction scope and ordered telescope. No consumer can be inferred from a descriptor label, solver term, or request inventory |

The full direct source inputs and the five relevant implementation files were
re-hashed in this assignment and match the R39 contract pins. This reuses R38's
source-constructor and native-demand pins because the bytes match exactly; it
does not reuse R38's prior non-consumer conclusion as proof of this trace.

## TODO and falsifier

`R39-RESULT-CONSUMER-OWNER` — owner: original Call/source-typing and native
consumer owners, coordinated by Luna. First required evidence: identify the
actual source rule/consumer at q that consumes the complete Call Result and
binds it to a declared ordinary `ValueDescription`, its sort, introduction
scope, and all ordered dependent fields. Then show the same q occurrence and
typed projection carried through the native consumer. A pinned source-owned
consumer plus a complete typed projection map from q's Result port to that
declaration would falsify the missing-edge finding. This is a request for
evidence, not a lease or semantic authorization.

No provisional instrumentation was added; there is no cleanup task. No Rust,
test, fixture, expected-output, manifest, or other worktree path was changed.

## Inputs, checks, omissions, and runtime

Contract: `tasks/agent-loop/sprints/original-call-introduction-result-consumer-20261018-r39.md`, SHA-256
`a985a8c25fdf8598631d503365e9b977020ecac8a0a9262a245d081f1ec73199`.

| Direct input | SHA-256 |
| --- | --- |
| `notes/design/2026-10-08-call-source-interface-definition.md` | `20edc62e798cef22111d0303b71a18b7769060515855fac1b315a5eba37b255c` |
| `notes/theory/2026-10-08-call-source-interface-construction.md` | `278034197a90eab6e62a073545c09dd14415a0353f58aa3b3cc122a6af945d98` |
| `notes/design/2026-10-07-complete-call-contribution-definition.md` | `4c83a095dce3636ada842bfc32c18cf0ef598db0e361861fb8e659745b74411e` |
| `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` | `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240` |
| `notes/design/2026-10-02-source-result-synthesis-choice.md` | `71326de0897159343797d6aec083860ee0f57a1bc04f9c4ae77e579ea0ba5992` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |
| `notes/progress/2026-10-18-r38-candidate-review-closeout.md` | `8ed59d6013f0be42e3f3609dd45fe4db37d9897dc7fec6d1b7790d1cb1f58050` |
| `notes/theory/2026-10-18-call-result-owner-r38.md` | `63ba5b3fe053b8ced790f089ab0a6defcf554b440114b94a9f901cec3176af92` |
| `crates/yu-solver/src/candidate_source.rs` | `66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c` |
| `crates/yu-solver/src/candidate_call.rs` | `e038ad0dfc4b12bd0d513d6cd6b34cee6b2b062d8b33368bc1c0dcdef980d479` |
| `crates/yu-solver/src/shadow_apply.rs` | `d5e6b179fd4f6fbca579b0fa4d479d8bd11b520d774acbf27f414451c4691137` |
| `crates/yu-solver/src/candidate_scheme.rs` | `8c370e47d5e8692a618fedf41be07d7ae3ac961f9070bfed6730e2b8e2f1137e` |
| `crates/yu-solver/tests/candidate_local_self_recursion.rs` | `47ced76fe8f0f136c42802b2376ca09f7cadec0fc8e5b1b3d4c6acc7bc613e55` |

Checks: exact direct-input SHA-256 inventory; static source inspection of the
constructor, admission, constraint/provenance, function expansion, observation
API, R38 specimen, and pending suppliers. No Git command, build, Cargo command,
test, nested CLI, or generated file. No dynamic occurrence counts, native IDs,
solved rows, executor trace, or complete source typing were measured. These
omissions prevent this artifact from claiming execution, theorem closure, or a
complete source/native Result consumer.

Assignment: R39-NATIVE-RESULT-TRACE, handoff revision 1. Requested model/effort:
Luna/high. Observed model/effort: UNKNOWN/UNKNOWN (no runtime model metadata was
provided to this worker). Worker: `/root/r39_native_result_trace`; session:
`current-conversation-2026-10-18`; launch: direct bounded assignment from Luna.
Charged grant: 720 seconds; actual active-work duration was not metered by a
runtime receipt. No descendants or generated outputs. Writes stopped after
freezing this note and its matching inbox handoff.

## Artifact freeze

This file is frozen with the matching inbox handoff. Its hash is recorded in the
inbox; the final inbox hash is supplied to Luna with this frozen handoff.
Independent compiler review remains required; the author does not certify this
trace.
