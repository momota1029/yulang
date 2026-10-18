# Operation v1: written callback field, continuation completion, and consumer

Revision 2 of the r17 Luna design; independent review required. Revision 1 is
preserved at `notes/design/2026-10-18-operation-v1-source-completion-and-consumer.md`
SHA-256 `47025832b8ebec78953649890b50e41972e6b210bb5753a2b941e3d82b442c9e`;
its focused spec review was BLOCKING and its source mismatch is captured in
`notes/theory/2026-10-18-operation-v1-source-completion-correspondence.md`
SHA-256 `4147ee01443f8e89187d7fcd99d83865a1ee4458bc8146525989f6c48a01c524`.
The governing r16 research-semantics rule is SHA-256
`1004426d4afa990453d0addc8008f88327166862b63d311be8445eeb4218503d`.

The unchanged parent `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` stays
OPEN / closure 0. This is an additive research semantics v1 candidate. It does
not prove the old semantics, change its fixed contribution, or authorize
production. The existing v1 field rule's conditional wrapper around a supplied
old `d_orig` is not used to manufacture completion here.

## Exact source candidate

```yulang
act outer:
    our next: () -> int
act signal:
    our ping: () -> (int -> [outer] int)

my response (x:int): [outer] int = outer::next()
my result = catch (catch (signal::ping())(1) {
    signal::ping(), k -> k response,
    v -> v
}) {
    outer::next(), _ -> 42,
    v -> v
}
```

This source is a proposed regression input, not yet parser/HIR/inference/runtime
accepted. `ping`'s nested result effect row `[outer]` at
`Operation.Function.ResultValue.Function.ResultEffect`, operand 0 is the exact
positive Written field under study. Existing accepted `ping:()->(int->int)`
does not have that field. Existing exact-Written test
`paired_negative_concrete_callback_interface_is_explicitly_unsupported`
returns `CandidateError::Unsupported` when `k` is used. The new v1 path must
make this exact source run through ordinary parsing, lowering, inference, and
the private playground runtime, and complete with integer `42`; this is an
expected, explicitly versioned acceptance change.

`response` is a source-defined callback, with its own function body and
`[outer]` row. The `signal` handler supplies that actual closure to the
captured continuation. Resuming the saved `( ... )(1)` suffix invokes that
closure, which issues `outer::next()`. The still-active outer handler consumes
that request. The output is produced by these source steps, not injected by a
test. The two `[outer]` rows occur at different source positions; equality of
their family/member is not a license or a map.

## Ordered v1 judgments and rules

All constructors below are new research-semantics v1 judgments, not old
rules. Constructor premises are source/type/runtime evidence; no conclusion
may be introduced by a family-set lookup alone.

```text
OpWrittenField_v1(c, decl, use, theta, path, j, e)
```

`c` is fixed at the resolved `signal::ping` source operation occurrence before
the handler runs. The rule retains the source declaration identity, resolved
reference, occurrence, full signature binder, nested path
`Operation.Function.ResultValue.Function.ResultEffect`, exact source-row
position, operand ordinal `j=0`, written operand `outer`, and source scope.
The source introduction rule is:

```text
HIR resolves this Operation occurrence to declaration `signal::ping`
declaration signature at the exact nested path is Function(int, Written([outer], int))
the row operand at j=0 is `outer`, with its own source position and scope
-------------------------------------------------------------------------------- OP-V1-Source-Written-Field
q : OpWrittenField_v1(c, decl, use, theta, path, 0, outer)
```

No output, handler match, runtime value or solver observation appears in these
premises. Repeated operands at another ordinal or declaration are distinct
proof objects. The resolver must retain the exact `SourceNodeKey` and
`HirOccurrenceId`; it may not rediscover the field by searching for `outer`.

The used continuation requires a negative view of the callback response. The
new constructor is deliberately restricted to the exact field proof `q`:

```text
q : OpWrittenField_v1(c, decl, use, theta, path, j, outer)
the nested result has value type `int -> [outer] int`
make a fresh response effect port `r_j` at the existing level
view_j is an allowance view indexed by q, with allowed family [outer], no tail
-------------------------------------------------------------------------------- OP-V1-Negative-Response-Field
neg_j : NegativeResponsePort_v1(q, r_j, view_j)
```

The term built for the negative function uses `r_j` at that exact nested
result-effect position. The view constrains an actual callback's latent lower
effects; it creates **no lower contribution** and no `Permission -> inflow`,
`Permission -> removal`, or new `Contribution`. Ordinary source operations in
the actual callback body remain the sole lower producers. Multiple nested
function nodes are traversed in full with polarity reversal only at each
function argument. All children, source positions, levels, and sibling rows
remain in the constructed value. If a row is not a positive Written field
owned by q, this constructor does not apply.

The response/resumption judgment is introduced only after source execution:

```text
Request_v1(decl, use, payload, captured_suffix, live_state, event_history)
the source handler resolves the exact same declaration and occurrence
the handler-pattern occurrence resolves that declaration; the request retains `use`
the binder is referenced; candidate typing proves supplied value has full B type
the supplied value is the actual source closure `response`, evaluated in its environment
captured_suffix is the ordered original continuation ending in A_decl
-------------------------------------------------------------------------------- OP-V1-Function-Response-Resume
resume_v1 : CompletedOperation_v1(c, q, closure, captured_suffix, live_state, event_history)
```

The captured suffix is installed with the exact closure value and its
environment. The `ResumeArgument` check uses the typed source derivation and
accepts a Function only when the received runtime value is a source closure
whose candidate type derivation matches the whole declared result path; the
runtime does not infer that type from a `Closure` tag. It retains the original
source site, declaration, response value identity and saved template. It then
executes the source suffix, including the actual application of `response`.

For this source, the only allowed terminal evidence is:

```text
resume_v1 completes application of `response`
the execution emits the actual resolved `outer::next` request
the outer catch's still-live resolved handler selects that request
the handler returns 42; no removed inner `signal` handler is reinstalled
-------------------------------------------------------------------------------- OP-V1-Output-Action
out_v1 : ActualSourceCompletion(c, q, response, result=42, outer_handler_event)
```

`out_v1` retains the actual full output and trace from the same machine run.
There is no independent `d_orig` wrapper, no test-supplied map, and no claim
that this local judgment supplies all old `A_decl` cases.

The v1 NPAIR consumer is a constraint consumer, not an old incidence cast:

```text
q : OpWrittenField_v1(c, ..., outer)
neg_j : NegativeResponsePort_v1(q, ...)
typed source closure response : int -> [outer] int
out_v1 : ActualSourceCompletion(c, q, response, ..., outer_handler_event)
actual constraint graph links the resumed callback invocation's lower `outer`
  to the still-live outer handler's ordinary operand check
-------------------------------------------------------------------------------- NPAIR-Consume-v1
consumed_v1 : V1FieldConsumed(c, q, out_v1, exact_constraint_occurrence)
```

The generated lower is the actual `outer::next()` operation in `response`.
The consumer checks that real lower against the real outer handler path. It
may not construct that lower from `view_j`/`Permission`, family equality,
runtime result 42, responder identity, or a cast to old `contributes-to`,
Contrib, Inc, Cover, selection or subtraction. The exact code owner and
constraint identity are required in the independent proof before any code
lease. No `delta_v1`/`At_v1` is claimed until their original NPAIR definitions
have a genuinely versioned, reviewed eliminator.

## Pending, bounded execution, and divergence

- A source `Request_v1` preserves the operation, payload, event identity and
  history, current live state, exact handler installation, and the complete
  ordered continuation suffix `k >>= A_decl`. Until a handler is selected and
  the actual response is typed, the suffix remains pending and is not
  replaced by a final output.
- A machine step budget exhaustion is a finite observed prefix with status
  `ResourceExhausted { steps }`; a machine still running at the observation
  point is `Running`. Neither is semantic divergence or returning evidence.
- This runtime does not decide infinite execution. A mathematical divergent
  case retains its actual finite prefix and original continuation/history; no
  bounded runner infers eventual return or discards the prefix.
- A returned result is only the actual `Completed(handle)` from the same
  source machine run after `response` and `outer::next()` are evaluated. An
  unhandled request and unavailable response remain separate outcomes.

## Compatibility, gates, and falsifiers

The rule newly admits a used negative callback response with a concrete
positive Written nested result row, subject to its exact source license and
same callback type path. This changes candidate acceptance and may change
inferred effect constraints. It is feature-gated, separately tested, and not
claimed equivalent to old behavior. Existing unsupported expectations remain
valid under the old solver entry. No `stable-core` expected-output is changed.

Independent spec review checks every judgment premise/conclusion, exact field
identity, fresh allowance-only port, full function traversal, actual
continuation identity/environment, ordered suffix/live handler, consumer
constraint and open universal parent cases. A separate compiler reviewer
checks HIR and runtime correspondence before a focused run.

Falsifiers: (1) a different `outer` source row or operation occurrence is
accepted as q; (2) allowance creates a lower contribution; (3) any Function
child or exact source occurrence is dropped; (4) a different but same-family
closure replaces `response` or its environment; (5) the saved application
suffix changes; (6) `outer::next()` reaches the removed/wrong handler; (7)
`42` is supplied instead of returned by execution; or (8) the consumer uses an
old-semantic cast. Any falsifier revokes this v1 candidate and leaves the
parent OPEN.

Not established: accepted HIR for the candidate, source-to-runtime typing
correspondence, source execution, same-development whole output map, v1
consumer implementation, all R/W/Z/futures/domain cases, whole-use transport,
F1/FK1, old-semantic compatibility, soundness, principality, termination or
production readiness. The source candidate still requires a proof and
implementation under r17 revision 2.
