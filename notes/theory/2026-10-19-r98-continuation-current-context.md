# R98 finite continuation reuse under current receiving contexts

Status: FROZEN candidate source-to-runtime-constructor correspondence, revision 1;
not independently reviewed, not a source-language handler-restoration theorem.
Author: `/root/r98_proof`; no descendants or coauthors. Requested model/effort:
Sol/high per assignment policy; observed model/effort: UNKNOWN (no runtime metadata
receipt supplied to this leaf). Sole outputs: this note and
`tasks/agent-loop/inbox/20261019-r98-proof.md`.

## 1. Original parent and finite application

R98's original obligation is the exact three-cell source/template/current-context
correspondence in its frozen contract, preserving raw capture identity, original
suffix and distinct current receiver/view/handler identities. The broader parent
remains the original Simple-sub/evaluator soundness, ordinary inference and
source/native hygiene obligations, including `R78-NATIVE-HYGIENE-1`, A/B,
R50/R85 and independent foreign-continuation quantifiers F1/FK1. No quantifier is
replaced by these three finite executions. Accepted input here is exactly P/N1/N2
below, under the existing LocalSource playground adapter and unchanged runtime.

Application to the parent: this constructor audit identifies a concrete shared
capture with two responses and distinct local receiving evidence, and exposes
the exact candidate execution falsifier. It supplies a finite operational bridge
target for independent review and Luna's one command. It supplies no arbitrary
provider/continuation typing, complete J_raw introduction, native K/D projection,
no-free/generalization result or production authority. Simple-sub generation,
accumulation, propagation, levels, extrusion, qualifying intrusion and
generalization receive no replacement rule.

Authority is scope-sensitive: ordinary-computation semantics §§2,3,5 and typed
source-owner realization §§1–3 are decorated-source candidate packages with
explicit input limitations. The prior capture-projection note §§2–4 is reused
only for retained operands and five-constructor control projection; its supplied
typed-view/interface premises are not inferred from parsing this fixture.

## 2. Exact source bytes and variant binding

The actual added test is
`runtime_resume.rs::same_raw_continuation_reuses_suffix_under_each_current_receiver`.
P is its decoded Rust `positive` string. N1/N2 are its actual `replacen(...,1)`
results; all are UTF-8 ASCII with LF separators and **no terminal LF**. The
following fences display those exact contents (the closing fence separator LF
is not a source byte).

### P: 389 bytes; SHA-256 `da8221d6ea8aa23fc64ea87510dc975ebf7a5861d45a90adcf51be7ff61c2f79`

```yu
act io:
    our tick: int -> int
    our other: int -> bool
my first (thunk:[io] bool) = catch thunk { io::other(p), _ -> true }
my second (thunk:[io] bool) = catch thunk { io::other(p), _ -> false }
my relay (thunk:[io] bool) = catch thunk { io::tick(p), k -> { my before = first (k 11); if before: second (k 23) else: true } }
my main = relay { my result = io::tick 7; io::other result }
```

### N1: 388 bytes; SHA-256 `f46d65226835c25a8ee197f65d70320b507d63dfee2c75d6a157d2cd28021755`

```yu
act io:
    our tick: int -> int
    our other: int -> bool
my first (thunk:[io] bool) = catch thunk { io::tick(p), _ -> true }
my second (thunk:[io] bool) = catch thunk { io::other(p), _ -> false }
my relay (thunk:[io] bool) = catch thunk { io::tick(p), k -> { my before = first (k 11); if before: second (k 23) else: true } }
my main = relay { my result = io::tick 7; io::other result }
```

### N2: 388 bytes; SHA-256 `e357e218870f30b95c2608bfb0f3354d495ab46ad3925c43c596110b3218ff9d`

```yu
act io:
    our tick: int -> int
    our other: int -> bool
my first (thunk:[io] bool) = catch thunk { io::other(p), _ -> true }
my second (thunk:[io] bool) = catch thunk { io::tick(p), _ -> false }
my relay (thunk:[io] bool) = catch thunk { io::tick(p), k -> { my before = first (k 11); if before: second (k 23) else: true } }
my main = relay { my result = io::tick 7; io::other result }
```

Each actual replacement needle occurs exactly once. N1 replaces only the
`other` token inside first's operation pattern with `tick`; N2 does so only in
second's pattern. P byte intervals [107,112) and [177,182), respectively, become
`tick`; all other bytes remain equal under the resulting one-byte offset.
The operation declarations, suffix `io::other result`, relay pattern, both
responses and branch bodies remain byte-identical. This closes the pre-edit
review's pending-byte caveat as a producer audit; independent delta confirmation
is still required. No existing expectation is changed. Implementation author `/root/r98_implementation` froze this test at SHA-256 `449c3ce11ef04fa60a49517c2fc8a7994d1547cb2dee058d6fdcbd0b095f8580`; its revision-1 handoff SHA-256 is `7bdce2ee736281be6da118b011d932c7334ca566b57c77710bd3098a8952f0c2`, acknowledged by Luna in the direct assignment message.

## 3. Source constructor and identity correspondence

`local_source.rs` named-formal construction retains each admitted parameter ID,
source/range/scope and annotation parsed with that definition's SourceRootId
(lines 590–638). Thus first, second and relay have three distinct formal IDs
spelled `thunk`, each with its own `[io] bool` annotation owner. Their row's
concrete family resolves through `source_annotation.rs` to the same unique
source declaration `io`; the result value is primitive Bool. No equality of
spelling identifies these formal IDs. `RootCompSchema::from_parameter` checks
annotation/formal ownership, explicit effects and primitive result shape.
`program.rs` maps these parameters to Computation role and their parameter Names
to Execute. This is a bounded runtime role adapter, not general annotation
meaning or a whole-source typing theorem.

`local_source.rs::IdentifierExpression` first resolves lexical IDs, then unique
module definitions; Catch arm construction installs its actual binder IDs in
that arm's lexical scope. Hence both `k` Names resolve to the **same** relay-arm
CatchBinder ID (ordinal 1), while `p` has that arm's ordinal 0 and `_` introduces
no binder. `result` and `before` resolve to distinct actual Local IDs; first,
second and relay Names resolve to their module definitions. Bool literals resolve
as Boolean forms. `program.rs` retains these resolutions, source roots,
occurrences and labels; nonparameter Names Observe. The runtime cell lookup is
by Binder/ID, not by printed spelling. The same k cell therefore holds one
`ExecutableValue::Continuation(t)` and both applications read that t.

`resolve_operation` uses unique family and member namespaces, retaining the
actual SourceOperationDeclaration. Write `io_id` for that family, `tick_id` and
`other_id` for its two declaration-owned IDs. They are distinct. tick has Int
payload/Int response; other has Int payload/Bool response. `catch` iterates arms
in original source order and `program.rs` copies that vector without reordering.
There is one operation arm and no value arm at each Catch: P first selects
other→true, P second other→false, relay tick→the before/if block. N1 and N2 change
only the corresponding first/second selector identity. No arbitrary handler
coverage or priority order is inferred from this single-arm fixture.

Application construction delays the entire argument; closure receiving entry
allocates a fresh invocation, creates the exact RootComp boundary and genuine
formal receipt, and binds the inert carrier. Executing its `thunk` Name creates
a current-owner read receipt and fresh execution view before executing it
(`machine.rs::consume`). The main block's Local frame waits for `tick 7`, then
binds the returned integer as result and evaluates the original `io::other result`
suffix. The operation application consumes its request carrier only after its
operation invocation returns (`OperationResultConsumer`); its operation receiver
is already ended when the request is emitted. None of these constructor checks
are claimed as an observed parse, HIR or inference receipt: helper preparation
remains UNOBSERVED until the authorized command. The actual helper invokes
`CandidateInference::solve` (`crates/yu-solver/src/shadow_apply.rs`, delegated to
`solve_mode`) before `RuntimeProgram::from_hir` and start/run. That is the
existing source→constraint/solve→runtime preparation path. No generated bounds,
propagation trace, extrusion/intrusion incidence or native evidence object has
been observed by this leaf. Neither the source audit nor the future green test
would prove those original inference preservation obligations.

## 4. Original capture and finite constructor induction

Let r be relay's active receiver, h_r its installed Catch, v_r the view opened
by executing relay's thunk, and c the pending Local cell for result. At the
initial `tick 7` event, the pending source suffix contains the actual Local frame
for that block followed by `RootCompReturn(v_r)`. `propagate_request` saves Local
as Ordinary and ends/saves v_r as Ordinary RootCompReturn. It reaches h_r while
r remains active. tick_id matches; the observation of v_r joins relay's genuine
receipt and its `[io]` boundary, giving the local grant. Primitive Int payload
and response shape permit capture. These are the concrete constructor premises
of the candidate transition, not an assumed abstract transition oracle.

`capture_template(request,r)` therefore constructs, from inner to outer:

```text
n0 = Hole
n1 = Bind(n0, original Local(block,next=1,environment,c,recursive=false))
n2 = View(n1, original v_r execution record)
n3 = Owner(n2, Invocation(r))       # explicit containing-owner root
root = n3
```

No saved ReceiverBoundary occurs here: the tick operation receiver ended before
emission and relay's own ReceiverReturn lies below h_r. The selected h_r is popped
by shallow selection and contributes **no ForwardHandler node**. No GlobalRead or
Root frame is captured. c is pending, not a bound result certificate. The raw
template stores source frames, handles, declaration and original event; it
stores no live-store snapshot. The relay arm binds t once as k, outside h_r.

Induction over this actual four-node chain:

- Hole returns the actual Int response under the then-current machine state.
- Bind pushes a clone of the original pending Local frame. On actual return it
  fills c with that response, extends the original environment by result's ID,
  and evaluates `io::other result`; it neither reruns `tick 7` nor skips that
  suffix. Sequential reuse may overwrite c; this fixture does not assert
  noninterference for arbitrary aliasing, nesting or parallel uses.
- View obtains a **fresh execution occurrence** for the same saved view/receipt,
  appends it to the existing current executing views, and installs a matching
  RootCompReturn. It does not rewrite the old receipt's owner or remove the
  resumer's view. This is the limited retained-operand projection of the prior
  capture note, not its full typed packet/interface premises.
- Owner starts from this use's fresh empty control map, resolves r, borrows it
  because relay has not returned, inserts r→r, and pushes OwnerReturn with its
  actual previous owner and owned=false. Completion restores that previous owner
  without ending r. If this owner were inactive, `new_invocation` would allocate
  a fresh occurrence and map only executable control slots; that branch is
  source-audited but **not reached by this fixture**.

`ForwardHandler` is absent from t, so no induction case for it is needed for t.
Its implementation resolves the saved owner through the per-use control map,
checks activity/current attribution and allocates a fresh Catch occurrence.
The negative paths do save their unmatched first/second Catch as HandlerBoundary,
but never call capture_template on that outward suffix; thus they do not
construct or enter a ForwardHandler TemplateNode. Claiming five constructors
occur here would be false. All finite constructors actually present have been
covered; other Bind frame varieties and re-capture remain outside this result.

## 5. Two applications, current observations and exact forwarding

Use j=1 with response 11 and current receiver first f, then j=2 with response 23
and receiver second s. Each application's Callee continuation branch allocates
a fresh k-use invocation a_j and forces its response expression exactly once.
ResumeArgument validates Int response against t's tick declaration, pushes one
ResumeReturn and enters t with `HashMap::new()`. The maps and pending frames are
separate even though t, original capture event and c are retained identities.
Only the capture root returns to that resumer. No use-count restriction is added.

first/second computation entry has already created its **own** view v_f/v_s,
formal receipt and Catch h_f/h_s before its thunk `k 11`/`k 23` executes. Entry to
t appends re-executed v_r, preserving v_f/v_s. When its unchanged suffix exposes
other, `execute` allocates a **new** event e_j and observations for all currently
executing views, including v_f/v_s and re-entered v_r. Original tick event is
retained in t as lineage and is not replayed as e_j. Owner r is executable
attribution inside the saved span; it is not f/s and does not rename their
receipts. During outward search, the saved view ends, borrowed r completion
restores a_j, a_j's ReceiverReturn ends a_j and restores f/s, and the current
receiver's executing view ends. h_f/h_s is then reached with its actual owner
still active/current. Ending an executing view does not erase its authenticated
event observations or genuine receipts.

For P, h_f then h_s match other_id exactly. Their positive local grants use
candidate-owner receipts for their exact v_f/v_s, the same-event authenticated
observations and their own concrete `[io]` boundaries (`Receiving::local_grant`).
The inherited v_r alone cannot supply a receipt for sibling/current receiver f/s.
The continuation wildcard causes no new capture; selection abandons the request
suffix and evaluates true/false outside that exact shallow Catch. The first
true fills before and selects the second call; the second false reaches relay's
return and main completion. Candidate prediction: Completed(Boolean(false)).

For N1, h_f covers tick_id, so the other_id candidate is skipped before any
local grant query; search forwards its exact handler/environment/installation
as HandlerBoundary. Relay's selected h_r is absent, and no second receiver has
been entered. Remaining frames are saved until the request stops outward with
other_id and payload Int(11). For N2, first's true still reaches second, whose
changed selector similarly forwards other_id and Int(23). There is no fallback
selection based only on family equality or lack of a local grant. The suspended
outward suffix and ContinuationHandle remain distinct from original t; neither
negative request is resumed by this test. General unmatched-suffix resumption
and arbitrary foreign continuations remain open.

All three runtime outcomes and preparation success are **UNOBSERVED** in this
leaf's handoff. The derivation is a candidate trace of inspected constructors;
it is not a fabricated dynamic trace or test pass.

## 6. Remaining premises, mutual TODOs and falsifiers

`R98-OBS-1` — owner Luna: after implementation freeze and CLEAN spec delta, run
exactly the contract's one focused command. Required evidence: real preparation,
all three cells executed, P false; N1/N2 UnhandledRequest with exact other_id and
Int 11/23. Preparation failure, wrong operation/payload/result, stale receiving
context, dependency drift or blocking/major review stops R98 without repair/retry.
No production implementation TODO is justified by the present static audit.

`R98-REVIEW-1` — owner Luna/fresh independent reviewers: check this finite chain,
source identities, retained current-view grant and actual one-pattern variants.
A real extra captured frame, missing current receipt/view, inappropriate handler
installation owner or erased suffix falsifies the stated bridge. Producer cannot
certify it. Implementation must retain exact helper/source bytes and report its
frozen dependency; proof handoff must remain immutable during review.

Parent obligations remain: actual complete decorated source/typed J_raw and
uniform arm membership (operation-package source owner); arbitrary raw/foreign
resumption and inactive-owner cases (source owner spans/enter_template consumers);
arbitrary provider/view support and no-free introduction (capture-projection
§§4–7); native K,D/constraint/evidence projection (native source/consumer owners
under R78); inference A/B and production adoption (Luna). This finite local
borrow cannot settle F1/FK1 or original independent quantifiers. R88 U/O/S and
R95/R97 bounded bridges are not promoted to whole-source authority; no R91/R93/
R94 failure is reused as a theorem, and no assumed transition test is used as
proof of actual source construction.

## 7. Frozen dependencies and resource receipt

Read-only static inspections and source-byte/delta hashing only. No build, test,
playground CLI, Git, production edit, expectation edit, scratch file or descendant.
A `python` byte-inspection attempt failed because that executable was unavailable;
`python3` performed the read-only extraction. These are not runtime checks.
Budget: proof ceiling 600 seconds, Astra 0; no enlargement. Exact elapsed active
work is UNKNOWN without a launch timestamp receipt; no budget renewal is requested. Next in-envelope step is Luna intake/review/one command;
this leaf stops writing at freeze rather than remaining RUNNING while waiting.

SHA-256 dependency manifest (actual file bytes):

- `tasks/agent-loop/sprints/continuation-current-context-20261019-r98.md`: `e5fb81b1ff423726fa853dcaf5c99deba4f3b286d1d84111268143872e95d4dd`
- `tasks/agent-loop/inbox/20261019-r98-spec-review.md`: `4dff6cf726aa0adc16f45ceaed2365a4b9d5a3e295ab73beb9917c62bece342c`
- `tools/inference-playground/tests/runtime_resume.rs`: `449c3ce11ef04fa60a49517c2fc8a7994d1547cb2dee058d6fdcbd0b095f8580`
- `tools/inference-playground/src/runtime/machine.rs`: `fa8dab7f7146f528ad354f336cdfe6e41a728505f9c3dd80c6df64e843dc5b46`
- `tools/inference-playground/src/runtime/continuation.rs`: `194e925c2e19816e05e8d0cdf773123f205dce47d36d83a70385daa07a77e2b3`
- `tools/inference-playground/src/runtime/program.rs`: `484967c20c829344a8abe3aa583f6a65e715fb927b8d6b0ba816f0cc6291ad11`
- `tools/inference-playground/src/runtime/receiving.rs`: `8c81deadc48c4770f25760e9086d2053815785ff16cfd5580fa814fb83af9bd9`
- `crates/yu-hir/src/module/local_source.rs`: `3014628f861840ca8e716b3baf8e6a3c9dd736b1bad318b32e7a7b195ddf8786`
- `crates/yu-hir/src/module/source_annotation.rs`: `b8462b66eac24a48b6fc5e931a3d8b7c38c19bb8b2f1a7cdc4ecd9a8a7a1117f`
- `notes/theory/2026-10-16-source-raw-continuation-capture-projection.md`: `5d0f6f1403e9956f162069f39574ea91cbf268315dbf50d25465fe00e3ae65f8`
- `notes/design/2026-10-02-typed-source-owner-realization.md`: `5cbd8110736ee4d43e0c65460fa9ecf700228bfdbe9fbaa7642ea0302d86f1aa`
- `notes/design/2026-10-02-ordinary-computation-semantics-package.md`: `ee3f5cf8185d516775b8915b0fda6dbb07390c3ecad7ac028eb5995581dff917`
- `tasks/agent-loop/inbox/20261019-r98-implementation.md`: `7bdce2ee736281be6da118b011d932c7334ca566b57c77710bd3098a8952f0c2`
- `crates/yu-solver/src/shadow_apply.rs`: `5bbcf27d51906814ba38b2cca2066807d285d0b1817f0ea6e04d70c4a5c8a5cb`
