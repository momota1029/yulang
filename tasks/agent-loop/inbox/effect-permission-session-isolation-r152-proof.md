# R152 proof/source handoff — revision 1

Assignment-ID: `effect-permission-session-isolation-r152-proof`.
Sprint: `effect-permission-session-isolation-r152`, contract revision 1,
SHA-256 `5fd4a9441a90be2b1201b179d8afb83c71ca2bbf4a8ca25c6f78e4da0d5bcc51`.
Admission SHA-256: `d90d065ca5124c5df82c08a6db54dd4bfe76efefc1a95ae965147e21aba85fd9`.
Worker/author: `/root/r152_proof`, assigned proof/source lane, session
`EFFECT-PERMISSION-SESSION-ISOLATION/20261102-R152`. The current parent assignment
and active-work message establish this assignment's execution; no descendants.
Requested model/effort: UNKNOWN/UNKNOWN. Observed model/effort: UNKNOWN/UNKNOWN,
as confirmed by the parent; no model is inferred from a role name.

Outcome class: **source-native-evidence plus conditional falsifier**. This is an
authored static audit, pending fresh independent review. No Lean theorem or
axiom audit is claimed; Lean execution was excluded. The source-wide parent,
INITIAL-STATE, CONSUMER, A/B and production gates remain open.

## Parent claim and immediate application

The R152 obligation is that every successful permission-use binding joins a
route, native term store, permission state, registered formal and retained
FreshUse mapping owned by one actual `InferenceSession`. Independent sessions
must remain independent even when they share source identities and have equal
registration, row and use ordinals.

The frozen input does **not** establish this invariant at its exposed binder.
`candidate_scheme::bind_native_formal_entry_permission_use` changes from one
session plus route/incidence indexes to independently supplied `route`, `store`,
`effect_state`, `registered_formals`, registration and occurrence. Its successful
return authenticates structural/source equality but contains no test that
these arguments have a common session owner. A common Rust borrow lifetime
does not establish that owner equality. This is sufficient to HOLD a claim that
the frozen API itself enforces session isolation. It does not establish an
executed production misbinding or a source-program result.

## Authenticated inputs and inspection method

Committed baseline: `225c5519943fc490c3d5620683918674f4f6afd5`, tree
`52417724761f968a75f83b064ebbae9138727671`. Read-only Python decoding of existing
loose object bytes authenticated each inspected object with its Git object
SHA-1; no Git command or repository mutation was used. Rust line locators below
refer to that committed baseline, unless explicitly identified as patch lines.
No dirty Rust file was read.

| Input | SHA-256 |
| --- | --- |
| Frozen R152 input patch | `643d75e8e8435253a8606af7800134c28ce8eb74c86b1880ab169d5b8891bd1a` |
| `candidate_effect.rs` | `102d0c78bb57339ccf110b9da721f005c83ad88d5a32901d6c676b90376ddf01` |
| `candidate_scheme.rs` | `e2b6209e3bf486a302e52e5051be60bf7cd8187a7a1e8453087b94f77e06b814` |
| `shadow_apply.rs` | `2fa42a5570e660babab5da6361e0d71e0c022b234a21f7e01b78eafbfc65f278` |
| `lib.rs` | `429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be` |
| `candidate_context.rs` | `a6e8bde3a187369ddf847a31f2ae6eb443434a34d819e44a7fc72c9788809905` |
| Annotation integration authority | `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18` |
| Inference principles authority | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |
| Design authority | `e4055100f6e75b9c8a6294ec6c68643d8677d7b35b45e430450f7e2c2ad97eb1` |
| Sprint rules | `f2e01e3c33dc13d6c5cb77a66e7c5f0de15f08669f5a47fef0d6cb5c914da3a5` |
| Handoff protocol README | `0f829876325565f3c42fbf1950d01deef8c6fda4e92989f668ce1adada41efd6` |

The three required Rust base hashes match the contract exactly. Authority
documents were read at their current paths and authenticated to the contract's
hash prefixes. `candidate_call.rs` is packed locally; its full committed blob
was not decoded. Its relevant field uses are visible in the authenticated
constructors below. This does not claim a complete call-registration audit.

## Actual construction and native evidence

1. `lib.rs:865` derives `Clone` for `ConstraintBatch`; its HIRs and collection
   identity are retained through `Arc` fields. `InferenceSession` owns its batch,
   store and candidate graph (`lib.rs:7933`). `try_new` constructs the store and
   moves in the batch (`10087`, `10122`); `try_new_candidate` starts a candidate
   graph (`10501`). Thus cloned batches can preserve source identity across
   distinct sessions. Source identity alone cannot distinguish those sessions.

2. `candidate_effect::candidate_formal_entry_annotation` (`1763`) reads the
   registration through **self.batch**, validates its computation role,
   annotation owner/scope, parameter recipe and actual source Lambda/parameter,
   and rejects duplicate retained permissions (`1766–1783`). It retains the raw
   entry row, exact source positions and concrete source operands, then publishes
   into **self.candidate_graph**'s effect state (`1792–1822`). This is actual
   common-owner construction of permission and registration. Concrete permission
   alone supplies neither inflow nor a Catch consumer.

3. `candidate_context::LambdaArgumentEffectOrigin` (`247`) retains registration,
   Lambda occurrence, original Function term and raw entry endpoint.
   `retain_lambda_argument_effect`'s body at `1648` publishes those fields into
   its own state's origin list. Capture reads that list through
   **capture.session**, selects the exact captured positive Function endpoint,
   follows Function child 1, and checks its captured row against the current
   canonical representative of the raw entry (`candidate_scheme.rs:2957–2989`).
   Frozen patch lines 1686–1708 additionally copy that raw entry into
   `LambdaArgumentEffectCapture.entry_effect`; raw and canonical rows remain
   distinct coordinates.

4. `prepare_candidate_fresh_use` obtains its use ordinal from this session's
   effect-context `begin_use` (`candidate_scheme.rs:4444–4447`). That method
   increments a state-local `uses` counter (`candidate_context.rs:3539`). FreshUse
   checks the captured Function/child/row incidence and takes the mapped row
   from the one shared fresh row vector (`candidate_scheme.rs:4529–4553`). Patch
   lines 1747–1754 carry the raw entry alongside that mapping. Route construction
   moves this graph, row vector and retained maps together into
   **self.candidate_graph.routes** (`4930–4975`). Those producers provide useful
   within-session evidence; their ordinals are not global session identities.

5. Native extraction (`candidate_scheme.rs:451–492`) checks the positive Function,
   child index, graph row, retained mapped row and the Function's actual native
   argument-effect term in the supplied arena. This establishes a structural
   correspondence for the **route/store pair**. The patched wrapper does not
   extend that arena ownership to the separately supplied effect state.

6. `candidate_effect::State::bind_formal_entry_permission_use` (`397–440`)
   selects a unique permission by registration and compares computation role,
   raw entry ordinal, parameter, formal, source owner, scope, occurrence and
   nonempty concrete payload. It borrows permission fields from `self` while
   accepting mapped row, definition-use reference and context-use ordinal from
   its caller. `State` has a private `brand` (`155`), but this binder neither
   compares it nor receives the route's session brand. The patched scheme
   wrapper consequently cannot infer common ownership from this successful call.

## Exact conditional cross-session falsifier

Let distinct sessions A and B start from cloned copies of one collected batch.
Assume both reach an authentic computation-entry permission and corresponding
route incidence for the same source Lambda, with equal registration and raw
entry ordinals. Use an authentic route and native store from A, and B's retained
effect state and formal-registration slice. Supply the shared source occurrence
and incidence registration.

The frozen wrapper's native extraction runs entirely on A. Its equality checks
compare incidence registration/Lambda with supplied source coordinates; its
definition-use and context-use checks compare values reconstructed from the
same A route with that A route again. The effect-state call runs entirely on B
and compares B's permission/registration against the shared source coordinates
and equal raw entry ordinal. It accepts A's mapped row and use identities without
an owner comparison. If those stated inputs exist, it returns a record whose
permission payload belongs to B and whose route/use mapping belongs to A.
Using A's arena avoids relying on any foreign-Term acceptance by B's arena.
No guessed native term or manufactured permission is required by this falsifier.

Equal context-use ordinals in A and B are possible under their separate counters
and do not prevent the join; the API does not even consult B's context-use
inventory for the supplied A ordinal. The unverified premise is reachability of
the paired successful source fixture with the stated equal raw entry ordinals.
No two-session execution, test compilation or concrete source result was
performed. Therefore this is a source-qualified **conditional** API falsifier,
not a completed executable counterexample or a whole-language refutation.

## Required repair evidence and retained limits

TODO `R152-OWNER-1`, owner `candidate_scheme::bind_native_formal_entry_permission_use`:
restore a single session-owned entry point that derives route, store, registrations
and effect state from one `&InferenceSession`, or provide a demonstrably common,
unforgeable session owner and reject mismatches before returning a binding.
The exact falsifier is the A-route/A-store plus B-state/B-registration call above.
Merely adding source-ID or ordinal equality cannot discharge this TODO.

TODO `R152-ORIGIN-2`, owners `candidate_formal_entry_annotation`, capture,
FreshUse and the scheme binder: justify every removed check from actual retained
construction. The baseline wrapper also checked unique context origin, original
native negative Effect row, unique Lambda recipe/exact source parameter, current
canonical captured-row association, and mapped native negative Effect ordinal
(`candidate_scheme.rs:518–571`). Carrying raw `entry_effect` is useful producer
evidence; it does not alone prove each deleted check redundant. Preserve those
relations or provide the corresponding explicit source argument in the candidate.

The baseline guard `registered.owner == Definition(route.provider)` (`509`)
cannot be used as a general repair premise: a returned/local Lambda can belong
to a different actual source owner from the module supplying its value. Follow
the retained registration and original Lambda constructor to authenticate that
owner. `route.source_owner` is separately the receiving owner (`4969`). This
packet does not establish completeness for returned/local functions, provider
selection, Catch arm identity, residual propagation or failure publication.
Those remain obligations of the candidate's whole-diff review and their source
owners. `candidate_receiver.rs` and quarantined runtime files were excluded.

Existing hygiene integration §3 is reused only as its stated conditional
transport framework; it requires valid owner/correspondence derivations.
It cannot supply the missing session relation. The prior numeric/source-equality
reasoning is rejected at this boundary. No old hygiene theorem was reopened,
no semantic restriction or Simple-sub bypass was introduced, and no provider,
permission, residual or witness lineage was collapsed.

## Checks, resources and STOP

Checks performed: SHA-256 authentication; read-only authenticated loose-object
source inspection; static branch-by-branch comparison of the frozen binder and
its committed producers. No tests, builds, Lean, new cache/environment, scratch,
worktree, checkout, Git operation, external contact or descendant was used.
One initial `python` read command failed because that executable was unavailable;
subsequent read commands used existing `python3`. No environment was changed.

Budget: 600 seconds maximum; stopped within that envelope. Exact elapsed and
remaining wall time are UNKNOWN because no start clock receipt was captured.
All new paths: this handoff only. Scratch/generated paths: none. Exact exclusive
lease: `tasks/agent-loop/inbox/effect-permission-session-isolation-r152-proof.md`.

Next in-scope step: Luna applies these owner requirements to the independent
implementation candidate and assigns fresh review of its complete frozen diff.
This author supplies evidence and cannot independently certify the combined
result. No further proof-lane stage remains authorized after this submission.

Writer-stop receipt: **STOPPED; all writes cease after freezing revision 1.**
No descendants or unresolved descendant leases. Revision 1 is immutable; its
actual-byte SHA-256 is returned to Luna in the final receipt. Pending review and
integration; no parent closure or production promotion.
