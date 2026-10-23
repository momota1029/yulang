# CB-PERMISSION-TRANSPORT-20261024

Status: ACTIVE under the existing type-inference/evaluator goal. This sprint
constructs the missing callback-result permission transport, then implements
only the reviewed construction in the already identified runtime owners.
The original Simple-sub A/B claims, quantifiers, source domain and
`SOURCE-SAFETY-BRIDGE` remain unchanged and open.

Branch: `research/simple-sub-intrusion`; baseline:
`a0dcc92b8f8b866f7ed2e06acf399a4c86057a3c`.
Selector boundary: sprint-end recommendation by `/root/next_action_selector`.

## Fixed outcome and authority

Target only the approved callback behavior:

```yu
my relay(cb: () -> [signal] int) = catch cb() {
    signal::ping(), _ -> 1,
    v -> v
}
my answer = relay signal::ping
```

The approved annotation policy requires result `1` for the callback case.
`[signal]` grants handling permission at the contravariant formal result
position; it is not a closed upper bound on callback input. Additional
`write` inflow remains outward. The computation-form thunk, arbitrary
callbacks/aliases, wildcard permission, scoped release, broader
source/native coverage and the original A/B are outside this outcome.

Before: source candidate permission `FormalPermission` retains the nested
`[Result]` row, but the reviewed runtime has no callback-result receiving
view. The relay Lambda is Value role with no `RootCompSchema`; its operation
invocation returns before `OperationResultConsumer` emits the request under
the restored relay owner. The reviewed obstruction is frozen in the pinned
evidence below.

Success requires all of the following:

1. A constructive source/runtime forward simulation transports the exact
   annotation owner, formal, Lambda, annotation coordinate, row coordinate,
   structural `[Result]` path and resolved family into the actual receiving
   relay invocation and callback Result execution view.
2. A frame invariant proves when that view opens and closes and that it
   authenticates the same request event `q`, view/port, and Catch owner after
   the operation invocation unwinds and `OperationResultConsumer` executes.
   Treat callback-call, operation-invocation and handler-owner identities as
   distinct.
3. The proof handles request bubbling, delimiter unwinding, discarded
   continuations and replay. Existing immutable view/template machinery is
   evidence to inspect, not an assumed solution.
4. A fresh non-contributor review accepts the frozen construction before
   Luna writes code. Then the three leased runtime owners implement the
   reviewed transport and same-Catch consumer. A later independent review
   accepts the frozen diff.

This is a proof and implementation target, not authority to change accepted
semantics. A missing grant remains no negative protection fact. No sibling
invocation, type equality, family spelling or receipt without a matching view
may grant the Catch.

## Frozen inputs and baseline owners

Approved policy: `notes/design/2026-10-10-annotation-effect-hygiene-integration.md`,
SHA-256 `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18`,
§§1.1–1.2.

Reviewed exact obstruction:

- `notes/theory/2026-10-24-callback-permission-bridge.md`,
  SHA-256 `c228ff45a272a52b92eaaccd91183272438bb8c3287dd39e7749d700ce919f4d`.
- `tasks/agent-loop/inbox/20261024-callback-permission-bridge.md`,
  SHA-256 `dddd305fb7d0aa6aca86b0868cf1a4806703e58e57f7c8b8e2e14ac0c5949335`.
- Its 15 policy, manuscript and owner dependencies were hash-checked by the
  fresh reviewer; the exact list and hashes are in the proof artifact.

Current source/runtime owner hashes at this sprint baseline:

| Owner | SHA-256 |
|---|---|
| `crates/yu-hir/src/module/source_annotation.rs` | `409ce491bc216c6963bf76d20810790aa2756edf260ecc35e76d5cfc05d24b3f` |
| `crates/yu-hir/src/module/local_source.rs` | `7055975d582dfb198836c2aa659f8b8033c29dff419d522feea4fea4c42523d1` |
| `crates/yu-solver/src/candidate_source.rs` | `57b119592a6a8d4afd42aca10c5e2bb749cfdf0fb0fdea967dd437d552a1a04e` |
| `crates/yu-solver/src/candidate_effect.rs` | `70c42056a1041d54f88f16d7712875e3acf9ef7649b99a34bc990ff19f04936f` |
| `crates/yu-solver/src/shadow_apply.rs` | `f8d92f2d59353e5b9cda014545b352c8d6356cc0aff3b4eeae0e81893e78202d` |
| `tools/inference-playground/src/runtime/program.rs` | `df58f9a1d60e39fafe6d85b1e50331b35fde2a9142a2eaea84ad028d3048fdb0` |
| `tools/inference-playground/src/runtime/receiving.rs` | `2170a3bcbc6710ce3fbf721a05129117f8266b9ecf21c67136db918815303551` |
| `tools/inference-playground/src/runtime/machine.rs` | `d993905eacc0c22f4f371a7a97cf3f3d4a48434fe1538976fba0739107e8f647` |
| `tools/inference-playground/src/runtime/continuation.rs` | `194e925c2e19816e05e8d0cdf773123f205dce47d36d83a70385daa07a77e2b3` |
| `tools/inference-playground/src/runtime/primitive.rs` | `eb0a53bfec8ce2854adbe6342c984d5140fd1585d91da5a8a9739d2ac96e8a85` |

## Lanes, exact paths and review gate

### Constructive proof — `/root/callback_permission_prover`

Exact write paths:

- `notes/theory/2026-10-24-cb-permission-transport.md`
- `tasks/agent-loop/inbox/20261024-cb-permission-transport.md`

Inspect current owners read-only. Construct the transition and frame
invariants, or return the exact failed premise with a falsifier. No production
code, tests, builds, probes, Git, descendants or additional output paths.
Freeze both artifacts, pin inspected hashes and report cessation/resources.

### Implementation and integration — Luna `/root`

Exact code write leases, gated until fresh review accepts the proof:

- `tools/inference-playground/src/runtime/program.rs`
- `tools/inference-playground/src/runtime/receiving.rs`
- `tools/inference-playground/src/runtime/machine.rs`

Candidate/solver owners remain read-only. If a required producer or semantic
decision lies outside these paths or the approved policy, stop and return for
a versioned contract before writing. Preserve Value entry, open effect inflow,
family-specific permission and inherited unknown coverage.

Luna assigns a fresh non-contributor to the frozen proof before code writes.
After the code is frozen, obtain independent review of the implementation.
No producer or primary self-certification.

## Falsifiers and verification

- The permission view ends at `ReceiverReturn` before
  `OperationResultConsumer` emits `q`.
- A sibling invocation, another view of the same callback, or a foreign Catch
  owner borrows the grant.
- Result permission leaks into argument preparation or grants `write`.
- Capture, resume, discard or replay changes historical evidence identity.
- The implementation derives authority from type equality, family spelling,
  or missing-grant forwarding.

After accepted code, Luna may run one
`cargo check -p yu-hir -p yu-solver -p yu-playground`. This sprint authorizes
no tests, expected-output changes or runtime probes. A passing check is only
compile evidence; no execution result is claimed.

## Resources and stop conditions

- At most 3600 active seconds total; no prior budget carries over.
- Proof assignment at most 1200 seconds; each independent review at most 300.
- Implementation, one cargo check, review and integration share the remainder.
- Assignment envelope 6 including the three UNKNOWN reservations; retain their
  quarantined reservations. Zero Astra and no descendants.
- One heavy compiler process, owned by Luna.

Stop at a reviewed implementation checkpoint, an exact proof obstruction,
semantic ambiguity, a new owner/lease dependency, budget limit, user STOP or
session end. Keep `SOURCE-SAFETY-BRIDGE` OPEN_REVIEW unless its original
broader obligations independently close.
