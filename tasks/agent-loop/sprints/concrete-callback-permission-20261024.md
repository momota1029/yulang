# CONCRETE-CALLBACK-PERMISSION-20261024

Status: ACTIVE under the existing type-inference/evaluator goal. This sprint
targets one already approved callback behavior and its source/runtime bridge;
it does not adopt the source manuscript's global permission candidate or close
`SOURCE-SAFETY-BRIDGE`.

Branch: `research/simple-sub-intrusion`; baseline:
`5fbc2c2d9e3ab28032caf599ca024b8ba8b19778`.
Selector boundary: `/root/next_action_selector` selected this callback
permission bridge as the next bounded source-to-runtime outcome.

## Original claim and exact bounded outcome

The original Simple-sub source/native A/B claims, quantifiers, and accepted
source domain remain unchanged. This packet addresses only the approved
annotated callback case:

```yu
my relay(cb: () -> [signal] int) = catch cb() {
    signal::ping(), _ -> 1,
    v -> v
}
my answer = relay signal::ping
```

The accepted observation is that the local `signal` handler returns `1` for
the callback form. The annotation grants permission to handle `signal`; it is
not a closed upper bound on callback effects. An additional `write` effect
must remain outward. These expectations are fixed by the approved annotation
policy, not inferred from a runtime probe.

The proof outcome is either (a) a bounded source-to-runtime derivation showing
that the concrete permission from this callback-result annotation reaches the
`signal` request made by this exact callback invocation and is consumed by the
`Catch` installed in the same relay invocation, or (b) the exact missing source
constructor/consumer premise. It must track annotation owner, formal, row,
occurrence, structural path, callback invocation, request event, receiving view,
handler owner, and matching concrete operation family. Equal types alone are
not permission evidence.

Only after the bounded bridge passes fresh independent review may Luna change
the runtime path to carry and consume that evidence. The only current code
write paths are:

- `tools/inference-playground/src/runtime/program.rs`
- `tools/inference-playground/src/runtime/receiving.rs`
- `tools/inference-playground/src/runtime/machine.rs`

If evidence identifies a missing producer outside these paths, stop and issue
a versioned contract revision before writing there. A missing positive grant
must not become a negative protection certificate or justify forwarding.

## Frozen authority and dependencies

Approved observable behavior:

- `notes/design/2026-10-10-annotation-effect-hygiene-integration.md`,
  SHA-256 `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18`,
  §§1.1–1.2, especially the callback example and residual `write` rule.
- `notes/design/INDEX.md` locates that policy at Annotation policy §1.2.

Proof inputs (research evidence, not blanket implementation authority):

- `docs/yulang-source-type-safety-ja.tex`, SHA-256
  `2c77bbd6f2679ac91ece3bb670152a9dfd16e033aa68545bff6c6dc509d24166`,
  §§10–11 and §15, especially the unadopted `W-Eligible` candidate.
- `docs/yulang-operational-type-safety-ja.tex`, SHA-256
  `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`,
  the decorated-plan eligibility construction.
- `docs/yulang-dot-selection-safety-ja.tex`, SHA-256
  `47b7fcec1f501e7c326ab9859885e329aab2730066806ea79212e825ebb32b0b`,
  retained only as a neighboring proof input.
- `notes/theory/2026-10-24-permission-implementation-bridge.md`, SHA-256
  `f9c40e49dd8c4e9ec1c4ef01a0391940ad5c7fd21b27da1c0635501721b6aeed`,
  a partial implementation audit; `SOURCE-SAFETY-BRIDGE` remains OPEN_REVIEW.

Current owner snapshot at the baseline:

- `crates/yu-solver/src/candidate_effect.rs` —
  `70c42056a1041d54f88f16d7712875e3acf9ef7649b99a34bc990ff19f04936f`
- `crates/yu-solver/src/shadow_apply.rs` —
  `f8d92f2d59353e5b9cda014545b352c8d6356cc0aff3b4eeae0e81893e78202d`
- `tools/inference-playground/src/runtime/program.rs` —
  `df58f9a1d60e39fafe6d85b1e50331b35fde2a9142a2eaea84ad028d3048fdb0`
- `tools/inference-playground/src/runtime/receiving.rs` —
  `2170a3bcbc6710ce3fbf721a05129117f8266b9ecf21c67136db918815303551`
- `tools/inference-playground/src/runtime/machine.rs` —
  `d993905eacc0c22f4f371a7a97cf3f3d4a48434fe1538976fba0739107e8f647`

The proof producer may inspect the listed owners read-only. No global
`P/P_foreign/Wildcard` rule is adopted by this contract. Wildcard permission,
scoped release, computation-form `thunk` handling, arbitrary callback syntax,
full source/native coverage, and the original A/B theorem remain separate.

## Lanes, leases, and review seam

### Constructive source/runtime proof — `/root/callback_permission_prover`

Exact write leases:

- `notes/theory/2026-10-24-callback-permission-bridge.md`
- `tasks/agent-loop/inbox/20261024-callback-permission-bridge.md`

Construct the bounded derivation from actual source annotations and retained
formal permission to the same invocation's runtime request and Catch consumer.
Inspect the existing candidate/runtime path, not merely the TeX construction.
If the path is absent, report the precise missing owner/transition and why the
other current routes do not supply it. No production code, tests, probes, Git,
descendants, or additional outputs. Freeze the handoff with exact hashes and
writer-stop evidence.

### Primary implementation and integration — Luna `/root`

Exact code leases are the three runtime files listed above. They stay read-only
until the proof result passes fresh review. Then implement only the evidence
transport and matching local-grant consumption needed for the bounded callback
case. Keep candidate solver files read-only unless a versioned amendment adds
a specifically evidenced missing producer.

The fresh read-only reviewer is assigned by Luna after the proof handoff and
before any dependent code write. The same independent reviewer may review the
later frozen runtime diff. The producer and primary cannot certify their own
work. Blocking or major findings stop acceptance until repaired and reviewed.

## Falsifiers and verification

- A sibling callback invocation's receipt or view authorizes this request.
- Type compatibility, a static family name, or a missing grant is used in place
  of the same-event, same-view, same-owner evidence.
- `write` is removed by the `signal` annotation or a handler that does not
  catch it.
- The implementation relies on wildcard permission, scoped release, or the
  unadopted global query candidate.
- The bounded behavior is implemented only by a sample-specific operation
  identity instead of the source formal/occurrence relationship.

After accepted proof-supported code, Luna may run one
`cargo check -p yu-hir -p yu-solver -p yu-playground` and obtain independent
review of the frozen diff. No tests, expected-output changes, or runtime probes
are authorized by this packet. A green check is implementation evidence only;
it does not close the parent source theorem.

## Resources and stop conditions

- At most 3600 active seconds total; no budget carries over from earlier
  sprints.
- Proof assignment: at most 1200 active seconds.
- Each fresh review: at most 300 active seconds.
- Primary implementation, check, and integration share the remaining envelope.
- Assignment envelope: 6 including unknown reservations; preserve the three
  remaining UNKNOWN identities and their leases. Zero Astra; no descendants.
- One heavy compiler process, owned by Luna.

Stop at a reviewed callback implementation checkpoint, a precise proof/source
obstruction with no safe code slice, a new authority or lease dependency, the
budget limit, user STOP, or session end. Keep `SOURCE-SAFETY-BRIDGE` OPEN_REVIEW
unless its original broader obligations independently close.
