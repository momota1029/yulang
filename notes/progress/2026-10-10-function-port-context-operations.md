# Function-port context operations checkpoint

Date: 2026-10-10
Branch: `research/simple-sub-intrusion`
Baseline: `3c42971ea6f53604537cf2c66ed3873f94ee248b`
Status: reviewed source-owned Function context construction; nonidentity
execution, recursive lifecycle certification, and cutover remain open

## Scope and authority

This implementation follows the Authoritative
[contextual attachment/admission design](../design/2026-10-10-contextual-attachment-admission-design.md)
§§3–7, especially §4 Function ports and positive wrappers. It does not add a
new language decision or enable concrete negative formal rows, `BothFromRight`,
recursive nonempty contexts, or public/default inference.

## Construction

Function-child admission now starts from the exact processing parent relation
and its post-check context. Argument Value and ordinary Argument Effect apply
`Swap`; Result Value and Result Effect preserve the context. A supported
child-local closed positive wrapper prefixes its weight outside that inherited
operation, matching the frozen Oracle operation order. Identity Swap may be
omitted structurally while retaining the exact `FunctionPort` incidence and
parent relation. Unsupported child-local constructors remain unavailable.

Focused regressions cover all four fields, identical endpoints with different
parent contexts, child-local prefix ordering, provenance retention, unsupported
execution, rollback/retry, and retained-byte accounting.

## Proof route and review

The active collaboration schema omitted `prover`, so the primary used the
configured `tools/codex-prover.sh` fallback. Its fresh Codex session registered
project roles and the session JSONL records an actual
`agent_type="prover"` child, `/root/function_port_proof`, requested at
GPT-6.1 Sol/high. Effective model and effort were not exposed. The resulting
[conditional ordered-port derivation](2026-10-10-function-argument-effect-contravariance-proof.md)
proves only the primitive context-expression order under its stated wrapper
and transition hypotheses. Independent compiler-referee review confirmed the
algebra and bounded frozen-source bridge; its minor Function-locator finding
was repaired and primary-checked. The note remains conditional and does not
establish arbitrary effect hygiene, source reachability, complete execution,
soundness, principality, or cutover.

An independent spec-auditor review of the implementation found no findings.
The reviewer checked exact parent provenance, argument/result operations,
prefix order, unchanged unsupported/certificate gates, and the focused tests.

Verification:

- `RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo test -p yu-solver --features shadow-apply-candidate --lib candidate_context -- --test-threads=1` — 77 passed.
- `git diff --check` on both implementation files and the proof note — passed.
- No broad test suite, build, benchmark, or performance measurement ran.

## Remaining gates

The current consumer still rejects nonidentity operation contexts. Source PUSH
generation and use, mixed-component propagation, exact two-cycle recognition,
late-edge invalidation, publication deferral, certificate rollback/retry,
contravariant concrete attachment formation and checks, complete Call,
ordinary inference, soundness/principality, and F5 replacement remain open.
