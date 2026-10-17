# Specification review: ordinary HIR applied-conformance repair

Sprint `ordinary-hir-applied-conformance-repair-20261017` rev4. Fresh reviewer
`/root/ordinary_hir_repair_spec_review` (`spec_auditor`; requested
`gpt-6.1-sol`/low, observed runtime/model/effort unavailable) STOPPED. Exact
elapsed unavailable; conservatively charge the 120s cap. Static source,
contract and test inspection only. No Git, tests, builds, Cargo, formatting
probes, network, descendants or reviewer writes. Luna transcribed this receipt
from the reviewer's final message because the reviewer role was read-only.

**MAJOR — execution coverage gap.** The two prescribed Cargo commands select
integration targets and do not execute library unit tests in
`crates/yu-hir/src/module.rs:3078`, `:3160`, and `:3182`. Neither integration
target independently checks conflicting root mappings, final private
`evaluation_class`, or the 64-binding indexed-finalization counter. The sprint
contract requires falsifying regressions for every repair finding, including
the many-bindings discriminator; adopted successor §8.3 requires conflict
rejection. These assertions are authored but would remain unexecuted under the
frozen command plan. This is an execution evidence gap; static inspection found
no implementation/spec conflict. Primary must adjudicate and record focused
execution evidence or keep these properties explicitly unverified. Do not
silently infer coverage or change the frozen commands.

No other actionable spec conflict found within scope. Static conformance review
found construction-owned source provenance, parse-owned keys, refusal before
operand resolution with causal errors retained, duplicate-before-operand
diagnostic order with dense final IDs, validate-before-append finalization,
final classification recomputation, one flat Apply error list and Group
forwarding. The stated O(V+E+R) resource account remains within the adopted
correction and its exclusions. Grouped unresolved-name expectations match the
adopted successor; no expectation weakening was found. Original parent claims,
quantifiers, source domain/native correspondence, Call, F1/FK1, N-Transport,
soundness, principality, termination and production remain OPEN.

All 12 supplied SHA-256 pins matched exactly: contract, plan, invariants, six
code/test inputs, shared handoff, adopted grammar and resource amendment. No
mismatch. Review did not inspect Git diff or run target commands; it does not
certify exhaustive diff absence or runtime behavior.
