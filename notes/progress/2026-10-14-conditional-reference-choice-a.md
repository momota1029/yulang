# Conditional references: approved Choice A

Date: 2026-10-14
Branch: `research/simple-sub-intrusion`
Baseline: `c34723114aee241a7dc1237b78b01a3b3e918d3e`
Status: declared implementation and bounded theorem complete after independent review
Mode: M1, one combined semantic/code/proof reviewer; zero timing measurements

## Authority and implementation

The user explicitly selected `Aですね．` after the corrected A/B explanation.
The [conditional-reference design](../design/2026-10-14-conditional-value-references.md)
records that approval. `candidate_value_graph.rs` now constructs one shared
fragment for each If and links its actual Expression Value to that fragment.
Every condition, branch and explicit else contributes through direct
Name/Apply/If children. Apply fragments also follow direct If children.
Existing Group/Ascription/Lambda/Block boundaries, definition ownership,
call events and the SCC consumer retain their contracts.

No edge enters an Expression Value. Accordingly this extension changes
outgoing reference ownership but leaves current semantic Value SCC membership
and original event qualification unchanged. It does not introduce an identity
alias or claim a new observable intrusion result.

## Proof and review

The [projection derivation](../theory/2026-10-14-conditional-reference-projection.md)
connects first-semantic-endpoint selection to helper contraction, SCC membership
and the actual HIR/graph construction. It also accounts for linear retained
entries, edges and incidence work, with identity-payload/hash costs explicit.
It reuses the established activation theorem at its qualification interface.

The fresh independent `compiler_referee` accepted the frozen code/proof
combination with no blocking or major finding. The primary accepts the bounded
projection, SCC/qualification and cost conclusions. One minor verification
gap was addressed with a conditional-callee test and explicit source-carrier
limits: Lambdas are synthesized only for definition parameters, so no direct
Lambda-child source fixture is available. The callee fixture uses the actual
Group syntax; the direct ungrouped If callee remains statically covered by the
symmetric child loop and projection proof. The final test-only delta was
inspected by the primary; no production change or new panel followed. The original
source-global applicability, typing preservation, principality, effects/hygiene
and production/F5 gates remain open.

## Focused verification

Each command below used `CARGO_BUILD_JOBS=2 timeout 300s`, with Cargo invocations
serialized and `--test-threads=1`.

| Command (after `cargo`) | Result |
| --- | --- |
| `test -q -p yu-solver --features shadow-apply-candidate --lib candidate_value_graph -- --test-threads=1` | 7 passed |
| `test -q -p yu-solver --features shadow-apply-candidate --test candidate_conditionals --test candidate_intrusion_observation -- --test-threads=1` | 10 + 3 passed |

The new cases cover actual resolved identities, both Boolean constants,
nested If/elsif/Apply, a direct If call argument, a grouped If callee with its
original receiver identity, wrapper boundaries, nested
initializer ownership, semantic SCC membership and qualification. The initial
Block fixture used unsupported inline braces; correcting it to an indented
Block preserved its expected boundary and all assertions. No expectation was
changed to match implementation output.

`git diff --check` passed. A deterministic hash check confirmed that removing
the last added test reconstructs the exact independently reviewed code snapshot;
the production section is unchanged. All four relative links in the new
checkpoint, selected design and updated playground README resolve.
No benchmark, broad workspace rerun or full workspace
test suite ran for this local graph change. The previous cross-layer checkpoint
contains workspace build evidence; it is not a test result for this new diff.
The separate solver-to-core development dependency and conflicting fresh-use
observation test mismatch were not altered or rerun.

## Integration

Primary-owned synchronization covers `tasks/current.md`, `tasks/research-lab.md`,
the design and its index, the playground README and this progress record.
The pending negative-formal question bundle is excluded from this checkpoint.
Effects/handler research is an independent lease and is not part of the
conditional implementation's completion claim.
