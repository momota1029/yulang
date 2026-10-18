# R44 implementation boundary: Application output certificate

Date: 2026-10-19
Sprint: `call-output-owner-jof-20261019-r44`, revision 1
Parent: full inference/evaluator theorem and original Simple-sub A/B, OPEN 0→0

## Recommendation and current code gate

The user delegated selection of the recommended source-owner decision. Luna
selected JOF for a new design-and-proof gate. That selection does not make the
candidate Authoritative or authorize a Rust edit. The exact source rule and
Generalize action still need an independent review and primary adjudication.

**Current result: `NO_SAFE_CODE_SLICE`.** The existing R41 owner map and R42
implementation gate are the source for this boundary. Their bounded evidence
shows structural coordinates already flow through `ApplySourceInput`,
`NativeInterface`, typed Function Result/Preserve and the Context/Dispatch
consumer. It does not identify the new source `Desc`'s owner, cursor or ordered
dependencies, nor prove a typed certificate is retained across each actual
copy.

## Required future code invariant

Once the source rule is Authoritative and its correspondence premises are
proved, the implementation should carry a single typed output-owner
certificate with:

```text
source Application identity
source component and class/sort
original cursor and ordered typed dependency telescope
separate output-value and Application-effect coordinates
complete Call result/provider/world/future and arm interface identity
actual copy lineage at each Generalize/CopyScope boundary
```

The producer is the owning Application source constructor. Consumers are the
source Call/header builder, `ApplySourceInput`, `NativeInterface`, typed Result
propagation and each actual output copy. They must validate the same
certificate rather than reconstruct provenance from endpoint IDs, solver
levels, function shape, source spelling or a successful constraint query.

## Leases and stop conditions

The following dirty paths remain unknown-owner and quarantined:

- `crates/yu-solver/src/candidate_scheme.rs`
- `crates/yu-solver/src/shadow_apply.rs`
- `crates/yu-solver/tests/candidate_local_self_recursion.rs`
- `tasks/current.md` and all untracked R35–R41 artifacts

No Rust, test, expected-output, fixture, build, Cargo or runtime path is leased
by R44. Do not integrate a patch that overlaps these paths until their writer
identity and write cessation are authenticated, the JOF rule has passed its
design gate, and the source/native/copy obligations have a concrete invariant.

The next implementation packet can begin only after those three conditions.
It must then exercise the exact source expression, generated constraints,
propagation, typed Result consumers and evaluator path under the approved
source rule. Passing a focused test alone cannot close soundness, principality,
natural inference, termination or the unchanged A/B parent.
