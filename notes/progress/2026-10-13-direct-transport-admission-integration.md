# Direct transport source-admission association integration

Date: 2026-10-13
Status: bounded private implementation; independently reviewed and compile-checked
Baseline: `8d90a83e5aa3c7035c799aa2fbb2b833256525a3`
Branch: `research/simple-sub-intrusion`
Mode: M1; one semantic referee plus mandatory pre-write assertion conformance review
Runtime verification, joint opposite-pair disposition and F5 cutover: OPEN

## Authority and completed correspondence

Top-level inference principles §§2–4 and contextual attachment/admission §§3–4
require retaining known construction evidence and preserving its provenance.
The [direct association proof](../theory/2026-10-13-direct-transport-admission-association-proof.md)
derives a finite exact admission prefix from the actual group, snapshot and
transform constructors. Fresh independent proof review passed with no findings.
Architecture adjudication confirms that this bounded internal repair selects
no new language meaning, source restriction or authorization rule.

The operation's existing immutable source snapshot already freezes admission
and emission heads. Its actual returned transform ID already identifies the
source/destination bound and fiber. No new arena, stored field, copied payload,
global inventory or reconstruction from endpoint shapes is needed.

`BoundAdmission.origin` is a processing `TypedPairKey`. It is distinct from
the contextual occurrence-bearing Origin and effect OperationOrigin. Reading
this association supplies no source-authentication or operation-field map.

## Implemented owning code

In `candidate_context.rs`, the private `BoundEvidence` reader takes the actual
`FiberTransformId`, validates its snapshot and exact source admission head,
then borrows only the saved predecessor chain. Each result contains the source
admission ID/record and the actual transform. Duplicate admissions and several
origins on one fiber remain distinct. Missing and inconsistent references are
distinguished; mismatched keys/groups or non-descending links yield no false
association. The reader does not consult current group heads or the latest
transform indexed by child relation.

The transform constructor inherits the entire source coverage value. A valid
nonempty exact admission prefix suppresses only the newly added
`MissingOriginAssociation` bit. Every inherited gap remains, including an
inherited association gap. Missing/mismatched/transformed-only source evidence
still receives the local gap. Admission and physical-emission evidence remain
separate.

The operational origin-table loop's `relation=None` fallback remains gapped:
it does not carry the exact source-fiber association retained in these records.
Executable bound/relation/context/dependency/replay behavior, FreshUse and
canonicalization, readiness, journals and persistent layouts are unchanged.
The borrowed reader remains private to `BoundEvidence`; there is no State or
CircuitEvidence consumer integration and no authorization consumer.

Records and IDs are local to the owning live State/route. A borrowed traversal
cannot overlap mutation or rollback. Retired or cross-State numeric IDs and
stale imported snapshots are outside the proved lifetime; numeric equality
cannot authenticate them. No new epoch or durable external handle is added.

## Assertion protection and reviews

The existing two-fiber extrusion test creates two exact nonempty admitted
source prefixes. Its old unconditional association-gap assertion described
the historical implementation, while canonical admission records retain the
direct association. Mandatory pre-write `spec_auditor` review approved only
replacing it with equality to the frozen source coverage. This enforces every
inherited bit and preserves all other snapshot, dependency, interning, append,
accounting and rollback assertions, test name and fixture.

One semantic `compiler_referee` reviewed the frozen implementation against the
independently reviewed source law, with no findings. No additional performance
review was triggered: constructor/head validation is O(1), borrowed traversal
is O(Avisited), cursor space is O(1), and there is no heap allocation, payload
clone or persistent size change. Repeated queries can revisit prefixes; no
amortization or cache claim follows.

## Exact verification and limits

Primary checks passed without warnings, sequentially on the frozen code:

- `RUSTC_WRAPPER= cargo check -p yu-solver --features shadow-apply-candidate --all-targets -j 2 --offline`
- `RUSTC_WRAPPER= cargo check -p yu-solver -j 2 --offline`
- `git diff --check`

All-target compilation compiles test configurations; it executes no tests.
No tests were added or run. Exactly one existing assertion changed after its
pre-write review. No runtime query/failure/rollback probe, broad suite or
benchmark ran. Two scoped Cargo processes; zero measured samples. Artifact
links, fences, whitespace and baseline/current code hashes are checked by the
primary; record-only changes require no repeated build.

Frozen reviewed code SHA-256:

```text
bbc54b0624a31569271412269dfec70ce75d4bbfc4fa74f3df64590d732c29d4  crates/yu-solver/src/candidate_context.rs
90830adbadfdc58f4449d66a2c442cd117150e8ecef2d51760ce2f2e21154e7a  crates/yu-solver/src/candidate_context_tests.rs
```

This consumes the direct association proof at its constructor/reader owner.
It does not close multi-hop or fresh-use association, original physical
incidence coverage, joint opposite-bound context disposition, source/Car/Call,
effects, L4, soundness, principality, production routing or F5. Those original
owners and gates remain OPEN. The next bridge must consume the actual retained
association at its particular source/transport/consumer seam; it cannot infer
completion from an endpoint, an ID, a coverage bit or successful compilation.
