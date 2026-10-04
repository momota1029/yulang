# Experimental SCC-intrusion transport gate

Status: Authoritative
Scope: isolated experimental implementation of finite graph parent/use transport
Approved-by: user, explicit experimental-implementation permission on 2026-10-04
Approved-at: 2026-10-04
Drafted-by: primary
Reviewed-by: architect, compiler_referee
Supersedes: none; narrow exception to the redesign charter's no-implementation boundary
Implementation authority: this test-only research gate; no production routing

## User direction

The user permits experimental implementation before the complete soundness and
principality proofs close, provided no known source counterexample exists and
the experiment is guarded by explicit invariants, differential tests, and
rollback. This permission does not authorize replacing the production inference
path while the remaining soundness/principality gates are open.

The chosen test-only transport gate was reviewed by an architect and a
compiler referee; the user's explicit permission supplies approval for this
bounded experiment.

The experiment below implements only the already-stated conditional parent/use
transport operation. It does not select which source identities are local,
which bounds belong to a member, or how a member root is generated. Those are
inputs to this operation and remain separate proof obligations. The known
one-polarity erasure counterexample is not included as a rule: the transport
operation retains every supplied obligation and every Function port.

## Bounded implementation gate

Add a `cfg(test)`-only graph transport module under `crates/yu-solver`. Given an
immutable finite graph, an exposed root, a complete disjoint partition of
member-local identities and fixed anchors, and the selected ordered bounds,
the module constructs (1) one parent-renamed view and (2) independent
per-incoming-use overlays. It is a transport prototype; no production
`InferenceSession`, `SolvedModule`, or `yu-types` behavior calls it.

The implementation may preserve opaque evidence/provenance as an immutable
association with each supplied bound. It does not certify evidence validity
after transport or infer identity equivalence between current separate value
and effect ordinals.

## Invariants and falsification conditions

1. Retain every supplied bound, its endpoint direction, ordered provenance,
   all endpoint nodes, sharing, recursive back-edges, and all four Function
   children. No polarity-based erasure or bound simplification occurs.
2. Map each local semantic identity once across all its occurrences. Every
   fixed anchor remains unchanged. The input partition is complete and
   disjoint; reject malformed partitions before returning a view.
3. Parent identities are injective and fresh against all source identities,
   anchors, and receiving-namespace identities. Each use overlay is fresh
   against that whole namespace (including caller/context identities, source
   identities, fixed anchors, and parent ports) and every other use's range.
4. Reuse of an identity within one graph remains shared; distinct identities
   do not alias. Recursive graph structure remains finite and regular.
5. The source graph is immutable. A failure returns no partial parent view or
   use overlay.
6. Differential checks compare each transported graph, after inverse
   renaming, with an independent whole-graph copy-and-substitute reference.
   Include one and multiple uses, cross-use constraints, shared diamonds,
   fixed anchors, recursive bound cycles, all Function ports, malformed
   partitions, receiving-namespace identity collisions, and simulated
   allocation failure. Mutating a test overlay must not change its sibling or
   source.

Any identity capture, dropped constraint/port, lost recursive edge,
cross-use mutation, source mutation, or partial publication falsifies this
gate. No source counterexample to identity-only transport is known; the
implementation must not interpret this as evidence that production root
selection or source generation is adequate.

## Owner, entrypoint, consumers, cost and rollback

The current production owner remains `InferenceSession` in `yu-solver`; its
replacement boundary still includes SCC execution, generalization, incoming
use handling, and result projection. This gate is deliberately outside those
entrypoints. Its only consumers are focused Rust unit tests, and it has no
production hot-path cost.

Expected graph traversal cost is linear in the materialized graph and bounds
per view/use; this is a structural estimate, not a measurement. No scaling or
timing campaign is part of this gate.

Rollback removes the test-only module declarations and its source/test files.
The current F5 production path, public APIs, diagnostics, and accepted-program
behavior remain untouched. Passing this gate closes only executable evidence
for finite identity transport; production implementation still requires the
remaining source adequacy, soundness, principality, lifecycle, and review
gates.

## Verification and next gate

Run only the focused `yu-solver` differential test filter and the existing
focused identity/recursion characterization tests. Do not run the workspace
suite at this experimental gate. A `compiler_referee` reviews graph and
identity invariants; a `spec_auditor` reviews the test-only boundary and the
conditional nature of all claims. Stop on any blocking/major finding or a
counterexample to an invariant; repair only that gate and rerun its focused
checks.

The next semantic gate remains the unclosed source-generated member/root
classification and full bound adequacy. This transport experiment cannot
advance production-path cutover by itself.
