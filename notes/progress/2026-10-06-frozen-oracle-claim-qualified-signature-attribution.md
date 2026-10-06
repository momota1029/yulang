# Frozen Oracle claim-qualified signature attribution

Date: 2026-10-06
Status: frozen research-only historical characterization; independently spec-audited
Yulang3 baseline: `f2525331641089b6eda8805bec8a23c6c4fa3f54`
Frozen Oracle: `a58eefc31e22141574b6f20c6a5748151c6d79f1`, `/tmp/yulang2-oracle-rebuild`
Semantic and implementation authority: none
Method: bounded read-only source archaeology and conditional local inversion
Review: `spec_auditor` PASS, no substantive findings, on note SHA-256 `4be3aa9f13ec1ec55729af2e0d6568bb2a159deba8cf593ffc92be9e0c56c544`; review covers current-authority separation and the cited historical attribution path

## Question and result

The current open producer is original inferred-signature applicability and
contribution licensing: each beta-owned incidence needs a source constructor,
upper contribution, original signature-position correspondence and scope, with
forward construction and exhaustive inversion on one original row. Existing
Oracle archaeology already covers application constraints, formal/frame
grouping, projected signature folding, source-boundary origins, and partial
occurrence provenance. This pass isolates a distinct downstream mechanism:
the historical collector can attach an exact claim-qualified projection
certificate to a generalized structural witness, then validate and explain
that certificate back to its original producer or replay premises.

This is a preservation and attribution mechanism for a selected proof carrier.
It is not the source producer that licenses an original signature occurrence.
The attachment occurs after projection evaluation, and its whole-scheme
completeness is explicitly incomplete.

## Historical dataflow

Locators below are relative to the frozen Oracle checkout.

1. **Projection evaluates an existing lower-bound proof.**
   `crates/infer/src/constraints/proof/mod.rs:10002–10130` validates the bound
   and supporting proof ledger, collects uncovered claimed roots and
   independent supports, then evaluates inclusion with evidence. Missing or
   inconsistent facts, malformed support/formula links, and resource failures
   return explicit errors. The input is an already-produced bound and proof
   state; this is not source applicability formation.

2. **The projection result becomes structural collector input.**
   `crates/infer/src/constraints/structural_kernel/access.rs:862–896`
   exposes `scheme_projectable_lowers_in_scope`. For an included qualified
   lower, `crates/infer/src/generalize/provenance.rs:234–280` attaches
   `BoundClaimProjectionProof(bound, coverage_root, representative_claim,
   proof)` for a decisive claimed arm and separately attaches independent
   supports. It does not substitute the raw mixed bound for the selected
   claim proof. Unclaimed lowers use a distinct raw-bound parent branch.

3. **The certificate retains historical identity.**
   `constraints/proof/mod.rs:2610–2735` distinguishes standalone,
   derived-unary and replay-conjunction certificates. Its key normalizes a
   representative claim to the coverage root, so representative replacement
   preserves certificate identity. The identity names a proof claim and bound;
   it is not a source slot or typed signature position.

4. **Reverse lookup validates before resolving.**
   `crates/infer/src/constraints/mod.rs:2965–3059` checks certificate/bound
   identity, representative/root agreement and proof-ledger linkage before
   returning a claimed-projection carrier. Independent carriers take a
   separate path and require their own ledger membership. Then
   `crates/infer/src/constraints/explain.rs:1410–1563` follows the selected
   certificate to its producer, structural/reduction parent, or exact replay
   premises. Attribution and premise mismatches make the explanation
   incomplete rather than silently selecting another source.

5. **Occurrence provenance exports the filtered witness.**
   `crates/infer/src/analysis/session/occurrence_provenance.rs:251–277`
   retains the filtered `{bound, proof}` root in occurrence provenance.
   Generalization ordering in `crates/infer/src/lowering/expr/tail.rs:982–1011`
   obtains the compact generalized root and captures witnesses before scheme
   finalization and recording. The path is therefore downstream of generated
   constraints and projection.

## Conditional local inversion and limits

Assume successful scoped projection, a decisive certificate, intact ledger
linkage, a surviving structural position and sufficient capture budget. The
collector emits that certificate as a generalized witness parent. Reverse
resolution validates the same certificate and recovers its exact historical
carrier. This proves attribution for the captured parent under those premises;
it does not prove exhaustive original source-incidence coverage.

The historical test `generalize/provenance.rs:1633–1685` checks a mixed lower
with one covered and one uncovered claim: capture retains the uncovered claim's
certificate while excluding the covered sibling and raw mixed-bound parent.
This is an inspected test contract, not a test run or an admitted-source
counterexample. The representation distinction is concrete: replacing the
selected certificate with `Bound(b)` loses the claim lineage. An empty
qualified selection also remains parentless instead of fabricating a raw bound
edge (`generalize/provenance.rs:115–132`).

Coverage is deliberately partial. Whole-scheme completeness is marked
`Incomplete` (`generalize/provenance.rs:67–73`); capture also has structural
survival/sandwich qualifications and finite witness, edge and depth limits.
An included projection can carry `FailOpenIncomplete`, so inclusion alone does
not certify complete attribution. The projection evaluator, certificate and
ledger are one historical proof system, not independent semantic oracles.

## Correspondence to the current missing producer

The useful constraint is narrow: if a future current source constructor emits
an original contribution witness, later structural attachment should retain
its exact witness identity, and reverse explanation should validate its
producer/replay chain rather than infer ownership from equal endpoints or a
merged Function shape. The Oracle mechanism is an example of such
proof-carrying attribution after query evaluation.

It does **not** construct current `Attach_C(X,e,t)` / `Lic_C(X,t)`, a complete
original `beta/Slots(beta)` profile, typed owner/receiver/path incidence, the
original correlated `(nu,K,D)`, Q-independent admission, or both licensing
coverage directions. Because attachment consumes already evaluated
projection evidence, it cannot be used as the pre-query source constructor
that the current gate requires. No Oracle semantic behavior, source acceptance,
language meaning, solver correctness, soundness, principality, source adequacy
or production authorization follows.

## Inspection record

Oracle HEAD was verified as the pinned commit. SHA-256 of the inspected source
files:

| File | SHA-256 |
|---|---|
| `constraints/proof/mod.rs` | `bc0f3fbcf8f5ed01245e74283d3fd9cb13aa1713aff252a1847fde76b11b8e03` |
| `constraints/structural_kernel/access.rs` | `ad90bc1444be22df6080c7131ef49fedace884178c375af84ecb09416b38740f` |
| `generalize/provenance.rs` | `83859368c64d27abb5896f1efc491b7fd616adf893b03d36d99b8f57da1792e0` |
| `constraints/mod.rs` | `ad3cf5fd60462cb1a08ef1a5d6fc57c4fd640148597bc3b331d09729616d8392` |
| `constraints/explain.rs` | `1138c38113654d1831d3b2e84362c05bbeba97a5f3d7186f4003f4747ec5d4e1` |
| `analysis/session/occurrence_provenance.rs` | `90613e12e904c74d40894e6f395162c358cc632a8aecb9ddc55db542dd897268` |
| `lowering/expr/tail.rs` | `ac406b309fbb0ba558a18e37aba63a8e7ffeabbc377a111566b1f97d786f93b8` |

Checks were bounded source-window reads, `git rev-parse` of the frozen Oracle
checkout, and SHA-256 hashing. No Oracle execution, build, test, benchmark,
compiler edit, or Git mutation occurred. This note is not independently
reviewed; its claim is limited to the cited historical mechanism.
