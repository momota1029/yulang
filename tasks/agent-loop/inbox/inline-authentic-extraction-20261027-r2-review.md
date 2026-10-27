# Independent review: INLINE-AUTHENTIC-EXTRACTION-20261027/r2

Reviewer: `/root/inline_authentic_extraction_r2_review`, fresh non-author.
Review was read-only; it performed no Git operation, Cargo, Lean/Lake, tests,
formatter or descendant work. The reviewer returned this report to Luna for
persistence.

**Verdict: no BLOCKING, major or minor finding for the exact frozen finite
fixture.** Accept the result as an executed, authenticated frontend trace with
a valid finite Lean consumer. It establishes no original allocator, universal
frontend refinement or whole-language result.

## Independently matched frozen evidence

| Artifact | SHA-256 |
| --- | --- |
| Contract rev6 | `a650bdbd86b3b88fe18d7b1200e4303b7237e3db4863411d075b11891529fbde` |
| Extractor `main.rs` | `fc22f1ab490e815a800a6b1e91eb4ea978006d6956ac838329cddf7b09ad1472` |
| Implementation handoff rev5 | `976fc2b754263b3afb534dfcc32e1e00895269036f0378fc3c732cce0de345b9` |
| Generated trace | `73a4a8aa65e5d7d44611a70e52b9d2b6ac5940c2292a7c06e01e69834f2ac5e3` |
| Lean consumer | `ed25ec65c5760e4a523fabe75f392c67476a710d3af60e345c07e5bf5eaeeb09` |
| Audit | `85e0dd8adcef88c9e10c6aebde526dcb2340a1f58e03a67a5dd4e903f08ad089` |
| Proof handoff | `d0a8da28f7bca9d9055dd4840ef7dfdad9a91aae55378b13e4bd9e152c555612` |

All 28 inherited r1 input pins match. The isolated manifest, lock and metadata
graph match; all 22 registry `(name, version, checksum)` tuples match the root
lock. The isolated graph has 26 nodes and no `yu-solver`. Commit/baseline identity
strings were not independently authenticated because Git was excluded.

The implementation call-6 `run-r5.*` hashes match the handoff and the exact
rev6 command. The saved raw stdout reports 8 authenticated expressions, 22
position rows, one Group projection and two ordered body entries. The timing
receipt is `ELAPSED_SECONDS=1.46 EXIT=0`. These are preserved execution receipts,
not an independent rerun or cryptographic runtime attestation.

## Source and trace assessment

The extractor uses `ShadowArtifact::position` and the exact retained position
reference for artifact-table indices; it does not substitute `Position::ordinal`
(parent-child order). It authenticates expression parse keys, HIR occurrences
and occurrence-to-source-key associations, compares registered inline binder
token ranges with `LocalSourceParameter.range`, retains raw Group callee and
each Group-to-inner projection separately, serializes full direct body
incidence, and compares resolved parameter identities before emitting ordinals.
The owner implementations at `local_source.rs:2092–2122`, `source_identity.rs:
152–157` and `shadow.rs:1800–1829` support these joins.

The exact finite fixture records:

- Outer Lambda/binder ranges `(11,35)` / `(12,13)`; outer body is
  `StatementBlock` at `(16,35)`.
- Apply index 3/occurrence 3 is `MlArgument` range `(29,30)`.
- Raw callee is Group index 4/occurrence 4/range `(19,28)`; its explicit edge
  reaches Lambda index 6/range `(20,27)`.
- Inner binder is `(21,22)`; argument Name resolves to outer parameter 0,
  inner body Name to parameter 1, and restored sibling to parameter 0.
- Both direct body rows preserve statement-expression/final-expression kind,
  order, index, occurrence, range and source position.

The Apply range is genuinely the `MlArgument` tail `(29,30)`, not a full
callee-containing call span; this agrees with `local_source.rs:1982–2020` and
`shadow.rs:1765–1767`. The consumer asserts the recorded tail convention and
does not claim callee containment. Inner-body Name range `(25,27)` includes
trailing whitespace; only binder-token ranges are equated with bytes for `x`.
Relevant inline-lambda, exact-origin, shadow/restoration, missing-source and
foreign-owner tests were inspected but not run.

The fixture has no binding-statement initializer, Sequence instance, annotated
or computation/record/unit formal, multiple Group edge or arbitrary source
form. Those cases remain in the parent domain and are not claimed by this finite
result. The generic binding-row serializer omits initializer incidence; that
does not invalidate this fixture, but other fixtures need a reviewed schema
extension.

## Lean audit

The consumer declares twelve finite theorems:
`input_byte_length`, `all_position_ranges`, `exact_binder_bytes`,
`binder_position_rows`, `group_projection_incidence`,
`group_range_contains_projected_lambda`, `apply_tail_range`,
`complete_direct_body_incidence`, `exact_name_resolution_rows`,
`names_have_source_positions`, `shadow_and_restoration_snapshot`, and
`foreign_report_inventory`. The reviewer independently inspected statements,
proof terms, both successful complete type/axiom logs and the retained first
failure. Each declaration has a complete empty transitive axiom report in both
successful logs.

Receipts match: check 1 failed (1, exit 1, 3.164s); check 2 passed (exit 0,
2.676s); delivered audit passed (exit 0, 2.519s). The proof handoff contains the
delivered audit stdout verbatim. Isolated copies equal submitted files. Lean
4.35.0 and Lake 5.0.0 are pinned. Source-cone manifest SHA-256 is
`243f41ff5b9ff1f3110c34d74c09bb5e6691a7d7a8e31e2b7dd97ddfd68eb396`; all 656
entries (3 project and 653 toolchain modules) match, with no unresolved listed
imports. No checker was rerun and no root/default-target integration build is
established.

The literal Bool flags are data. `foreign_report_inventory` proves only the
four emitted strings, not Rust rejection. Runtime assertions and owner checks
are supported by the inspected source plus execution receipt, not by those
Lean string/Bool theorems. The consumer states this boundary explicitly.

## Parent application and remaining gate

`OriginalIdentityRealization.Identity` requires declaration, ambient scope
entries, Context, Lambda/formal/admin-wild/Name Sites and Name. The inspected
`OriginalIdentityEntryOrigin` equations accept that already-supplied Identity;
they do not construct it from Rust ownership. No original allocation equation
is supplied here, so no specialization is justified. Runtime labels or
serialized ordinals cannot fill this gap by convention.

The next owner is the original-source/frontend interpretation lane, which must
construct the complete original tuple and prove its source, lexical, scope,
Apply/argument and Group-projection equations. Original allocation, universal
refinement, A/B, soundness, effect hygiene, principality, progress/termination,
complete Call, source/native, receipt/admission, whole-language and production
gates remain **OPEN**.
