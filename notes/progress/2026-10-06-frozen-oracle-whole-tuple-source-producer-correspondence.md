# Frozen Oracle whole-tuple source-producer correspondence

Date: 2026-10-06
Status: frozen, independently compiler-referee-reviewed historical characterization
Yulang3 baseline: `393b77b64cef03e74b3f1e76adb22c2aac5c981d`
Frozen Oracle: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Semantic and implementation authority: none

## Question and result

The current missing source producer must jointly interpret the unannotated
formal's protected inference seed, its ordinary-value refinement, source
argument and invocation, typed incidence, and original shared
`xi=(nu,K,D)`. This note locates the nearest corresponding historical
mechanisms inside Frozen Oracle and tests whether any of them supplies that
whole-tuple producer.

**Result:** Oracle has substantial identity and evidence plumbing across local
formals, generalization, instantiation and sparse source provenance. The
historical pieces are distributed across separate records and consumers; the
inspected paths do not produce a source-owned interpretation corresponding to
current `U_c`/`Delta_formal`. In particular, common variable identity,
derivation lineage, and provenance completeness are not themselves a rule
relating annotation absence, protected seed, ordinary-value refinement,
argument/invocation and typed positions under one current `xi`.

This is bounded correspondence evidence, not a repository-wide absence proof.
Frozen Oracle is not used as authority for current semantics, and no Oracle
behavior is adopted by this result.

## Historical mechanisms located

1. **Formal and use identity.** `infer/src/lowering/local.rs:6–22` retains a
   formal `DefId`, live `TypeVar`, optional Scheme and call/frame state.
   `infer/src/uses.rs:132–138` retains each reference's parent, value endpoint
   and source span. For a monomorphic local, the call/use can therefore reach
   the shared live endpoint. This establishes an identity route, not a
   whole-tuple semantic constraint.
2. **Correlated generalized interfaces.** `poly/src/types.rs:17–23` packages
   quantified variables, residual role predicates, recursive bounds, stack
   quantifiers and a predicate root. These preserve correlated symbolic
   references across a Scheme; the packaging alone does not establish current
   source admission or a particular joint interpretation.
3. **Generalization provenance.** `infer/src/constraints/mod.rs:3118–3150`
   records generalized owner/generation, witness paths, derivation parents,
   completeness and source-witness instantiation identities.
4. **Use-time projection.** `infer/src/instantiate.rs:91–101,179–186,212–256`
   projects witness records through the same instantiator used for the Scheme.
   Argument mappings and structural mappings are separate channels; incomplete
   or unprojectable witnesses are counted and skipped. This is coordinated
   freshening/provenance plumbing, not current `beta`/`Slots(beta)` formation
   or receipt semantics.
5. **Formal-keyed annotation evidence.** `poly/src/expr.rs:76–81,147–163`
   retains annotation family paths, function depth and resume policy under a
   formal identity. Existing annotation producer archaeology records the
   guarded call-upper feedback route. Those annotation-dependent markers and
   call uppers do not define the current complete, comparison-independent
   profile or typed capture/rebind/read association.
6. **Sparse structural occurrence provenance.**
   `poly/src/provenance.rs:24–104` and
   `infer/src/analysis/session/occurrence_provenance.rs:15–68,119–181,228–322`
   retain owner, role, structural type path and explicit completeness state.
   Application expected provenance is registered after application subtype
   submission (`infer/src/lowering/expr/tail.rs:552–586`). In
   `append_generalized_occurrences`, completeness is inherited from each
   witness and downgraded when a parent carrier is unavailable
   (`infer/src/analysis/session/occurrence_provenance.rs:251–307`). The positive
   Function branch of `WitnessCollector::collect_pos` traverses the argument
   at every depth but traverses argument-effect, return-effect and return
   positions only when `path.depth() != 0`
   (`infer/src/generalize/provenance.rs:308–338`). This is a bounded collector
   omission, not a claim that every generalized witness is incomplete.
   This sidecar is useful provenance plumbing,
   but is post-submission and intentionally sparse; it cannot establish
   query-independent source registration or independent admission.

## Discriminator and limit

The historical projector itself distinguishes complete from incomplete
provenance: holding a projectable FunctionArgument witness, its path and the
instantiated Scheme fixed, changing only its completeness marker changes the
result from a mapping to an incomplete-witness count. This is a direct
representation-level discriminator under supplied state premises. It is not
an accepted-source counterexample, executable experiment, or current semantic
claim.

The closest historical counterpart is therefore a **pipeline of shared
identity, correlated Scheme freshening, and partial owner/path evidence**.
Its first missing correspondence with the current producer is the source rule
that gives these facts a joint interpretation: the protected provisional
formal view and later ordinary-value use must constrain the same original
relation, while complete typed positions/profile and independent admission
are retained. Neither an eventual generalized mapping nor a post-solve
occurrence record supplies that source rule.

This result does not claim Oracle has no other relevant path. It covers the
listed representation and projection mechanisms and the already inspected
neighboring formal-keyed annotation/call producer routes. Changed source blobs
or an uninspected evidence-bearing producer could narrow the result. No
current proof gate closes from this correspondence; soundness, principality,
source adequacy and production cutover remain gated.

## Provenance and checks

Frozen Oracle revision was fixed at
`a58eefc31e22141574b6f20c6a5748151c6d79f1`. Read-only source inspection and
content-hash comparison matched the original eight inspected files against the
prior frozen-source hash tables. Four additional cited files were directly
read during the review repair in `/tmp/yulang2-oracle-rebuild`; their content
hashes below match the primary's separate validation against the exact frozen
revision. Blob SHA-1 values were computed from file bytes using the Git blob
header, without invoking Git. No Oracle execution, build, test, mutation, or Git
operation was performed. The source-search scope was bounded to identity,
generalization, instantiation and occurrence-provenance paths; this note does
not report exhaustive repository search coverage.

Original eight-file inventory:

| Oracle path | Blob SHA-1 |
| --- | --- |
| `crates/poly/src/types.rs` | `472e3ae280cf5aaeb81fa49f9104fcde83214d0a` |
| `crates/poly/src/expr.rs` | `4cd13e8b9d71b63f768d4a5739a264b5a3b76c1e` |
| `crates/infer/src/typing.rs` | `7d8ad7846aaf4942512a23ad3710ddfd9d2e78be` |
| `crates/infer/src/uses.rs` | `46e093ef7dd2f9cabbdb8ec115437bac2d5568e9` |
| `crates/infer/src/lowering/local.rs` | `5b60e91edc1ff194486fe3292b53b292bf54d529` |
| `crates/infer/src/instantiate.rs` | `7a0039439955b399f2bf526dc39f1d1aeddd008d` |
| `crates/infer/src/constraints/mod.rs` | `14860e3664a7ac05f7493f1d51fe69a6f34216e5` |
| `crates/infer/src/constraints/machine/entry.rs` | `d75544523281cc7f5c6f1778fbe25eb42b7dfe7b` |

Additional cited files inspected for the review repair:

| Oracle path | Blob SHA-1 | SHA-256 |
| --- | --- | --- |
| `crates/poly/src/provenance.rs` | `0980898542588402426b80cca421a5299fd75867` | `9b1dc3fa436d92c39c2732ec401f10b3747e3e0f1bb921dc23b96fb19039e519` |
| `crates/infer/src/analysis/session/occurrence_provenance.rs` | `6a3e4da511d8c2f6f512f2c22b6112ecda6076c8` | `90613e12e904c74d40894e6f395162c358cc632a8aecb9ddc55db542dd897268` |
| `crates/infer/src/lowering/expr/tail.rs` | `8289bfdc6a17b2469ae168ac7939d34813fda474` | `ac406b309fbb0ba558a18e37aba63a8e7ffeabbc377a111566b1f97d786f93b8` |
| `crates/infer/src/generalize/provenance.rs` | `62a70745be4d0e5e7880adec727216f188640b4a` | `83859368c64d27abb5896f1efc491b7fd616adf893b03d36d99b8f57da1792e0` |

No current compiler code or shadow premise was changed by this historical
correspondence note. The exact current unresolved cut remains source-owned
`U_c`/`Delta_formal`, complete original profile and typed incidence, and
independent admission under the shared original `xi`.

## Independent review

A compiler referee reviewed the original frozen note and the repaired
evidence inventory. The original finding concerned omitted source locators and
hash entries; the delta review verified all twelve listed paths against the
frozen Oracle revision, confirmed the exact completeness/collector locations,
and found no remaining issue. The accepted scope remains this bounded
historical characterization only. No current source-generation, soundness,
principality, admission, adequacy or production result is certified.
