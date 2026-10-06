# Frozen Oracle whole-tuple source-producer correspondence

Date: 2026-10-06
Status: frozen research-only historical characterization; review pending
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
   submission (`infer/src/lowering/expr/tail.rs:552–586`). Generalized
   completeness is explicitly partial, and the root-function collector omits
   root return/effect witnesses. This sidecar is useful provenance plumbing,
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
content-hash comparison matched the eight inspected files against the prior
frozen-source hash table. No Oracle execution, build, test, mutation, or Git
operation was performed. The source-search scope was bounded to identity,
generalization, instantiation and occurrence-provenance paths; this note does
not report exhaustive repository search coverage.

Inspected paths:

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

No current compiler code or shadow premise was changed by this historical
correspondence note. The exact current unresolved cut remains source-owned
`U_c`/`Delta_formal`, complete original profile and typed incidence, and
independent admission under the shared original `xi`.
