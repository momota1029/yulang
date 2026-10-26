# Independent review: finite generalization solution transport

Review ID: INFERENCE-GENERALIZATION-REVIEW-20261026/r1. Reviewer:
`/root/inference_frontier`, a non-author of the target and its constraint-syntax
dependency. Primary: `/root`. Task baseline reported by primary:
`0f6346a2de0a8bff863f41d487eb4b29cf8fb5f3`; this reviewer ran no Git commands.
Review started 2026-10-26 01:19 UTC. This initial review is frozen before the
primary's announced narrow repair. The source hashes below define its scope.

## Disposition and severity

**No blocking or major mathematical finding against the literal finite-store
pullback theorems. One MINOR claim/correspondence finding, M1, is accepted by the
primary and awaits a narrow repair plus delta review.** The initial target is
not certified as exact native freshening, complete source generalization, or
the original inference-soundness/A/B theorem.

The primary's response accepts M1 and proposes to retain the arbitrary-map
forward theorem, label its level construction as a seeded lower envelope, add
an in-range/idempotent canonical-map condition with exact class-minimum and
post-allocation results, and make the complete-store/native boundary explicit.
This receipt does not prejudge those unwritten additions. No source was repaired
by the reviewer, and no new theorem/source hash is accepted here.

## M1 — canonical quotient claims exceed the arbitrary-map hypotheses

Location: `SimpleSubGeneralizationSoundness.lean`, `quotientLevels` at lines
191–196, its description as a finite minimum over a quotient fiber, and the
interpretation of the later allocation as independent fresh post-quotient
blocks. The theorem parameters use the completely arbitrary kind-preserving
`Renaming = Kind → Nat → Nat`.

The fold starts from `before k representative`, then takes minima over original
rows `i < n` satisfying `q k i = representative`. That seed need not belong to
the finite fiber. By direct expansion, take one kind, `n = 2`, `q(0) = 1`,
`q(1) = 0`, `before(0) = 5`, and `before(1) = 0`. The finite fiber of 1 is
`{0}` and has minimum 5, whereas the implemented `quotientLevels ... 1` is 0.
The proved inequality `quotientLevels ... (q i) ≤ before i` remains true.
Consequently its anchor-preservation and forward-pullback uses remain valid.
The defect is in calling this an exact class minimum for arbitrary `q`.

Likewise, the original allocation lemmas require their row indices to be below
`n`. They cannot be applied automatically to `q k i`. For `n = 2`, `count = 2`,
boundary 0, all after-levels 1, and `q(0) = 0`, `q(1) = 2`, the post-use image
of row 1 in use 0 is 4, equal to the image of row 0 in use 1. The post-use image
of row 1 in use 1 is 6, which is also a literally fixed future-client identity.
This does not refute the forward theorem: its post-state solution premise
already includes those identifications. It does prevent an unconditional
interpretation as the native allocator's disjoint post-quotient use blocks.

An in-range canonical representative map (`q i < n` for `i < n`, and
`q(q i) = q i`) supplies the missing interpretation: the representative is
itself in the finite fiber, and the existing fresh-block arithmetic applies
to all representative indices. The broad pullback theorem should remain broad;
the exact minimum/freshness claims need their precise canonical-map premises.
No compiler or language semantics change follows from this finding.

## Checked theorem content and shared witnesses

The reviewed namespace is `YulangClosure.SimpleSub.Generalization`.

- `freshen_anchor` and `freshen_eligible` follow the actual definition's level
  partition. `freshen_injective` assumes both original indices are below `n`.
  `distinct_uses_disjoint` additionally assumes distinct use IDs and that both
  rows are above the boundary. Low rows intentionally remain shared. Repeated
  IDs in the finite `uses` list denote the same use, not new independent uses.
- `transport` is one total kind-preserving map. It maps original `[0,n)`
  coordinates through `q`, decodes each reserved use block by quotient and
  remainder, and fixes coordinates at or beyond `n * (count + 1)`.
  `transport_base`, `transport_copy`, and `transport_future` prove these cases.
  The `n = 0` and zero-use boundaries do not create an undefined division case:
  the interior block branch has no inputs then, and copy lemmas require `i < n`.
- `PreservesAnchors n boundary before after q` states only that a bounded
  originally low row has a low post-map image. It is not a disguised solution,
  native-success, diagonal-lift, or source-typing premise. The broad
  `quotientLevels_le` theorem constructs this property through a nonincreasing
  finite fold. M1 concerns the stronger class-minimum interpretation.
- `transport_freshen` proves the commuting equation for every kind, original
  index `i < n`, and use `use < count`, from `PreservesAnchors`. An originally
  high row may become low. No hidden requirement that all high rows remain high
  occurs. `raising_anchor_breaks_transport` correctly demonstrates why the
  low-anchor premise is substantive.
- `base_term_pullback` requires `Bounded n t`; `fresh_term_pullback` additionally
  requires anchor preservation and a bounded use index. Both use one valuation
  `ρ`; the induction covers every actual finite `Term` constructor, including
  all four function ports and unchanged record labels/optional bits, variant
  tags, and tuple order. Atom identities remain rigid.
- `quotient_uses_sound` requires a bounded original store, anchor preservation,
  bounded use IDs, and a solution `ρ` of the complete post-map store plus its
  copies. It constructs satisfaction of the complete original store plus all
  requested copies under exactly `fun k i => ρ k (transport ... k i)`.
- `quotient_uses_with_clients` adds an arbitrary finite `clients : Store`.
  Its post-state premise contains `clients.map (Constraint.rename transport)`;
  its conclusion contains the original `clients` under the same pulled-back
  valuation. This is correct for arbitrary clients and arbitrary `q` as typed.
  It does not silently assert that unrenamed arbitrary clients have identical
  post-state syntax. The root pullback lemmas provide the separate equations
  needed for clients constructed from corresponding published roots.
- `minimum_quotient_uses_with_clients` replaces the anchor premise with the
  concrete `quotientLevels` construction. Its literal statement is correct;
  its class-minimum interpretation is subject to M1.

No per-clause or per-use existential witness is chosen. The input valuation and
the total transport are shared across the retained base, all finite uses, all
four function ports, roots, and arbitrary client clauses. The proofs do not
infer a solution from native successful return. No reverse coverage,
principality, or arbitrary joint diagonal lift is established.

## Source/native boundary and remaining parent obligations

The top-level principles retain the original soundness, principality,
termination, ordinary inference behavior, and source/native correspondence.
The reviewed theorem contributes a constructive simultaneous forward solution
transport. It does not instantiate `SourceProblem.InferenceSoundness`.

`usesStore` explicitly retains the original `Store` and copies **every clause**
for every requested use. It has no native bound owner, published-root
reachability computation, captured-local metadata, or actual allocation trace.
It therefore does not itself formalize NL6's equality for actual reachable-high
native publications. An actual native solution cannot simply be declared to
satisfy this larger copied store without a correspondence or extension proof.

The pinned native-level note distinguishes ordinary-history level closure and
low-anchor dependency closure (NL1–NL4) from closure after quotienting (NL5).
Its NL6–NL7 additionally address root-reachable class saturation and actual
published-clause correspondence. The present finite all-clause construction
does not assume these properties, and it does not prove them. They remain with
the native/source bridge owner unless an alternative exact bridge is built.

Actual Rust inspected here supplies further concrete obligations:

- `candidate_scheme.rs::row` (around 1739–1762) canonicalizes the row and
  computes `local = level > boundary && !metadata.non_generic`.
- `expand_row` (around 2137–2142) stops at nonlocal rows; their mutable bounds
  remain in the session. This differs from copying every clause.
- `prepare_candidate_fresh_use` (around 4195–4275) uses one map keyed by current
  canonical rows. It reuses its first image, and allocates only when the stored
  `row.local`, current level guard, and `!non_generic` guard all hold. It also
  reconstructs source/scope/effect evidence beyond these finite terms.
- `candidate_intrusion.rs` (around 668–697) merges level metadata by `min` and
  non-generic metadata by OR before changing representative links. Connecting
  a finite canonical quotient and its metadata to all actual forest operations
  remains a separate invariant. Immutable source Value birth is not this row
  freshening eligibility metadata.

The old `/home/momota1029/rust/simple-sub-reference/.../Typer.scala` source is
absent in this environment. The reviewer did **not** read or independently
verify that reference source; the inspected source evidence is the Rust owner
above and the pinned existing NL note. The primary explicitly confirmed this
scope. No unavailable historical file is claimed as freshly read.

The finite syntax also omits complete source Call/effect admission, hidden
source witness/scope realization, recursive solution existence, actual native
allocation identity and resource behavior, interleaved solving/new lets,
source-scoped reverse coverage, and original whole-language termination.
Opaque structural atoms and the independent `Sub` relation do not discharge
those missing meanings. These are retained obligations, not restrictions newly
imposed on the original supported language.

## Frozen inputs and checker evidence

Both repository and isolated-project copies match for the complete local import
closure:

| Input | SHA-256 |
| --- | --- |
| `SimpleSubGeneralizationSoundness.lean` | `e4f7224c9c50038991554dc30275f101c6cb8df9d6462c7bca98946ccee3890a` |
| `SimpleSubConstraintSyntax.lean` | `a9ec574d31223e0484fd827838b45cd019fc858eece9f326c95ebc2e1e77a1f6` |
| `Contracts.lean` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |
| `notes/theory/2026-10-24-native-level-closure-and-publication.md` | `37aeacff4a6dc310bedcb5a44db4afcf8329b05ed684df19350487c5e8711c13` |
| `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` | `3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271` |
| `crates/yu-solver/src/candidate_scheme.rs` | `02349de1a2d69289eb348f7ff807a9e36faa2e2028cf61d10c1af9cd364409c5` |

Isolated checker project:
`/workspace/scratch/f98087c7ac1a/inference-generalization/`.
Its `lean-toolchain` pins `leanprover/lean4:v4.35.0`; manifest has no external
packages. Reviewed `check-03.log` reports the target built successfully in four
jobs, with no warning/error. The reported complete audit exit is 0, elapsed
2.221 seconds.

| Evidence file in isolated project | SHA-256 |
| --- | --- |
| `GeneralizationAudit.lean` | `3b71221b4dd09d8fa360e0df953827ac0de9957d5c7636511b6f88cecf8929ff` |
| `check-03.log` | `b24edc3699a6fbb36ef3976cd0a0a24d7745b8f97e74644112f68a38d3f36901` |
| `audit-04.log` | `7690846308f2fd6e6281d629798083d2f0c0501fe372eed4f58caef47af0cc2a` |
| `audit-04.json` | `ac27e0c2450e59c5467278b64d3c4983606d69dd34b54a134868729e61d3249a` |
| `lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |
| `lakefile.toml` | `834b73ad29dd92c372a948c35d7c6c0f3744eade289a3afbab2ab7375a0d6c01` |
| `lake-manifest.json` | `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3` |

The audit enumerates every theorem originating in the module, including private
and generated constants, rejects project axioms, requires six named roots,
prints each complete type and indirect axiom set, and rejects axioms outside the
standard allowlist. Independently parsed all 65 unique matching begin/end
blocks; each has a type and exactly one axiom report. Actual distribution:
35 with no axioms, 21 with `propext` and `Quot.sound`, and 9 with `propext` only.
No `Classical.choice`, project axioms, `sorryAx`, or checker bypass was found.
The changed source and both local dependencies also contain no proof holes or
unchecked native-evaluation tactic. No Lean checker rerun was warranted by M1:
the discrepancy is in interpretation, not the accepted theorem statement.

## Write cessation and next review

The reviewer's only write is this receipt. No source, cache, configuration,
Git, compiler, scheduler record, test expectation, or other receipt was changed.
No child or checker was launched. The producer handoff was not yet present at
the initial review cutoff and is not claimed as reviewed here.

**Initial review writes stopped.** Wait for the primary's separately frozen
delta source/hash, full types/audits, and handoff. Delta review should check the
new canonical hypotheses, exact minimum and post-allocation results, unchanged
broad pullback statement, and clarified native boundary without repeating the
unaffected broad review.
