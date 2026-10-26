# Owner-local scoped publication: constructive forward bridge

Packet: INFERENCE-SCOPED-PUBLICATION-20261026/r1. Producer:
`/root/inference_frontier`; primary `/root`. Fifteen-minute bounded leaf packet;
no children, Git, compiler, or production changes. Original parent:
`SourceProblem.InferenceSoundness`, with unchanged full source/native/A/B scope.
This packet does not close that root or identify native successful return with
a supplied solution. Source was frozen before this handoff was written.

## Result and improvement over the complete-store theorem

New module: `notes/theory/lean/YulangClosure/SimpleSubScopedPublication.lean`.
Namespace: `YulangClosure.SimpleSub.ScopedPublication`.

**Constructed and checker-accepted:** every transported original published
clause belongs to a post-quotient publication consisting of the complete
retained base plus only the clauses of reached local owners. A single
post-publication valuation therefore pulls back to the original retained base,
all selected owner clauses for arbitrarily many finite uses, and arbitrary
client clauses under the same transport.

The prior theorem copied every supplied clause for every use. The new theorem
does not assume satisfaction of that larger copied store and does not assume
the final clause correspondence. It derives clause inclusion from structural
owner dependencies, the actual stopping distinction, inactive-image metadata,
and finite bounds. Only the forward reachability image is needed; no reverse
reachability or quotient-class saturation is assumed.

**Concrete remaining obstruction:** the post-quotient stopping/dependency
closure needed by this bridge is not established for all actual native
histories. Two checked counterexamples rule out deriving it from owner minima
alone or from numeric level closure alone. No source-program unsoundness or
source-qualified intrusion counterexample is claimed.

## Source inspection and represented operations

The source was inspected before constructing the proof:

| Actual owner | Corresponding formal object | Boundary |
| --- | --- | --- |
| `candidate_scheme.rs::row`, around 1739–1762 | `captureGuard boundary metadata` is `boundary < level && !nonGeneric` | Snapshot guard, not immutable Value birth |
| `expand_row`, around 2137–2142 | `Reach` stops when the captured owner is nonlocal | Root rows are retained even when their bounds are not traversed |
| Value/effect direct lower and exact lower loops | Positive `Bound` becomes `body ≤ var owner` | Both kinds represented |
| Value/effect direct upper and exact upper loops | Negative `Bound` becomes `var owner ≤ body` | Both endpoints retained under one rename |
| `freshen_candidate_graph_core`, around 4178–4193 | All selected captured bounds are restored for a use | Allocation eligibility is separate from capture traversal |
| `prepare_candidate_fresh_use`, around 4248–4276 | `useGuard captured boundary liveMetadata` conjoins captured-local with current level/non-generic guard | Actual canonical-row first-image memo coherence remains a native obligation |
| `candidate_intrusion.rs`, around 630–697 | Retained bound map; minimum level and non-generic OR motivate `MetadataTransport` | Inspection of one write site is not an all-history proof |

`Bound` retains kind, owner, side and finite structural body. `vars` traverses
every constructor of the frozen `Term`: variables, atoms, bottom/top,
union/intersection, all four Function ports, record labels/optional bits,
tuple order, and variant tags/payload/tail. Function argument/result effect
variables retain their effect kind when traversing a value-kind body.
Substitution/rename does not erase any constructor or change atom identities.

`Published` is an inductive finite-clause membership relation. Its base rule
retains every original owned clause. Its copy rule requires an actual bound in
the list, a requested use ID, reachability of that bound's owner, and a local
capture guard. It copies that clause through the use's one allocation map.
The relation is a structural publication model; no source typing, native
success, or final correspondence certificate is a constructor field.

Membership/satisfaction intentionally concerns clauses, not an equality of
physical list order, duplicates, evidence IDs, or allocation traces. Those
remain distinct native correspondence obligations.

## Main theorem types and why the hard case works

`publication_clause_image` has these exact premises:

1. `BoundsBounded n bounds`: every bound owner is below `n`, and every variable
   in its structural body is below `n`.
2. `InactiveImages n beforeUse afterUse q`: an originally inactive bounded row
   has an inactive image under the same kind-preserving map `q`.
3. `StoppedClosed (bounds.map (Bound.rename q)) afterCap`: for each post-map
   bound, an inactive capture owner has only inactive capture dependencies.
4. Capture stopping also stops post allocation: `afterCap k i = false` implies
   `afterUse k i = false`.
5. Every requested use ID is below the finite block count.
6. Membership of the particular original clause in `Published`.

Its conclusion is membership of that clause renamed through the existing
`Generalization.transport` in the post-map `Published` relation. There is no
assumption that the requested clause image is present.

`reachable_active_image` proves the necessary image condition by induction over
the real owner/dependency reachability constructors. If a post dependency is
active, `StoppedClosed` prevents its predecessor from being inactive. The
induction thus constructs a post path whenever its target is active. It need
not reconstruct the images of stopped descendants or prove equality of the
two reachable sets.

For a copied clause, the proof uses the established bounded freshening square.
It then splits on the **post capture owner**:

- If active, the derived reachability image selects the actual post copied
  owner clause.
- If inactive, closure makes every structural dependency inactive. Allocation
  therefore fixes the owner and every dependency. `stopped_clause_fixed` proves
  that the entire copied clause equals its retained base clause, including
  every port of a compound body. Owner level alone would not justify this step.

`publication_solution_pullback` applies the derived inclusion and
`Constraint.rename_satisfied`. The result uses exactly

```text
rho'(k,i) = rho(k, Generalization.transport n count 0
                    (guardLevels afterUse) q k i).
```

`publication_with_clients` adds arbitrary finite client clauses. Its input
clients are explicitly renamed by this same total map; the output satisfies
the original clients under the same `rho'`. No per-clause or per-use witness is
chosen. The root equations from `Generalization.base_term_pullback` and
`fresh_term_pullback` apply with `guard_anchors` to every bounded actual root
term under this very valuation. Relating actual native root terms and root-row
inventory remains a separate source/graph correspondence obligation.

`guardLevels` is a zero/one encoding of an explicit Boolean eligibility guard
solely to reuse the frozen transport theorem. It is not a new native level
semantics, and it is not source Value birth. The generic algebraic theorem
allows arbitrary `q`. For disjoint post allocation and fixed future regions,
the previously proved `Generalization.Canonical n q` and canonical post-use
bounds/disjointness must additionally be supplied by the native representative
bridge; arbitrary `q` is not silently called a native canonical allocation.

## Concrete metadata specialization

`metadata_publication_with_clients` applies the preceding theorem to the exact
two-stage guards. It takes capture snapshots `beforeCapture/afterCapture` and
current-use metadata `beforeLive/afterLive`, all at the same publication
boundary. Its explicit non-solution premises are:

- bounded owners/bodies and bounded requested use IDs;
- `MetadataTransport` at both capture and current-use snapshots: mapped levels
  do not increase, and an original non-generic bit remains set at its image;
- `BoundLevelsClosed` on the complete post-map owned bounds: every dependency
  has level at most its owner;
- `NonGenericClosed` there: a non-generic owner has non-generic dependencies.

`capture_inactive_images` and `use_inactive_images` derive the inactive-image
premise from those concrete metadata facts. `capture_stopped_closed` derives
stopping closure from level inequalities and non-generic dependency propagation.
`useGuard_stops` proves the capture-stop/allocation-stop implication directly.
The specialized root then returns simultaneous publication/client satisfaction
from the actual selected post publication model and the same mapped clients.

The level and non-generic premises are **not** the conclusion of the root and
are not assumed source soundness. They are explicit native invariants still
requiring proof from the supported operations. The construction establishes
what they imply without treating their names as evidence that Rust satisfies
them.

## Checked falsifiers and actual unresolved native obligations

`numeric_closure_does_not_imply_guard_closure` constructs one value lower bound
with owner 0 and dependency 1. Both levels are 2, so numeric bound-level closure
holds. Owner 0 is non-generic while dependency 1 is generic. Capture stops at
owner 0 but would copy dependency 1. Thus numeric closure does not imply the
stopping closure of the actual non-generic-aware guard.

`minimum_counterexample_canonical` proves that the second example's map is a
genuine finite canonical map: original row 0 maps to 2; other rows remain fixed
in `[0,3)`. Original levels are 1 except row 2 at 0. The same old owner-0 bound
has level closure. The exact `Generalization.quotientLevels` construction lowers
owner 0's image to 0 while dependency 1 remains at 1. All non-generic bits are
false. `minimum_does_not_imply_guard_closure` proves post stopping closure fails.
This counterexample uses the repaired exact class-minimum construction and
canonicality, not the earlier arbitrary-map seed issue.

These are finite metadata/bound counterexamples, with no source occurrence,
qualifying Value pair, or actual accepted source trace. They refute shortcuts
in a proof; they do not authorize changing intrusion or freshening semantics.

Further source readback found:

- `candidate_insert_bound_with_evidence` canonicalizes and appends the actual
  owned bound; its inspected body is not a standalone check of the above
  post-merge dependency invariant.
- Intrusion copies both bound sides, takes minimum levels, ORs non-generic
  metadata and changes the representative. The necessary global closure cannot
  be inferred merely from those local minimum writes, as the checked example
  demonstrates.
- Initial and fresh row metadata in inspected `lib.rs` owners sets
  `non_generic = false`; the candidate merge preserves OR. Several tests set
  true explicitly. A native all-history false-bit invariant could discharge
  the non-generic closure premise on its actual domain, but this packet has not
  proved that invariant or erased the real guard.
- Effect capture adds incidence/allowance clauses and reverse upper-owner
  frontiers. These are not all ordinary owner-versus-body bounds. Source role,
  scope, attachment, evidence and effect reconstruction also occur outside this
  finite structural model. They must be mapped explicitly, not omitted from a
  claim about full native publication.

The first remaining native bridge is therefore: establish the precise
post-capture dependency/metadata invariants for actually qualifying histories,
or construct an alternative exact clause/solution transport where those
invariants do not hold. Canonical first-image coherence, all native clauses and
roots, actual allocator identity, recursive solutions/native success, full
Call/effect/source scope, principality and termination remain with the original
parent owners. No whole-language or production gate is promoted here.

## Frozen hashes

| Artifact/input | SHA-256 |
| --- | --- |
| New `SimpleSubScopedPublication.lean` | `d64e9bffca5d513985237a9ff78dcf3d9e43baae1594edbc93dff4b5410d428f` |
| `SimpleSubGeneralizationSoundness.lean` | `3f6114e4173d6cade6ad135ed83ad543116e28e87845b0f6a834cb8f727f6246` |
| `SimpleSubConstraintSyntax.lean` | `a9ec574d31223e0484fd827838b45cd019fc858eece9f326c95ebc2e1e77a1f6` |
| `Contracts.lean` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| `crates/yu-solver/src/candidate_scheme.rs` | `02349de1a2d69289eb348f7ff807a9e36faa2e2028cf61d10c1af9cd364409c5` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61` |
| `crates/yu-solver/src/lib.rs` | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` |

All four Lean source hashes match their isolated-project copies. Frozen
dependencies were not modified. Governing interpretation remains the October
11 inference principles and the pinned NL1–NL7 note
`2026-10-24-native-level-closure-and-publication.md` (SHA
`37aeacff4a6dc310bedcb5a44db4afcf8329b05ed684df19350487c5e8711c13`).
The original Scala file is absent and is not claimed as freshly inspected.

## Pinned checks, failures and complete audit

Isolated project/cache/output lease:
`/workspace/scratch/f98087c7ac1a/inference-scoped-publication/`.
Exact Lake: `/workspace/scratch/e41512dd7957/toolchains/lean-4.35.0-linux/bin/lake`.
`versions.log` records Lake 5.0.0-src+eb6cafb using Lean 4.35.0 and Lean commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. No external packages, global
configuration changes, or foreign cache writes. Every proof command used
`LEAN_NUM_THREADS=1`, `-j1 -M1024` through project arguments or the direct audit,
and a 90-second subprocess timeout. Commands were sequential.

```sh
lake --no-cache build +YulangClosure.SimpleSubScopedPublication
lake env lean -j1 -M1024 ScopedPublicationAudit.lean
```

| Attempt | Exit | Seconds | Result |
| --- | ---: | ---: | --- |
| `check-01` | 1 | 6.696 | Unsupported namespace-alias syntax and substitution rewrite elaboration; compiler-generated error placeholders, not a successful proof |
| `check-02` | 1 | 2.086 | Required explicit `Store.Satisfied` for a mapped list |
| `check-03` | 0 | 2.274 | All five dependency jobs successful; no warnings |
| `audit-04` | 0 | 1.220 | Complete originating-module audit accepted |

Both failed logs and JSON command/exit receipts are retained. No failed log was
overwritten. The final source contains no `sorry`, `admit`, project axiom,
unchecked native evaluation, or kernel bypass. There are 26 authored theorems;
the audit includes **all 82 originating theorem constants**, including private
and generated ones. Every complete type/axiom block was inspected or parsed;
all 82 start/end names are unique and match.

Actual axiom distribution: **51 none**, **13 `propext`**, **18 `propext,
Quot.sound`**. No `Classical.choice` or project axioms occur. The initial summary
regex missed two wrapped axiom lines; `audit-04.json` was corrected using full
multiline blocks. The actual checker log is unchanged, and the complete audit
was already successful.

| Final evidence | SHA-256 |
| --- | --- |
| `check-03.log` | `21cadadea08ec1a27c69f31e17ff1906f7712065003e803caf1dce5ef9bfa6b2` |
| `check-03.json` | `139bdb9d7c0910406d8c1513a4f4bc225fdde2b41e4b7e39079f5cb9d387c029` |
| `ScopedPublicationAudit.lean` | `a8a9ffb6d8cb9363427957c90080a9cc9de6c145c125bce6331965372c101e53` |
| `audit-04.log` | `9262b9a4b2f1b6abc496f439936537c047d852abb676280c0ae72eb640c8c029` |
| `audit-04.json` | `2e1e7d41dd685f4759294efce3b1c1cb1ec5fb4f638ebd3834cdea1ff9468477` |

## Ownership and stop receipt

Tracked writes are exactly the new Lean module and this handoff. Scratch writes
are confined to the granted isolated project, including its local package
configuration, copied frozen imports, cache, logs, audit and receipts. No Rust,
shared root import, dependency, existing handoff, current state, compiler,
expected output, or Git artifact was changed. No children were started.

**All checks have exited; source and handoff frozen; writes stopped.**
Independent review and integration belong to the primary. The producer does
not independently certify this component or mark its native premises closed.
