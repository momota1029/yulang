# Atomic Record visible-projection finite model

Status: Independently reviewed finite characterization; no theorem or implementation authority.
Date: 2026-10-05
Baseline: `f65d68c5d43623f0d8a02194142828ec144755ab`
Implementation authority: none

## Question and governing premises

This independent finite model asks whether the positive-projection image of
the supplied unguarded upper-only atomic fiber `X <= {a:kappa}` is precisely
the visible Record-root language with no root `a`, within the named finite
graph envelope. Here `kappa` denotes hidden rigid atom `κ` and `Int` is the
sole visible primitive. This is an executable characterization, not theorem
evidence by itself, source acceptance evidence, or a production implementation.

The governing sources are
[open residual factorization §7.1](../design/2026-10-03-open-residual-factorization.md)
and [scoped structural projection §3](../design/2026-10-03-scoped-structural-projection.md).
The former allows arbitrary contractive regular values in extra fields when
there are no lower bounds; the required root field remains `a:kappa`. The
latter makes positive Record projection always available, retains a field
exactly when its positive child is available, and makes a hidden atom
unavailable. Consequently constructor back-edges are available even when
the referenced Record also contains hidden atom leaves.

Permissions, guards, and original joint predicates remain separate premises
to be conjoined on the same original assignment. This experiment neither
implements them nor assumes that every structural witness satisfies them.
For example, a permission excluding `kappa` could remove every source in
this enumeration; no corresponding full joint image equality is claimed.

Dependency SHA-256 values at the assigned baseline:

| Dependency | SHA-256 |
| --- | --- |
| `notes/design/2026-10-03-open-residual-factorization.md` | `02e6e04d1a4eea405442587206e34c653b45405677d653e6bfec37568fee4f43` |
| `notes/design/2026-10-03-scoped-structural-projection.md` | `b1b7e675902820d6e5d4488c656ab11332b4fc2f54dd64e0fa2cd2e5cf5519a0` |

## Exhaustive domain and equality criterion

The range is exhaustive, with no random seed: one or two reachable,
deterministic, uniquely labelled Record nodes, rooted at node zero. Atom
leaves are not included in the Record-node count. Only labels `a` and `b`
exist. The root has mandatory `a:kappa`; its `b` slot is absent, `kappa`,
`Int`, or any Record-node reference. Each nonroot Record has independently
selected `a` and `b` slots with the same choices. Selected fields are
mandatory; an absent slot chooses a different Record shape, not optional
field semantics. References may share targets, refer to the root, or form
cycles; every reference passes through a Record constructor. Unreachable
input nodes are excluded from enumeration.

The independently generated candidate grammar has a Record root with no
`a`, an absent or visible `b` field, and at most two reachable Record nodes.
Nonroot Records may have `a` or `b`, with values `Int` or any Record
reference. Candidate generation does not call the projector or inspect
source graphs. In the two-node case the root's `b` must reference the
secondary node, which makes the family directly enumerable.

The direct reference implements only this Record/atom fragment of `A+`:
retain visible atom and Record-reference fields, delete hidden atom fields,
and retain graph back-edges without unfolding. Two outputs are equal exactly
when their rooted deterministic labelled trees are bisimilar. Partition
refinement computes a greatest Record bisimulation using exact label sets,
atom identities, and successor blocks. The reachable quotient is numbered
in root-first breadth-first order with ordered labels. Thus node IDs,
duplicate bisimilar nodes, and newly unreachable projected nodes cannot
affect the key.

Reference and candidate share the graph encoding, atom alphabet, and
bisimulation-key routine. They do not share enumeration or projection code.
The self-check includes equivalence between one-node and two-node cycles,
invariance under a detached node, and distinctions from empty and
atom-ended Records. This is consistency evidence for the supplied structural
premises, not independent validation of source semantics or of the entire
projection implementation.

## Result and falsifiers

| Family | One Record node | Two Record nodes | Total presentations | Rooted bisimulation classes |
| --- | ---: | ---: | ---: | ---: |
| Admitted source graphs | 4 | 25 | 29 | 27 |
| Independently generated visible candidates | 3 | 16 | 19 | 17 |
| Correct projected outputs | — | — | 29 generated outputs | 17 |

The source output set and candidate language set are equal: exactly **17**
rooted bisimulation classes, with no missing or excess class in this range.

The hidden-availability mutation wrongly supplies visible `Int` as the
projection of `kappa`. It produces **17 false-positive image classes**.
Its smallest source has one Record node and only the required hidden field:

```text
source:        {a:kappa}
correct A+:    {}
mutated A+:    {a:Int}
```

The mutated result is visible but has a root `a`, hence is outside the
candidate language. This is minimal in Record nodes and selected source
fields because every admitted source has a Record root and mandatory `a`.

A separate admissibility mutation accepts `{a:Int}` as a witness of
`X <= {a:kappa}`. Identity-only atomic comparison rejects that source;
ordinary positive projection would retain `a:Int`, giving the same smallest
false-positive visible shape. The still smaller-field source `{}` also
violates the required-root-field premise, but its projected result belongs
to the legitimate image. Thus image-set equality alone cannot detect an
admissibility mutation that only admits missing-`a` sources; the script
checks source admissibility separately for that witness.

Recursive visible `b` fields remain admitted. The script checks the
one-state self-cycle and this non-collapsing two-state cycle:

```text
source r0 = {a:kappa, b:r1}       projected r0 = {b:r1}
source r1 = {a:Int,   b:r0}       projected r1 = {a:Int, b:r0}
```

The projected graph has two bisimulation classes of Record nodes and occurs
in the independent candidate language. Removing the hidden required field
does not remove the recursive `b` edge.

## Verification and boundary

One deterministic single-process computation completed successfully:

```text
python3 tools/research_atomic_record_visible_projection.py
```

The script enforces a 5-second wall timer, a 5-second CPU limit, and a
256-MiB address-space limit. The sole bounded run exited zero without a
timeout, emitted `equality: true`, and passed its image, bisimulation,
mutation, and recursive-witness assertions. No additional search process,
Cargo invocation, broad suite, or performance sampling was used. Peak
resident memory and performance timings were not measured. Whitespace was
checked only on the two leased artifacts.

Omissions are graphs requiring more than two reachable Record nodes, other
labels and atoms, additional or lower bounds, Functions, declared-variance
constructors, permission/guard/Phi solving, source generation, lifecycle,
effects, and production correspondence. Equality for this finite envelope
does not prove the unbounded visible-root language statement. No theorem or
authority status is promoted by these checks.

## Frozen commit packet

Exclusive paths:

- `tools/research_atomic_record_visible_projection.py`
- `notes/progress/2026-10-05-atomic-record-visible-projection-model.md`

The artifact is a research-only checkpoint based on the baseline and
dependency hashes above. The producer ran its one capped check. Independent
`spec_auditor` review found no blocking, major, or minor findings. It verified
the source and candidate enumeration ranges, projected-node correspondence
for recursive edges, rooted labelled-tree bisimulation key, mutations, and
permission/guard exclusions. Review did not reproduce the producer's
execution, extend the finite range, or audit production source generation.
This remains finite characterization, not an unbounded theorem. No production
code, expected output, manifest,
question bundle, shared task record, or design-status file was changed.
Shared `tasks/current.md`, `tasks/research-lab.md`, and theory/index
synchronization are intentionally deferred to the primary's integration.
The primary owns dependency rechecking, review adjudication, and all Git
operations.

Proposed commit message: `research: characterize atomic Record visible projection`
