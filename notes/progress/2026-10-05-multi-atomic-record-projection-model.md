# Two-hidden-atom Record projection finite model

Status: Independently reviewed finite characterization; research-only checkpoint.
Date: 2026-10-05
Baseline: `caad6f1676867bfc46631119eadce925f1d4fafa`
Implementation authority: none

## Question and supplied premises

This bounded experiment asks for the exact positive-projection image of the
unguarded upper-only structural fiber

```text
X <= Record{a:kappa_a, b:kappa_b}
```

where the two hidden rigid atoms have distinct identities and there are no
lower bounds. The supplied governing sources are
[open residual factorization §7.1](../design/2026-10-03-open-residual-factorization.md)
and [scoped structural projection §§2–5](../design/2026-10-03-scoped-structural-projection.md).
The first fixes required root fields by atom identity and permits arbitrary
contractive regular extra fields. The second supplies the signed greatest
availability fixed point and its shared projection construction. These are
research premises; this experiment gives them no additional authority.

The existing
[one-atom model](2026-10-05-atomic-record-visible-projection-model.md)
covered only Record/atom extras. Here Functions supply a distinct falsifier:
contravariant access to the original root can prevent an extra Function field
from projecting, even though the root's positive Record projection exists.
No permission, guard, `Phi`, source acceptance, or production correspondence
claim follows. All constraints in this note concern the supplied pure
structural fiber on one assignment.

Frozen dependency SHA-256 values:

| Dependency | SHA-256 |
| --- | --- |
| `notes/design/2026-10-03-open-residual-factorization.md` | `02e6e04d1a4eea405442587206e34c653b45405677d653e6bfec37568fee4f43` |
| `notes/design/2026-10-03-scoped-structural-projection.md` | `b1b7e675902820d6e5d4488c656ab11332b4fc2f54dd64e0fa2cd2e5cf5519a0` |
| `notes/progress/2026-10-05-atomic-record-visible-projection-model.md` | `ee1657bb9f3d1f5843d8b6c8602fcd2ed94d991726a570a95a39305a14399098` |
| `tools/research_atomic_record_visible_projection.py` | `a440ab5e832a9da8d09ec70a0d26ee58af9bfe7acb2616909e16f1d07b13a44c` |

## Exhaustive source and independent candidate envelopes

Sources have one or two reachable constructor nodes, root zero a Record,
and alphabet `Int`, `kappa_a`, `kappa_b`. Atoms do not count as constructor
nodes. The only Record labels are `a,b,c`. The root's `a:kappa_a` and
`b:kappa_b` are mandatory. Its `c` slot is absent, any atom, or a reference
to any constructor node. The second node, when present, is either a Record
with three independently selected slots or a Function with two mandatory
children. Each nonroot Record slot is absent, any atom, or any node
reference; each Function child is any atom or any node reference.
Unreachable presentations are excluded. Every reference crosses a constructor,
so sharing and cycles are contractive. Absent slots choose different mandatory
Record shapes; they do not introduce optional-field semantics.

The source enumeration covers **246** presentations: 5 with one constructor
and 241 with two. Reachability forces root `c` to reference the second node
in the two-node family, leaving 216 possible nonroot Records and 25 possible
Functions. Exhaustion has no random seed.

The broad visible grammar is independently enumerated: one or two reachable
constructors, a Record root omitting `a,b`, only `Int` leaves, and the same
constructor and label vocabulary. The root's `c` is absent, `Int`, or a node
reference. There are 3 one-node presentations, 64 with a secondary Record,
and 9 with a secondary Function, totaling **76**.

The exact candidate for the stated source cap adds this grammar condition:
starting at the root with positive polarity, no finite signed dependency path
reaches that root with negative polarity. Record children preserve polarity;
Function arguments reverse it and results preserve it. Candidate filtering
traverses these signed paths without calling availability or projection.
All 64 secondary Records pass. Exactly 5 of the 9 Functions pass, leaving
**72** candidate presentations. This condition is part of a finite
characterization, not a claim about arbitrary regular graphs or finite hidden
sets.

The reference starts all constructor/sign pairs available and deletes pairs
that violate the supplied equations. Hidden leaves have neither sign;
visible leaves have both. Positive Records always remain available, negative
Records require all negative children, and Functions require the reversed
argument sign and unchanged result sign. Construction keeps exactly available
positive Record children and all children of other available pairs, allocating
and sharing one output node per reachable signed source pair. It preserves
back-edges without unfolding.

Equality is rooted regular-tree bisimulation with exact constructor heads,
Record label sets, indexed Function slots, and atom identities. Partition
refinement computes the greatest bisimulation, then breadth-first numbering
canonicalizes the reachable quotient. Consequently source node IDs,
bisimilar duplicate nodes, and detached projected nodes cannot affect an image
class. The self-check covers cycle duplication, a detached node, empty versus
cyclic Records, Record versus Function heads, and distinct hidden identities.

Reference and candidate share graph encoding, atom vocabulary, polarity rules,
and the equality key. Candidate generation and its signed-path filter do not
call the projector or inspect sources. This separation discriminates the
supplied rules within the named envelope; it is not independent validation of
those rules as source semantics.

## Result and discriminating witnesses

| Family | Presentations | Rooted bisimulation classes |
| --- | ---: | ---: |
| Admitted sources | 246 | 244 |
| Exact candidate grammar | 72 | 70 |
| Correct positive-projection image | 246 generated outputs | 70 |

The two image sets are equal: **70** rooted bisimulation classes with no
missing or excess class. The broad visible grammar that merely omits root
`a,b` has **4 excess classes** at this source-size cap.

For example, the following two-node source loses its `c` field:

```text
source r0 = {a:kappa_a, b:kappa_b, c:r1}
source r1 = Function(r0, Int)
correct A+(r0) = {}
```

`A-(r0)` is unavailable because both hidden required fields are present.
Hence `A+(r1)` is unavailable through its argument, and positive Record
projection omits `c`. A sign-blind mutation using positive Function arguments
instead produces the visible two-node cycle

```text
v0 = {c:v1}
v1 = Function(v0, Int)
```

which belongs to those four excess classes. This attacks Function polarity,
rather than repeating hidden-leaf deletion alone.

The negative-root-path condition is specifically an artifact of the bounded
source envelope. One targeted, non-enumerated **three-node** source realizes
the same visible cycle correctly:

```text
r0 = {a:kappa_a, b:kappa_b, c:r1}
r1 = Function(r2, Int)
r2 = {c:r1}
```

The visible clone `r2` has both signed availabilities. Projected positive and
negative copies of its Record/Function cycle are bisimilar to `v0,v1`, and
the projected original root is bisimilar to that Record. This targeted check
does not extend the exhaustive range beyond two constructors or establish
the full unbounded image.

The two independent hidden-availability mutations replace either selected
hidden identity by visible `Int` during projection. Each produces **70 excess
image classes**. Their smallest admitted source has one Record and the two
mandatory fields:

```text
source:              {a:kappa_a, b:kappa_b}
correct:             {}
kappa_a leak mutant: {a:Int}
kappa_b leak mutant: {b:Int}
```

These witnesses are minimal in constructor nodes and selected source fields
within the admitted fiber. The leaked `Int` makes each wrong output visible;
merely retaining an opaque atom would already violate the visible codomain.

Admission has separate mutation checks. Dropping the `a` requirement admits
`{b:kappa_b}`; dropping `b` admits `{a:kappa_a}`. Swapping the required
identities admits `{a:kappa_b,b:kappa_a}` under an identity-blind rule.
All three sources fail correct admission yet project to legitimate `{}`.
Thus image-set equality cannot certify those admission rules. Replacing
either required atom by `Int` also fails admission, and its retained visible
field yields an excess image. The checker asserts both categories explicitly.

Recursive visible extra fields survive, including a root self-cycle and
the non-collapsing two-Record cycle:

```text
source r0 = {a:kappa_a, b:kappa_b, c:r1}
source r1 = {a:Int, b:kappa_b, c:r0}
visible v0 = {c:v1}
visible v1 = {a:Int, c:v0}
```

The latter has two distinct rooted quotient nodes and belongs to the exact
candidate language. Hidden-leaf omission preserves the `c` back-edges.

## Verification, limits, and frozen handoff

An independent `spec_auditor` statically reviewed the frozen script and note
and found no blocking, major or minor findings. The review checked the source
and candidate envelope counts, signed-path cap condition, quotient/bisimulation
key, distinct-atom admission, mutations and clone witness. The reviewer did
not execute the script; the reported class totals and command result remain
producer-reported execution evidence rather than reproduced review evidence.

One deterministic computation completed successfully:

```text
python3 tools/research_multi_atomic_record_projection.py
```

It used one Python computation process, enforcing 5-second wall and CPU
limits and a 256-MiB address-space limit. The run exited zero without a
timeout, emitted `equality: true`, and passed all image, admission,
bisimulation, recursive, leak, Function-sign, and clone-witness assertions.
The command runner reported approximately 0.1 seconds elapsed; CPU time and
peak resident memory were not sampled. No Cargo build, test suite,
performance repetition, extra search process, or random sampling was run.

Omitted cases include exhaustive sources with more than two constructor
nodes, more labels/atoms/hidden names, lower or interacting bounds,
declared-variance constructors, effects, permissions, guards, joint `Phi`,
source generation, and production implementation. Even the two-hidden-atom
unbounded image theorem remains outside this result. No arbitrary finite-H
theorem, principality gate, implementation permission, or language authority
is established.

Exclusive completed lease paths:

- `tools/research_multi_atomic_record_projection.py`
- `notes/progress/2026-10-05-multi-atomic-record-projection-model.md`

Both artifacts were frozen before review. No dependency change was observed
against the packet's frozen hashes. No Git mutation was performed. Shared task, queue, index and
theory-status changes are intentionally deferred to the primary; the proposed
delta is to record a new finite signed-projection characterization and its
source-cap counterexample, without promoting theorem or authority status.
Recommended next action: independently review the precise finite envelope,
candidate signed-path filter, and the clone witness before checkpointing.

Proposed checkpoint message: `research: characterize two-hidden-atom Record projection`
