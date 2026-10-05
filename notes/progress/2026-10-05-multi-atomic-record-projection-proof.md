# Visible image of a finite multi-atomic open-Record residual

Date: 2026-10-05
Status: Independently reviewed conditional constructive research derivation; no implementation authority
Baseline: `caad6f1676867bfc46631119eadce925f1d4fafa`
Implementation authority: none
Exclusive write scope: this note only

## Governing inputs and claim class

The [open residual factorization record](../design/2026-10-03-open-residual-factorization.md)
§7.1 supplies the unguarded fiber of an atomic-Record bound with no lower
bounds. The [scoped structural projection record](../design/2026-10-03-scoped-structural-projection.md)
§§2–5 supplies the regular structural domain, greatest signed availability
and shared projection construction. The independently reviewed
[one-atom image proof](2026-10-05-atomic-record-visible-projection-proof.md)
supplies the closed-copy/fresh-root method used here.

This is a constructive extension uniform in every finite set of required
labels. It characterizes a pure structural set image modulo rooted
regular-tree bisimulation. It is not an example-only observation, an
independent review of the one-atom proof, a new authoritative decision, or
an implementation gate closure. Permissions, guards, `Phi`, source
generation and effective inference are excluded throughout.

## Hypotheses and precise image

Fix the following data.

1. The structural domain consists of finite contractive closed regular
   graphs of atoms, Functions and finite mandatory Records with unique
   labels. Function arguments are contravariant and results covariant;
   Record fields are covariant with ordinary width. Atom subtyping is
   identity only. There are no effects, invariant constructors, optional
   fields, lattice constructors or declared hidden bounds.
2. Fix one visibility classification of atoms. A visible graph has no
   reachable hidden atom. Let `H` be a finite set of distinct Record labels
   and let `h |-> kappa_h` assign each `h in H` a hidden rigid atom. The
   identities `kappa_h` are pairwise distinct. Here `H` denotes required
   labels, not the visibility frontier used in some source notation.
   Other atoms retain their fixed visibility and identity. Nested occurrences
   of labels in `H` are permitted.
3. After a fixed successful equality quotient, one descriptor-free flexible
   class `X` has exactly one upper structural bound

   ```text
   X <= U_H,       U_H = Record{ h:kappa_h | h in H }.
   ```

   It has no lower bounds, other structural clauses or additional equality
   constraints. An assignment to `X` is one closed regular root. Extra
   fields may share subgraphs, recurse mutually or refer back to this root;
   they are not independently instantiable flexible fields. Graph identity
   and sharing are not additional observable constraints.
4. Projection is precisely the two-sign construction of projection §3:
   visible atoms have both signs, hidden atoms neither; a Function at sign
   `p` requires its argument at `-p` and result at `p`; positive Records
   are always available, while negative Records require all negative
   children. Availability is the greatest Boolean fixed point. A positive
   Record keeps exactly fields whose positive child is available.

Define the structural fiber and candidate image:

```text
F_H = { T = Record(D,t) |
          D finite, H subset D,
          t(h) = kappa_h for every h in H,
          extra fields have arbitrary closed contractive regular values }

R_H = { V | V is a visible finite-label contractive regular Record,
            labels_at_root(V) intersect H = empty }.
```

Equality `t(h) = kappa_h` is modulo rooted bisimulation; equivalently the
child root is that atom. By residual §7.1 and identity-only atom comparison,
`F_H` is exactly `{ T | T <= U_H }` in this unguarded domain. The empty
case is included: `U_empty = {}`, and `F_empty` contains every Record
assignment. Non-Record assignments do not satisfy even this empty upper
Record bound because heads must match.

**Uniform finite-set image claim.** For every such finite `H`,

```text
{ [A+(T)]_bisim | T in F_H } = { [V]_bisim | V in R_H }.
```

The required atom identities do not appear in the image beyond their
hidden status. Pairwise distinctness is part of the assigned extension;
the proof in fact needs only that every required atom is hidden.

## First inclusion: all required root labels disappear

Take any `T in F_H`. Its positive Record root is available regardless of
recursive feedback. For each `h in H`, the required child is `kappa_h`,
whose positive state is unavailable. Therefore projection drops every
root label in `H`. It can retain only a subset of the finitely many extra
root labels.

Every output edge targets an available signed state. A hidden atom has no
such state, so no reachable output node is a hidden atom. The shared
construction yields a finite constructor-guarded regular graph with a
Record root. Thus `A+(T) in R_H`.

This argument permits arbitrary recursion in `T`, including back-edges
into the hidden-bearing root. Negative availability of that root can
remove further extra fields through Function arguments, but cannot retain
a required hidden child or create a hidden output leaf. It does not require
the extra subgraphs to be visible or separately closed away from the root.

## A closed visible graph survives both signs

For any closed visible finite contractive regular graph `G`, assign true
to both signed states of every node. Every availability equation is
satisfied: visible atoms are true, and all required signed children of
each Function or Record are true. This is the top fixed point, hence the
greatest fixed point. Constructor cycles and mutual recursion introduce
no exception.

Projection retains every field and constructor edge. Relate each
projected signed node `(n,p)` to its original node `n`. Atom identity,
constructor head, Record label sets and each indexed child edge match;
the Function argument merely changes the sign of its projected target.
This relation is a bisimulation, proving `A+(G) ~ G` and `A-(G) ~ G`.

## Second inclusion: simultaneous closed-copy graft

Take any `V in R_H`, represented by a closed visible finite regular graph
`G`, with Record root `v`, root labels `E`, and child roots `v_f`.
Because `E intersect H` is empty, the following construction introduces
no duplicate root label.

1. Take a closed copy of all nodes and edges of `G`. Preserve all sharing
   and back-edges inside that copy, including edges targeting its root `v`.
2. Allocate a fresh Record root `r` outside the copied graph and an atom
   leaf with identity `kappa_h` for each `h in H`.
3. Give `r` the fields `h:kappa_h` for all `h in H` and `f:v_f` for all
   `f in E`, using targets in the copied graph. Do not redirect any copied
   edge to `r` or to a new hidden leaf.

Call the resulting rooted graph `T_V`. It is finite and contractive:
the copied constructor cycles are unchanged, and the fresh root introduces
only constructor edges. Its root labels are `E union H`, with the required
atomic child at every `h`. Therefore `T_V in F_H`. The comparison with
`U_H` asks only for these required fields and their identity comparisons.

The copied graph remains a closed visible subgraph. A fixed point of the
whole graft's availability equations is obtained by setting all copied
signed states true, all hidden-leaf states false, and `r+` true. Set `r-`
false when `H` is nonempty; its required hidden children force that value.
Set `r-` true when `H` is empty; all its copied negative children are true.
Thus the greatest fixed point keeps every copied signed state available,
including negative states reached through arbitrarily recursive Function
arguments. Hidden-leaf states remain unavailable.

At `r+`, projection drops all fields in `H`, retains every field in `E`,
and connects it to the positive projection of its copied target. Relate
`r+` to `v`, and every copied projected signed node `(n,p)` to original
`n`. At the fresh root, both sides have exactly labels `E` and matching
child targets under the relation. At copied nodes, the preceding visible
graph bisimulation applies. Hence `A+(T_V) ~ V`.

This constructs a preimage for every `V in R_H` and every finite `H` in
one operation. Together with the first inclusion it proves the asserted
image equality; no induction on graph depth or restriction on the number
of mutually recursive visible nodes is needed. The empty-`H` construction
also works, or one can simply take `T_V = V` in that case.

## Why the closed copy matters

For a nonempty `H`, choose a label `b` outside `H` and consider the visible
regular graph

```text
V = mu z.Record{ b:Function(z,Int) },
```

where `Int` is visible. Both signs of every node in `V` are available. If
one modifies its existing root by adding the fields `h:kappa_h`, instead
of taking a closed copy and fresh root, the modified root's negative sign
becomes unavailable. The positive sign of the `b` Function then becomes
unavailable because its argument points to that negative root. Consequently
the modified graph's positive root projection is `{}`, which is not
bisimilar to `V`.

The graft keeps that Function argument inside the original visible copy,
where the negative root remains available, so it preserves `b` and the
entire recursive structure. This is a counterexample to naive root
mutation, not to the image theorem. In the theorem, old references to the
copied root need not become references to the fresh root: rooted
bisimulation accepts the resulting duplicate representation of the visible
root. An additional observable graph-identity constraint would need a
different statement.

## Boundary and next obligation

All labels in `H` are forbidden only at the image root. Visible nested
fields with those labels are allowed and preserved by the graft. If any
required atom becomes visible, its root field survives, changing the image.
Additional lower bounds or correlated equality constraints can forbid a
grafted witness. The construction makes no claim about those extensions.

Permissions, comparison guards and `Phi` are absent from this theorem.
Its structural preimages need not be admitted by any supplied scoped or
joint package. No claim that projection eliminates an original witness
predicate, generates source constraints or yields an effective inference
procedure follows. Production authority, source rejection policy and
effectful compatibility remain outside the result.

An independent `compiler_referee` review of the frozen proof found no
blocking, major or minor findings. It checked both inclusions, the uniform
finite-label graft, empty `H`, arbitrary regular recursion, bisimulation and
the explicit exclusion of permissions, guards, `Phi`, source generation and
effective inference. The reviewer verified the target and direct dependency
hashes before review. Production correspondence was outside the review scope.

## Verification and commit packet

Verification budget: one output-only whitespace/link check and direct
dependency SHA-256 recheck. No tests, builds, executable model, measurements
or Git operations. The three direct dependencies below were inspected and
rechecked; no dependency hash changed during construction. The output has
a final newline, no tabs or trailing whitespace, and all three relative
Markdown source links resolve.

| Direct dependency | SHA-256 |
|---|---|
| `notes/design/2026-10-03-open-residual-factorization.md` | `02e6e04d1a4eea405442587206e34c653b45405677d653e6bfec37568fee4f43` |
| `notes/design/2026-10-03-scoped-structural-projection.md` | `b1b7e675902820d6e5d4488c656ab11332b4fc2f54dd64e0fa2cd2e5cf5519a0` |
| `notes/progress/2026-10-05-atomic-record-visible-projection-proof.md` | `96263d62870e8e7eda93879a2234b9069bb5ea9cad1af62afd288184a36879cd` |

Exact leased path:
`notes/progress/2026-10-05-multi-atomic-record-projection-proof.md`.
Baseline: `caad6f1676867bfc46631119eadce925f1d4fafa`.
Claim/review status: independently reviewed conditional constructive
structural derivation, uniform in finite `H`; no implementation authority.
Proposed one-line checkpoint message:
`research: derive finite multi-atomic Record projection image`.

Recommended next action: derive the exact additional admission premise needed
for graft witnesses under supplied permissions, guards and joint `Phi`; do not
infer that this structural image eliminates the original witness predicate or
is an effective projection.

Shared record deltas are intentionally deferred to the primary/curator:
`tasks/current.md`, `tasks/research-lab.md`, any inference theory/status
map, and `notes/design/INDEX.md`. Proposed delta after adjudication: record
the uniform finite-label structural image extension, its closed-copy
witness construction and its review scope, while retaining the
joint-admission, source-generation and effective-inference gates.
