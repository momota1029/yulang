# Conditional visible-query membership by admission retraction

Date: 2026-10-05
Status: Independently reviewed conditional derivation and abstract-predicate obstruction; research only, no implementation authority
Baseline: `4b093702f` (assignment baseline)
Observed later HEAD: `80b5749f0e5c2beccb080749713bf11d228439de`; primary confirmed unrelated checkpoint movement
Implementation authority: none
Exclusive write scope: this note only

## Inputs and exact question

The [residual factorization record](../design/2026-10-03-open-residual-factorization.md)
§§2–7 retains permissions, guards and joint coordinates on one assignment.
The [structural projection record](../design/2026-10-03-scoped-structural-projection.md)
§§2–6 supplies the regular structural relation and its visible-comparator
factorization. The independently reviewed
[multi-atomic Record image proof](2026-10-05-multi-atomic-record-projection-proof.md)
supplies the structural image and its closed-copy/fresh-root graft.

This note asks when that graft also provides an effective membership test
for the image of an admitted residual fiber. It proves a conditional theorem
for a supplied abstract predicate. It does not establish that production
`Guard` or `Phi` is effective, extensional, or closed under this graft, and
does not prescribe their syntax or meaning. The literal retraction premise
alone has an obstruction if the predicate can observe graph presentation;
that obstruction is given below.

## Fixed data and hypotheses

Use the atoms/Functions/mandatory-Records grammar and visibility classification
of the multi-atomic proof. Structural subtyping is its greatest simulation:
atoms compare by identity, Functions reverse their argument comparison, and
Records use width and covariant fields. Graphs are finite, closed and
contractive; their sizes have no common bound. Assignments and visible query
values are considered modulo rooted regular-tree bisimulation `~`. No
additional equality, graph-sharing identity, lower bound, interacting open
class, effect or declared-variance constructor is included.

After the fixed successful equality quotient, `X` is one descriptor-free
flexible class. Fix a finite required-label set `H`, hidden rigid identities
`kappa_h` for `h in H`, and finitely many fixed closed visible regular upper
queries `W_1,...,W_m`. The structural constraints are exactly

```text
X <= U_H,       U_H = Record{ h:kappa_h | h in H },
X <= W_i       for i = 1,...,m.
```

The empty cases `H = empty` and `m = 0` are included. As in the reviewed
proof, required identities may be taken pairwise distinct; the argument only
uses their hidden status. `W_i` may have any head in the stated grammar.
A non-Record `W_i` simply cannot compare above this Record-root fiber.

Let `Omega` be supplied as an explicit complete finite list of coordinates,
possibly empty, or equivalently by a terminating complete enumeration with
an exhaustion certificate. Mere enumerability of a finite domain does not
supply this exhaustion signal. For each `omega`, `P_omega` is the propagated
permitted set of rigid binder identities for this class, with an effective
membership test.
These permissions refer to identities, not spellings or levels. For a rooted
graph `T`, define

```text
Rigid(T) = the set of rigid identities reachable from its root,
Perm_omega(T) iff Rigid(T) subset P_omega.
```

Primitive atoms do not require a rigid-name permission. All permission
constraints on this single class are assumed represented by `P_omega`;
there are no additional identity-sensitive permission obligations.

Let `A(T,omega) = Guards(T,omega) and Phi(T,omega)` be supplied as one
predicate. Evaluating it uses the same original bound contexts, original
joint coordinates and witness `omega`, including guards on comparisons
actually reached for this candidate. No component is replaced by a
predicate independently guessed from the projection. The positive theorem
has these two explicit admission hypotheses:

1. **Effective extensional admission:** `A` is a total decision procedure on
   every finite contractive graph in this grammar and every `omega`; if
   `T ~ T'`, then `A(T,omega) = A(T',omega)`.
2. **One-way retraction:** for each relevant candidate `T` and the same
   `omega`,

   ```text
   A(T,omega) implies A(G_H(A+(T)),omega).
   ```

   It suffices to require this for candidates satisfying `T <= U_H`,
   `Perm_omega(T)`, and every `T <= W_i`. A premise covering all
   `T <= U_H` is stronger and also suffices. This is a candidate assumption,
   not a consequence of effectivity, structural projection or the original
   residual factorization.

Here `A+` is the projection operation, which is distinct from the predicate
`A`. Its positive root is always defined for this Record fiber. For visible
`V` with a Record root and `labels_root(V) intersect H = empty`, `G_H(V)`
is exactly the reviewed graft: copy the entire closed visible graph,
preserve its internal sharing and back-edges, then add a fresh root with the
copied visible root's field targets and the required fields `h:kappa_h`.
Copied edges are never redirected to the fresh root. This operation is
partial outside that visible root-label domain.

## Membership statement

Define the admitted fiber and its projected image:

```text
J = { (T,omega) |
        T <= U_H,
        T <= W_i for every i,
        omega in Omega,
        Perm_omega(T),
        A(T,omega) }

Image(J) = { [A+(T)]_~ | (T,omega) in J }.
```

Write `K_H = { kappa_h | h in H }`. For a supplied finite query graph `V`,
let `RootOK_H(V)` mean that it is closed, contractive, visible, has a Record
root and has no root label in `H`. Nested occurrences of these labels are
allowed. Define the test, with `G_H(V)` evaluated only after `RootOK_H(V)`:

```text
Member(V) iff
  RootOK_H(V)
  and V <= W_i for every i
  and exists omega in Omega:
        K_H union Rigid(V) subset P_omega
        and A(G_H(V),omega).
```

**Conditional theorem.** Under the fixed-data and admission hypotheses,
for every finite contractive query graph `V`,

```text
[V]_~ in Image(J) iff Member(V).
```

This is exact membership of a supplied visible value in the projected
admitted image. It is not an emptiness decision over all visible values,
an enumeration of the image, or a full inference procedure. In particular,
finite `Omega` does not make the infinitely many possible visible queries
into a finite search domain.

## Structural, permission and bisimulation facts

The reviewed image proof gives three facts, uniformly for finite `H`:

```text
T <= U_H implies RootOK_H(A+(T)),
RootOK_H(V) implies G_H(V) <= U_H,
RootOK_H(V) implies A+(G_H(V)) ~ V.
```

It covers arbitrary extra regular subgraphs in `T`, including feedback to
its hidden-bearing root. The graft's closed copy is essential: mutating an
existing visible recursive root can disable a negative projection and
therefore lose a field whose Function argument returns to that root.
No root field in `H` survives projection, since its required child is the
hidden atom `kappa_h`. These labels can survive at visible nested nodes.

For each closed visible upper query, projection §4 yields

```text
T <= W_i iff A+(T) <= W_i.
```

Apply this both to original candidates and to `G_H(V)`. With the graft
identity it follows that

```text
RootOK_H(V) implies
  (G_H(V) <= W_i iff V <= W_i).
```

These are unguarded structural facts. They neither prove that any particular
comparison guard admits a witness nor turn a guard failure into a structural
contradiction; admission remains the full separate predicate `A`.

Projection copies available atoms and constructor edges but creates no new
rigid identity. Thus

```text
Rigid(A+(T)) subset Rigid(T).
```

The required rigid identities are reachable in every `T <= U_H`. Every
rigid identity reachable in a visible `V` is reachable through one of its
root field children, since the root is a Record. The graft copies exactly
these children and adds the required atom leaves. Consequently

```text
Rigid(G_H(V)) = Rigid(V) union K_H.
```

An unreachable copy of the old Record root, if kept in an implementation
of the construction, does not affect this rooted set. Therefore

```text
T <= U_H and Perm_omega(T)
  imply Perm_omega(G_H(A+(T))).
```

If a required hidden identity is forbidden by `P_omega`, that coordinate
cannot witness membership. No admission closure premise can repair that
permission failure. Other hidden identities in `T` can be dropped; the
graft adds only required ones already reachable in `T`.

All structural facts above are invariant under rooted bisimulation. To
see projection invariance explicitly, lift a bisimulation to signed node
pairs. Corresponding states have matching availability equations. Starting
from all true, each descending iteration agrees on corresponding states;
stabilization gives the same availability. The resulting projected edges
also lift the original bisimulation. In the graft, relate the fresh roots
and corresponding copied field descendants; required atom identities match.
Hence

```text
T ~ T' implies A+(T) ~ A+(T') when defined,
V ~ V' implies G_H(V) ~ G_H(V') on its domain.
```

Reachable rigid identities match by finite paths through a bisimulation.
Structural subtype comparisons match by lifting their simulations. Admission
extensionality is the additional hypothesis needed to transfer `A` between
these bisimilar grafts. It is not inferred merely from the structural facts.

## Forward direction

Suppose `[V]_~ in Image(J)`, witnessed by `(T,omega)`. Set `V_0 = A+(T)`,
so `V_0 ~ V`. The structural image theorem and bisimulation give
`RootOK_H(V)`. Each `T <= W_i` factors to `V_0 <= W_i` and then to
`V <= W_i`.

By permission preservation, `K_H union Rigid(V_0) subset P_omega`;
bisimulation replaces `Rigid(V_0)` by `Rigid(V)`. The original candidate
is admitted, so the one-way premise gives `A(G_H(V_0),omega)`. Graft
bisimulation gives `G_H(V_0) ~ G_H(V)`. Extensionality therefore gives
`A(G_H(V),omega)`. The very same coordinate witnesses `Member(V)`.
No permission, guard or symbolic witness is selected independently.

## Reverse direction

Suppose `Member(V)`, witnessed by `omega`. Set `T = G_H(V)`. The graft
is finite and contractive and satisfies `T <= U_H`. Visible query
factorization gives every `T <= W_i`. The exact graft rigid set and the
permission test give `Perm_omega(T)`. The final membership conjunct is
exactly `A(T,omega)`. Thus `(T,omega) in J`.

Finally `A+(T) ~ V`, so `[V]_~ in Image(J)`. This direction never uses
`A(G_H(A+(T)),omega) implies A(T,omega)`. Such a reverse admission
condition is unnecessary: the canonical graft itself is the witness.
The one-way premise provides a representative in the admitted part of
every nonempty projected fiber, rather than asserting admission is constant
throughout that entire fiber.

## Effective termination without a graph-size cap

Given a finite query graph `V`, first check graph validity, visibility,
its root head and the root-label exclusion. A rejected input makes
`Member(V)` false without applying the partial graft. Next decide each
`V <= W_i` by finite ordered-pair simulation: start with all locally
compatible node pairs and remove any pair missing a required successor.
Every pair is removed at most once. This handles Function reversal, Record
width and regular cycles without unfolding them indefinitely.

Compute the finite set `Rigid(V)` by rooted reachability. Build one graft
of `V`; if `V` has `N` represented nodes, the explicit construction has
at most `N + 1 + |H|` nodes. Preserving a closed copy of `V` is essential,
but does not require searching larger candidate graphs. Traverse the
supplied complete finite list for `Omega`; for each coordinate passing its
rigid permission tests, invoke the supplied total decision procedure for `A`
on this graft.
Accept if any invocation accepts; reject once the list is exhausted without
acceptance. Empty `Omega` rejects immediately. The equivalent terminating
enumeration uses its exhaustion certificate for the same rejection step.

Each operation terminates on the supplied finite input, including the complete
coordinate list, and there are finitely many admission invocations. The
argument does not enumerate assignments, assume
a maximum size for all witnesses, truncate recursive unfolding, or choose
a source resource policy. It provides no uniform practical complexity bound
for the supplied admission procedure. It also fails if admission is merely
semidecidable: all rejecting coordinates can then diverge. The finite
coordinate premise cannot hide an infinite search for an original witness
inside the claimed effective predicate.

## Obstruction to the bare premise without extensional admission

Here is a presentation-sensitive total predicate for which the proposed
one-way premise holds, yet the displayed graft test is not exact modulo
rooted bisimulation. Use singleton `Omega`, all rigid permissions, one
upper query `W = {}`, and initially `H = empty`. Let `b` be one label.
Define `A(T,omega)` by the following finite graph inspection:

```text
T has a Record root with field b targeting a Record node q,
and q has field b targeting the identical graph node q.
```

One can take abstract `Guards = true` and `Phi = A`; this claims no
production-predicate correspondence. For any `T` satisfying this predicate,
both the root and `q` have their positive Record state available, and the
field `q.b` is retained as a self-edge on `q+`. The root's `b` field is
also retained. The closed copy preserves this self-edge, so

```text
A(T,omega) implies A(G_empty(A+(T)),omega).
```

Thus the one-way premise is satisfied for every relevant `T`.

Compare the visible regular queries

```text
V_1: one node r with r = Record{b:r},
V_2: two nodes r,s with r = Record{b:s}, s = Record{b:r}.
```

They are rooted-bisimilar. `V_1` is itself an admitted structural candidate,
with `A+(V_1) ~ V_2`; hence `[V_2]_~ in Image(J)`. But in `G_empty(V_2)`,
the fresh root's `b` child is the copied `s`, whose `b` child is the copied
`r`, a different node. Therefore `A(G_empty(V_2),omega)` is false.
In `G_empty(V_1)` that copied child has a self-edge and admission is true.

This uses one visible label and the smallest possible regular-cycle length
distinction, one versus two reachable visible nodes. A one-node cycle is
already the minimum nonempty cyclic presentation; two nodes are the first
presentation able to distinguish a self-edge from a cycle back through a
different node. This is a minimal counterexample for this self-edge test,
not a claim that every possible graph-sensitive predicate has this form.
If nonempty required `H` is wanted, use `H = {h}` with hidden `kappa`,
`h != b`, and choose the witness `G_H(V_1)` instead. Its root has
`h:kappa` and `b` targeting the closed one-node loop. It is admitted and
projects to `[V_2]_~`, while `G_H(V_2)` still fails the same predicate.
Permissions and `W = {}` continue to pass.

The obstruction concerns effective predicates that can observe representation.
If admission is defined on rooted regular-tree values from the start, its
extensionality is already part of that domain contract, and the conditional
theorem applies. Alternatively, supplying a fixed effective canonical graph
presentation to all admission evaluations changes the premise that must be
proved; this note does not choose such a representation or a production rule.

## Verification and handoff

Verification budget: source reading, direct dependency SHA-256 recheck and
one output whitespace/link check. No tests, builds, executable probes,
performance measurements or Git operations.
An independent `compiler_referee` reviewed the complete two-direction theorem
and presentation-sensitive obstruction. The initial major finding that a
finite enumerable `Omega` did not guarantee detectable exhaustion was
repaired by requiring a complete finite list or a terminating enumeration
with an exhaustion certificate. A narrow delta review confirmed the repair
closes the finding and that no other theorem text changed. No further findings
remain in the reviewed scope.
The derivation covers empty `H`, empty queries, empty `Omega`, forbidden
required rigid identities, root versus nested label exclusions, arbitrary
finite regular recursion, visible Function arguments and preserved closed-copy
feedback. Source-generation, production admission, additional structural
bounds and global image nonemptiness are outside the result.

| Direct dependency | SHA-256 |
|---|---|
| `notes/design/2026-10-03-open-residual-factorization.md` | `02e6e04d1a4eea405442587206e34c653b45405677d653e6bfec37568fee4f43` |
| `notes/design/2026-10-03-scoped-structural-projection.md` | `b1b7e675902820d6e5d4488c656ab11332b4fc2f54dd64e0fa2cd2e5cf5519a0` |
| `notes/progress/2026-10-05-multi-atomic-record-projection-proof.md` | `28548a4f1702f997f625fd4bc8b5f0925247618155c731deecab2e8538613208` |

Exact lease: `notes/progress/2026-10-05-residual-admission-retraction-proof.md`.
Baseline: `4b093702f`; observed unrelated checkpoint HEAD as recorded above.
Claim class: independently reviewed conditional mathematical derivation plus
abstract-predicate obstruction; no implementation authority. Dependency hashes
did not change during construction or review.
Proposed checkpoint message:
`research: derive conditional residual admission retraction membership`.

Recommended next action: determine whether any actual source-generated
admission class has the effective extensional representation and one-way
transport property required here. The source audit found no such derivation;
retain the original existential witness when it is absent.

Shared records intentionally deferred to the primary/curator:
`tasks/current.md`, `tasks/research-lab.md`, theory/status maps and
`notes/design/INDEX.md`. Proposed delta after adjudication: exact visible
query membership has a canonical-graft reduction conditional on total
extensional same-witness admission and one-way retraction; arbitrary
presentation-sensitive admission does not satisfy that conclusion from the
one-way premise alone. Production correspondence remains open.
