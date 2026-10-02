# Scoped structural projection for visible regular contracts

Status: Draft
Date: 2026-10-03
Reviewed-by: compiler_referee and spec_auditor, 2026-10-03; no findings in the bounded theorem/source-evidence package or the separate §6 invariant/closed-import delta
Scope: partial best visible comparators, invariant support and closed-hole symbolic projection for a regular structural fragment
Implementation authority: none
Supersedes: no approved source rule or historical exact-trace theorem

## 1. Authority, obstruction and bounded source evidence

[Charter §§20, 22–23](2026-09-29-scc-intrusion-redesign-charter.md)
retain one existential request witness, guard generated comparisons, and place
levels on variables. The [exact staged-extrusion package](2026-10-03-staged-extrusion-solution-relation.md)
remains valid for its stated trace and relation. This package retires the
blanket hypothesis that eager exact-reference extrusion must handle every
unknown cross-scope structural target completely. It introduces no guard exception.

Under ordinary record width and call rules, the local judgment
`x:kappa, f:{} -> Unit |- f {field:x}:Unit` has a uniform derivation.
Comparison with the expected empty record asks for no field and generates
no comparison involving `kappa`. By contrast, eagerly extruding
`Record{field:kappa_l} <: Y_B` before solving captured outer `Y_B`, with
`B < l`, emits `kappa_l <: R_B`, rejected by the selected guard. This
shows why that eager step cannot be imposed as the complete successor route;
it does not invalidate the original algorithm's unscoped theorem.

Frozen commit `a58eefc3` supplies bounded structural evidence:

- `crates/infer/src/constraints/machine/propagate.rs:550–573` enqueues
  comparisons for matching expected fields.
- `crates/specialize/src/specialize2/type_graph.rs:760–796` first rejects
  missing required expected fields, then compares only matching fields.
- `crates/infer/src/lowering/pattern.rs:415–490` lowers an empty record
  pattern to empty positive and negative Record fields.
- `crates/infer/src/annotation/builder.rs:180–207` does not support
  `TypeRecord` annotations. No frozen acceptance of an explicit `{}` type
  annotation is claimed; use `my consume {} = ()` for the candidate consumer.

The following is an illustrative source skeleton, not an executed fixture,
accepted program, or proof of its whole-program inference:

```text
act sink:
    our put: 'a -> ()
my consume {} = ()
my make f =
    my run(action: [sink] 'r): 'r = catch action:
        sink::put x, k ->
            f {field: x}
            run(k ())
        v -> v
    run
my run = make consume
run: sink::put 1
```

The local width/call derivation is conditional on those ordinary rules.
The skeleton does not supply actual caller equations as generic-arm bounds
or establish source-template generation, syntax acceptance or effect checking.

## 2. The theorem domain and structural relation

Take finite contractive regular graphs with `N` nodes and `E` indexed child
edges. Nodes are atoms, Functions, or finite unique-label mandatory Records.
Atoms comprise primitives, visible rigid names and hidden opaque names.
Functions are contravariant in their argument and covariant in their result;
Records have ordinary width and covariant depth. Constructor heads have no
levels; visibility classifies variable/name leaves only.

Define `<=` as the greatest coinductive structural subtype relation. Atoms
compare only with the same atom. Function comparison requires the reversed
argument pair and ordinary result pair. Record comparison requires every
field of the upper record in the lower record, with comparable child types.
Different heads do not compare. A visible graph contains no hidden atom.
Contractiveness excludes unguarded recursion; constructor cycles remain regular.

This theorem domain assumes no Top, Bottom, unions, intersections, declared
hidden bounds, flexible constraint solving or effectful contracts. These
exclusions delimit the proof, not a selected source support envelope.

## 3. Availability and shared construction

On signed node pairs `(t,p)`, define availability as the greatest Boolean
fixed point of the following equations:

```text
visible atom: A+(t) and A-(t) available
hidden atom:  neither available
Function(a,b), sign p: available iff (a,-p) and (b,p) available
Record(fields), +: always available
Record(fields), -: available iff all (child,-) available
```

Start all `2N` states true and delete states falsified by these equations.
A worklist with indexed reverse dependency edges changes each state at most
once. With ordinary adjacency bookkeeping it scans `O(N+E)` nodes/edges;
this is a construction bound, not whole-solver complexity or a resource policy.
The descending result is the greatest fixed point: every post-fixed true set
survives deletions, and at quiescence the remaining set satisfies the equations.

For available pairs, construct a shared graph `A_p(t)`. A visible atom stays
itself. A Function uses `A_-p(a)` and `A_p(b)`. A positive Record retains
exactly fields whose positive children are available; a negative Record keeps
all fields with their negative projections. Unavailable pairs have no result.
Allocate one node per available signed pair and connect the indexed edges;
there are at most `2N` nodes and `2E` edges. Back-edges remain graph edges,
and constructor guarding preserves contractiveness. Failed availability means
no visible comparator in this fragment, never a source `ill-typed` verdict.

## 4. Partial best-comparator theorem

For every visible regular `u`,

```text
t <= u iff A+(t) is defined and A+(t) <= u
u <= t iff A-(t) is defined and u <= A-(t).
```

For existence, collect signed source nodes having some visible regular
comparator in the appropriate direction; the comparator may vary by node.
Comparable atoms must be visible. Function
comparisons furnish both required child comparisons with flipped argument
sign. A negative Record comparison furnishes all target fields; a positive
Record has no availability requirement. This set is post-fixed, so the
greatest availability fixed point contains it. Thus comparability implies
the required projection is defined, including along regular cycles.

Simultaneously establish `t <= A+(t)` and `A-(t) <= t` by coinductive
simulation on available pairs. Atoms use identity. Function arguments use
the opposite signed simulation and results the same sign. Positive Records
ask only for retained fields; negative Records provide every original field.
These finite graph relations are post-fixed subtype simulations and hence
belong to the greatest subtype relation.

A second simultaneous coinduction proves bestness: from `t <= u` derive
`A+(t) <= u`; from `u <= t` derive `u <= A-(t)`. Function children use
the opposite/same signed conclusions. For positive Records, any field asked
for by visible `u` has a comparable visible child, so existence above makes
that child available; it cannot have been omitted. For negative Records,
`u` already provides all original fields and the negative child conclusion
applies to each. Atoms use identity. This supplies a post-fixed comparison
relation even for cyclic graphs. The reverse implications follow by composing
with the simulations. Transitivity follows by composing simulations: for
`s <= t <= u`, the composite pairs matching atoms, reverses both argument
comparisons for Functions, and obtains each field required by `u` through
`t` from `s`. Child pairs stay in the composite relation, which is post-fixed
and therefore contained in the greatest structural simulation.

## 5. Scope safety, substitution and joint clauses

Generated structural derivations never compare a hidden atom with an outer
endpoint. A positive omitted Record field has no child obligation. Retained
subderivations follow identity and ordinary constructor comparisons on the
available signed graph; their atomic identity cases involve visible atoms.
This proves a fragment construction that respects the guard without an
exception or a hidden-atom substitution into an outer port.

Uniform substitution of hidden names by the actual request-package map
preserves these structural proofs. Shared occurrences retain the same witness;
constructor and identity steps survive substitution, and omitted fields
remain unasked. This establishes soundness after proof substitution, not
reflection or completeness after concrete instantiation. It is not commutation of projection
with substitution: substitution may change visibility and hence availability.

During generic checking, hidden leaves remain opaque and the symbolic original
term `t` stays fixed. Assignments `nu` range over visible outer endpoints.
Define `C(t,Y;nu) = (t <= nu(Y))` in this structural relation with `kappa`
opaque. The theorem factors exactly this clause through `A+(t)` (and its
negative dual through `A-(t)`), conjoined with unchanged `Phi` over the same
joint coordinates and the retained original graph. Undefined projection makes
this opaque structural clause false. This is not pointwise denotational
equivalence after an actual `kappa := Int` substitution: opaque `t=kappa`
has no projection toward outer `Int`, whereas its concrete instance compares
by identity. No arbitrary same-assignment semantic constraint is eliminated.
No typed-evidence rewrite, independent marginal solution choice,
new-port invariant decomposition or whole effectful relation theorem follows.
No witness/evidence is deleted and arbitrary invariant/effect atoms are not
automatically processed. The bestness result is relative principality within
this structural syntax, not semantic inclusion across all models.

## 6. Invariant coordinates and symbolic unknown inputs

This extends the mathematical fragment of §§2–5, under
[charter §§10–12, 20, 22–23](2026-09-29-scc-intrusion-redesign-charter.md).
It supplies a common variance construction, not a site-specific source rule,
an adopted effect representation or complete operation compatibility.

### Declared variance and visible-equivalent support

Add a finite signature of fixed-arity labelled constructors `C`, each with
a declared variance vector drawn from `+`, `-`, `=`. Same-head comparison
retains a positive child comparison, reverses a negative child comparison,
and requires mutual structural subtyping for an invariant child. Other heads
do not compare. These are structural relation clauses; heads still have no
levels. Records retain mandatory width/depth and Functions their earlier rules.

Use three modes `U,L,I`: upper availability, lower availability, and
visible-equivalent support. `I(t)` holds exactly when the whole rooted graph
is hidden-free. Equivalently, a visible regular `u` exists with `t <= u`
and `u <= t`. Necessity follows by mutual structural simulation: record width
in both directions forces identical labels and mutual child comparisons;
Functions and declared-variance constructors force both directions at every
coordinate. Any finite path to a hidden atom would require that same atom
in `u`, impossible for visible `u`. Sufficiency uses `u=t` and identity.
Every reachable hidden atom has a finite path even in a cyclic regular graph.

`I` is not ordinary equality validity. The local identity `kappa ≈ kappa`
remains valid although `I(kappa)=0`; `I` asks for a visible equivalent.
Compute `I` as the greatest conjunction of all child `I` states, with visible
atoms true and hidden atoms false. Keep the earlier `U,L` equations. For
`C` at sign `p`, a `+` coordinate requires mode `p`, a `-` coordinate
requires `-p`, and an `=` coordinate requires `I`. Construct its signed
projection with the corresponding signed children; invariant coordinates
retain the original child root and identity, without polarity approximation.
An `I` projection is the original `t` itself and exists only when `I(t)`.

The §4 proof extends by simultaneous coinduction. Comparability at an invariant
coordinate supplies a visible mutual comparator, hence `I`; the unchanged
child factors through that comparator by the original mutual comparison.
For other coordinates use the same/flipped signed conclusion. The two
simulation directions and bestness therefore hold for the extended grammar.
Scope safety extends as well: an invariant retained child is entirely
hidden-free, and generated signed subderivations use the prior rules.

There are at most `3N` mode states/roots. Indexed Boolean propagation still
costs `O(N+E)` for this fixed graph; existing original graph nodes may be
referenced by invariant outputs. This is not a whole-solver bound.

### Five profiles do not classify types

Two signed bits cannot express invariant support. For

```text
t = Record{f:Function(Record{g:kappa},Int)}
(U,L,I)(t) = (1,1,0)
A+(t) = {}
A-(t) = {f:Function({},Int)}
```

Neither output can replace `t` in an invariant coordinate. This is the
ordinary invariance requirement, not a new fixture-specific obligation.
Since `I` implies both signed availabilities, at most five profiles occur;
all five are realized when hidden `kappa` and visible `Int` are available:

| `(U,L,I)` | Example |
|---|---|
| `000` | hidden `kappa` |
| `100` | `Record{g:kappa}` |
| `010` | `Function(Record{g:kappa},Int)` |
| `110` | the enclosing Record in the example above |
| `111` | `Int` |

Profiles classify projection control only, not types, subtyping or equality.
`Int` and `Bool` both have `111`; matching bits never discharge `Eq(X,Y)`.
An alphabet without hidden atoms, or a hole restricted to visible inputs,
has a smaller admitted profile domain.

### Effective finite transformer with closed imports

Fix a finite contractive open template with `m` flexible holes, possibly
repeated, and one visibility frontier `H`. A substitution `sigma` assigns
each hole a closed regular graph over the same visible/hidden atom alphabet.
Imported graphs have no references back into the template or to open holes.
They may share nodes/aliases and depend mutually on known imported roots:
treat their union as one closed graph with common identity and projection
map. All occurrences of a hole share the same original imported graph;
different roots in that union create no fresh witnesses.

Compile greatest Boolean equations for the template's local `U,L,I` states,
using each imported hole's profile as constants. For every such `sigma`,
these equations give exactly the profile of the substituted graph `t sigma`.
To prove this, restrict the global greatest fixed point to the closed import
union: its states satisfy that union's equations. The union's own greatest
fixed point bounds that restriction from above. Conversely, combine that
fixed point with the greatest local solution using its root profiles; closure
of imports makes the combined assignment a global fixed point. Maximality
forces equality of the restrictions and of the local states. Cycles inside
the template and inside imports remain greatest-fixed-point equations.

Output construction references the same imported `A+(sigma X)` or
`A-(sigma X)` at signed hole occurrences, and the original `sigma X` at
`I` occurrences. Repeated uses remain correlated to that one imported input.
Positive Record field edges are retained exactly when the child's `U` holds;
whole-node availability follows the equations. Constructors with unavailable
required coordinates produce no output. This is an effective type transformer,
not a solver hidden behind an availability predicate.

A finite symbolic template may enumerate at most `5^m` profile branches,
each with at most `3N` local mode nodes, where `N` counts template nodes.
Imported output graphs are referenced, not counted as constant-size objects;
total size bounds add the shared imported graph and projection sizes.
Closed imports are essential:
self-dependent constraints or aliases feeding back into the template require
joint equations, not independently guessed profile assignments.

### Root factorization and remaining source constraints

For every closed `sigma` and visible outer target, §5's opaque structural
root-clause factorization applies uniformly to `t sigma`. Retain unchanged
`Phi` and the original joint coordinates. Invariant equations and source
`K,D` stay on original shared endpoints and travel jointly; they are never
rebuilt after concrete row materialization. Imported projected roots are
derived outputs correlated to original `X`, not independently instantiable
ports. Symbolic residual conditions while a hole is unknown are proof notation
for the existing relation, not a new source-obligation kind or implementation.

More generally, on the domain of a defined projection `q`, a predicate `Phi`
can be reconstructed from projected coordinates exactly iff it is constant
on each fiber of `q`. Reconstruction implies constancy for equal images;
conversely constancy defines the predicate on each image independently of its
chosen preimage. Equality generally fails this criterion: positive projection
maps both `{f:kappa}` and `{}` to `{}`, while mutual structural equality
with original `{}` differs. Exact rewriting of one structural inclusion
therefore does not permit rewriting every incident invariant edge. The `=`
constructor mode uses the explicitly admitted mutual-structural-comparison
law, not complete family `OpCompat` or arbitrary semantic `Eq_nu`.

For example, `Record{f:X}` projects positively to `{}` under `X=kappa`,
but to `{f:Int}` under `X=Int`. Eagerly dropping the unknown field or blindly
treating it as visible loses this best-comparator behavior. Recompute profiles
when substitutions change; this is no frontier-change or freshening theorem.

This finite presentation covers projection only. Five states cannot encode
flexible-bound satisfiability, complete source inference, arbitrary declared
bounds, lattice types, open rows, effectful contracts, complete `OpCompat`,
invariant family schemas beyond structural equality, or milestone-4 lifecycle.
Next solve source-generated joint constraints while retaining these summaries;
no source support envelope is narrowed and implementation remains unauthorized.

## 7. Separate semantic correlation obstruction

A mathematical all-model example reinforces why structural derivability must
be stated. Let `D` be the powerset of two value tokens `0,1` and four unary
Boolean-function tokens. Interpret `Function(C,E)` as the function tokens
mapping `C intersect {0,1}` into `E intersect {0,1}`. Let hidden `X` range
jointly over singleton `A={0}` and singleton `B={1}`, and fix outer
`a=Function(A,A) union Function(B,B)`. It excludes swap, while the original
uniform `Function(X,X) <= a` holds. Uniform links `N <= X <= P` force
`N` empty and `P` to contain both values. Retried `Function(N,P)` contains
swap by the empty-domain condition, so cannot lie below `a`.

This carrier example is not established source declared-bound or union typing,
and does not allow actual callers to specialize a generic arm. It separates
a chosen structural proof relation from an unrestricted all-model correlation
claim; it selects no source rejection rule.

## 8. Provenance and exact next gate

Structural variance and record width are Simple-sub precedents, as recorded
in the [pinned audit](../progress/2026-09-30-simple-sub-paper-mlsub-audit.md).
Existential opening and variable-only levels are user-selected Yulang
extensions. This partial-adjoint construction is a new successor candidate,
proved and independently reviewed only for the stated structural fragment.
No source-semantic approval or compiler implementation authority follows.

The §6 symbolic transformer closes projection for the stated closed imports,
including structural invariant coordinates, not flexible inference constraints.
Next construct and solve the full source-generated joint graph while retaining
these summaries and handling feedback/unknown endpoints, then complete
effectful Function checking and invariant typed-family and lifecycle
transport. Show when actual source clauses enter this fragment
and preserve the remaining joint constraints. Historical exact-trace results
remain available where their premises apply; they are not mandatory eager
handling of unknown cross-scope targets. Source principality, full acceptance
and implementation remain later gates.
