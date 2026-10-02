# Scoped structural projection for visible regular contracts

Status: Draft
Date: 2026-10-03
Reviewed-by: compiler_referee and spec_auditor, 2026-10-03; no findings in the bounded theorem/source-evidence package
Scope: partial best visible comparators for a pure regular structural fragment
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

## 6. Separate semantic correlation obstruction

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

## 7. Provenance and exact next gate

Structural variance and record width are Simple-sub precedents, as recorded
in the [pinned audit](../progress/2026-09-30-simple-sub-paper-mlsub-audit.md).
Existential opening and variable-only levels are user-selected Yulang
extensions. This partial-adjoint construction is a new successor candidate,
proved and independently reviewed only for the stated structural fragment.
No source-semantic approval or compiler implementation authority follows.

Next construct the full source graph generator and handling of unknown
endpoints, then complete effectful Function checking and invariant typed-family
and lifecycle transport. Show when actual source clauses enter this fragment
and preserve the remaining joint constraints. Historical exact-trace results
remain available where their premises apply; they are not mandatory eager
handling of unknown cross-scope targets. Source principality, full acceptance
and implementation remain later gates.
