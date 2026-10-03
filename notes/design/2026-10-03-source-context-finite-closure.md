# Finite guard and evidence contexts for supplied open templates

Status: Draft
Date: 2026-10-03
Scope: conditional finiteness of comparison-context closure for a supplied finite linked open-template graph
Approved-by: none
Reviewed-by: architect pre-write audit; after repairing the finite-label-carrier gap, bounded compiler_referee/spec_auditor delta reviews of the conditional closure theorem found no remaining findings; bounded compiler_referee/spec_auditor reviews of §4's supplied-derivation root-context corollary found no findings (2026-10-03)
Implementation authority: none
Supersedes: none

## 1. Purpose and limit

The [open residual factorization candidate](2026-10-03-open-residual-factorization.md)
has a finite-state bound conditional on a finite set of stable comparison
contexts. The [source-wide audit](../progress/2026-10-03-source-guard-context-audit.md)
maps the missing source obligations but does not prove that source comparison
generation supplies such a context set. This note isolates the narrower
closure theorem for a **supplied finite linked open-template graph**.

It does not prove that every source program generates such a graph, that
generalization or freshening produces only admissible instances, that residual
bounds are effectively satisfiable, or that the result is principal for the
complete source language. It selects no new source rule, rejection policy,
solver representation, or resource limit. The user's approved variable-level
guard remains in force: every derived comparison must re-enter the same guard
before committing a forbidden specialization.

## 2. Finite template interface

Fix a supplied finite linked template graph `T` with:

- `B`: finitely many original comparison-site identifiers;
- `P`: finitely many endpoint and descriptor ports, including shared imports
  and original `K,D/Phi` references;
- `L`: finitely many lexical binder ports, each carrying its owning block and
  the source-defined opening/level order;
- `W`: finitely many declaration/request witness ports and their incidence to
  endpoint ports;
- `E`: finitely many typed-evidence and source-position ports;
- `R`: finitely many rule schemas which create, decompose, transport, replay,
  or invalidate comparisons; and
- `A_T`: a finite canonical label alphabet for rule outcomes and evidence
  incidence, formed from fixed rule identifiers and finite references to
  `B`, `P`, `L`, `W`, `E`, and canonical comparison states.

An open template does not enumerate future concrete witness names or runtime
execution identities. Its maps name ports and preserve which occurrences
share an endpoint or witness. A supplied linking map may identify imported
type ports only where the source map permits sharing; it keeps owned binder,
evidence, and comparison-site identities distinct. A consistent fresh renaming
of bound proof names changes no port incidence or source opening relation.

Use a canonical comparison state

```text
s = (b, j, u, v)
```

where `b in B` is the immutable originating obligation, `j` is a canonical
context over the finite interface, and `u,v in P` are endpoint ports. `j`
retains the lexical assumptions, witness correspondence, source evidence and
joint symbolic references required by `b`. Context equality is modulo only
consistent fresh renaming of bound proof names. It does not identify sibling
opening ports merely because their printed names or numeric levels match.

Each provenance hyperedge has a label in `A_T`, an ordered finite tuple of
parent states and a finite tuple of conclusion states. Composed evidence is
represented by references to canonical states and hyperedges, not by newly
nested path expressions. The supplied template must provide a
meaning-preserving canonicalizer into `A_T`; fresh-name renaming or endpoint
shape growth cannot be silently discarded to make a label fit this alphabet.

The finite context carrier `J_T` is an explicit input to this theorem, not an
assumed global universe of source contexts. Every rule schema in `R` must
construct its successor context inside `J_T`. In particular:

- structural decomposition inherits `b` and `j`; it does not mint a path ID;
- aliases remap endpoint ports and invalidate dependent checks without
  replacing the original context;
- a multi-parent rule records one labelled hyperedge with all parent states
  and their witness/evidence incidence; it does not grant the union of parent
  assumptions to a new independent check;
- recursive feedback points to an existing canonical state or hyperedge; and
- guard evidence is recomputed or invalidated when its recorded endpoint or
  permission dependencies change.

Alternative source obligations remain distinct roots in `B`. Parent
conjunction is carried by the hyperedge, so canonicalizing equal endpoint
pairs cannot erase whether evidence was alternative or conjunctive.

## 3. Conditional closure theorem

Let `N = |P|`, `M = |B|`, and `J = |J_T|`. Assume:

1. `T`, its endpoint graph, `B`, and the rule-schema set `R` are finite.
2. Each comparison-producing rule has uniformly bounded parent and conclusion
   arities and is **context-closed**: for every admitted input state/parent tuple, it emits
   only states in `B x J_T x P x P` and hyperedge labels in `A_T`.
3. The `A_T` canonicalizer preserves every rule-relevant evidence distinction.
   Labels cannot recursively wrap prior labels, embed unbounded derivation
   history, or introduce endpoint constructors outside `P`. Recursive proof
   and evidence relations use back-references to canonical states/hyperedges.
4. Rule behavior depends on canonical states, finite labelled operands and
   finite recorded dependency values, not on derivation-tree depth or a fresh
   identity for each path.
5. Binder transport is equivariant under consistent fresh renaming and
   preserves binder ownership, sharing, and the source-defined opening/level
   order. Sibling binders remain distinct ports.
6. Every multi-parent rule is sound under one shared assignment and retains
   all parent assumptions conjunctively. It cannot expose a caller-private
   equation as a generic-arm assumption or split shared witnesses into
   independent copies.
7. Dependency updates are finite and terminating: either closure is monotone
   over a finite information order, or every invalidation decreases a stated
   finite measure and each state is rechecked fairly after relevant changes.

Then the canonical state universe has at most

```text
M * J * N^2
```

states. For each fixed finite rule set, finite label alphabet and uniformly
bounded parent/conclusion arities, only finitely many canonical labelled
hyperedges can be formed:
each edge selects a rule, label, parent tuple and conclusion tuple from finite
sets. Fair exhaustive closure therefore reaches a finite cyclic provenance graph;
arbitrarily long derivations are represented by graph back-edges rather than
unfolded path identities. If every rule schema also preserves its source
judgment under the same shared assignment, the closed graph retains the
conjunction of the supplied source obligations and their guard/evidence
contexts.

This uses the supplied finite `J_T` in the residual normalization bound for
this particular `T`. It does not construct `J_T` or `A_T` from source rules,
prove their canonicalizers sound, or establish that source generation
supplies a valid `T`. Those require the separate rule-by-rule source bridge.

### Proof sketch

The product `B x J_T x P x P` is finite. Every admitted transition creates
states only in this product and a hyperedge whose label and ordered parent and
conclusion tuples range over finite sets. There are finitely many such
canonical hyperedges. Canonical state and hyperedge interning prevents a
recursive back-edge from making a new identity merely because its derivation
path is longer. The finite-update premise rules out
infinite retraction/republication of guard facts. Thus fair closure processes
finitely many state and hyperedge changes and terminates in a finite graph.
Inductively, each state retains its originating obligation and exact `j`; each
hyperedge retains the source rule and all of its parent states. Under the
shared-assignment soundness premise, adding or reusing a hyperedge preserves
the conjunction of the original judgments. Fresh renaming preserves this
argument because it preserves port incidence and binder relations.

This is a finiteness argument, not a proof of the seven semantic/context
premises. In particular, putting an infinite source context into a nominally
finite `J_T` by forgetting distinctions would violate premises 3, 5 or 6
rather than establish the theorem.

## 4. Supplied derivation roots for representation-preserving checks (candidate)

There is a bounded root-context corollary for the checking fragment of
`typed-computation-core-elaboration.md` §7. Take a finite §6 derivation graph,
its original contracts, supplied typed `Flow`/receipt correspondences, one
shared assignment `ν`, and a finite set of proof-only checks of the forms
`Check(Value(A),Value(B))` and
`Check(Computation(E,A),Computation(F,B))`. Do not add source conversions,
scheme instances, adapters, or new source introduction/consumption sites.

Assign each source check occurrence its existing annotation/check site `b`
and the generating context already present in the derivation. Keep `b` stable
through recursive source references; two distinct source occurrences remain
distinct even if they have equal endpoint terms. Store endpoint paths,
typed evidence references, source witness correspondence and shared `K,D`
incidence in the finite supplied ports, under the same `ν`. Typed `Flow`
transport changes which corresponding paths carry the view; it retains the
original predicate identity, source evidence tags, and lexical check context.
For a multi-input transport, retain each indexed source map and its witness
tag, rather than combining their lexical assumptions into a new check
environment.

Under those premises, adding or erasing the finite proof labels creates no
new runtime instruction, receipt, receiver boundary, view introduction, or
source demand. The included interface constraint and its original annotation
and evidence references remain. The set of roots is finite because it is
indexed by the supplied finite source/check graph, and the context carrier is
finite because every referenced port comes from that graph's finite `P`,
`L`, `W`, and `E` sets. The executable graph is unchanged. This is the
composition of the proof-label erasure theorem in core-elaboration §7 with
typed-boundary §6's path-indexed transport; it does not add a new source rule
or an independent context identity.

This corollary establishes only **initial root/context retention** for the
supplied derivation. It does not generate annotation roles or typed paths
from raw syntax, prove a complete `A <: B` decomposition, close replay or
aliases, instantiate schemes, admit a value conversion, or establish
source-wide `J_T` finiteness. In particular, a check inclusion is not an
executable adapter, and adapter placement cannot be inferred from this
erasure result. Those remain separate source-bridge premises.

## 5. Why alpha-only instance enumeration is insufficient

Fresh-name equivalence alone cannot make all recursive source instances
finite. A synthetic port transfer

```text
t  -> Box(t)
t, Box(t), Box(Box(t)), ...
```

creates infinitely many constructor-distinct endpoint shapes, and renaming
bound names does not identify them. This is not a source example or a
non-finiteness result for Yulang. It shows only that a proof cannot infer
finite instance closure from alpha-renaming of a literal instance enumerator.
The source bridge must either prove that the actual SCC/use rules do not
generate this recurrence, or represent the permitted family by a sound finite
parametric/recursive schema and prove its instance completeness. Current
parametric-linking evidence treats finite supplied instance graphs only and
leaves source polymorphic recursion, use-site freshening and shape-dependent
instance generation open.

## 6. Rule-by-rule source bridge still required

Before using this theorem for source-wide finite `J`, establish that every
source comparison origin and derived rule is represented, including:

1. annotations, executable conversions, ordinary Function/Record comparison,
   and complete invocation/callback ports;
2. operation request packing/opening, uniform handler-arm checking, and
   retained shared `K,D` witness correspondence;
3. structural decomposition, variable aliases, same-pivot bound replay,
   extrusion, and multi-parent provenance;
4. dependency invalidation when aliases, levels, permissions, or shared
   endpoints change;
5. external use-site instantiation and internal SCC references, with a proof
   that each finite linked program yields a permitted finite template graph;
6. sealed request/result/store transport without exposing caller-private
   assumptions; and
7. consumer placement for any cast/adaptation evidence retained by a
   comparison.

All source comparisons use the same `A <: B` judgment with endpoint-dependent
solver transitions. Variable-edge propagation may be transitive, but concrete
resolution outcomes and their cast/adapter evidence are not premises for a
third concrete comparison. In particular, success of `A <: X` and `X <: B`
does not by itself authorize creation of a new `A <: B` task; a same-pivot
replay needs its own source-preserving internal route rule. Optional Record
comparisons remain the counterexample to composing concrete successes.

No source acceptance boundary, compiler representation, or implementation
gate is selected here. No tests, builds, or measurements are required for this
conditional closure statement; the proof work concerns the stated finite
products and source-rule premises.
