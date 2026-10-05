# Source-preserving same-pivot replay: minimal missing data

Date: 2026-10-05
Status: bounded research candidate; independently reviewed, not adopted
Baseline: committed `b5c637eea` on `research/simple-sub-intrusion`
Scope: two original inequalities with a shared flexible pivot; context transfer
and source-conservation obstruction, without production changes
Claim class: specification underdetermination and a finite semantic witness
against unconditional mandatory replay; no source non-finiteness claim
Approved-by: none
Implementation authority: none
Supersedes: none
Review: compiler_referee and spec_auditor found no BLOCKING/major/minor
findings within the semantic-obstruction and authority scopes. The candidate
defines no admitted replay rule and has no source-wide realization.

## 1. Result

The inspected variable-bound policy does not determine a complete replay
context from

```text
p1 = [b1,j1] A <: X
p2 = [b2,j2] X <: B
```

even when `X` is one shared flexible endpoint and both originals are retained.
It specifies preservation obligations for a replay **if admitted**, but leaves
both admission and the parent-to-conclusion context/consumer map open. A
conjunctive provenance hyperedge preserves the missing data; its existence
does not discharge either missing law.

There are two separate obstructions. First, two parent judgments do not
universally entail a mandatory direct `A <: B` judgment under the selected
endpoint-dependent relation (§4). Second, retaining two distinct lexical and
witness contexts does not select the lexical scope, witness transport or
consumer of an independently admitted child (§3). The second obstruction is
about absent source data, not evidence that a valid rule is impossible.

## 2. Governing sources and retained input

All cited source files match the committed baseline; concurrent task/theory
edits and later commits are not premises.

- `rules/design-authority.md`, “Authority order” and “Approval and
  implementation gate”: an unapproved semantic candidate cannot become an
  implementation rule.
- [Concrete compatibility §1](../design/2026-10-03-concrete-compatibility-boundary.md):
  one inequality, endpoint-dependent resolution, variable-edge propagation,
  and concrete-success non-composition. Its §2, paragraphs beginning “If
  source preservation admits a replay” and “Keep original source comparison
  tasks”, leave admission open. Its §3 restricts applicability of structural
  fragment theorems; §6 requires two-way inequality-task conservation.
- [Scoped constraint solving §§1–3, 5](../design/2026-10-03-scoped-constraint-solving.md):
  finite regular structural fragment, identity-sensitive rigid permissions,
  common guard entry, original joint `Phi/K,D`, and retained open clauses.
  Its §3 is closed structural saturation, not a same-pivot replay rule.
- [Open residual factorization §§2–4.1](../design/2026-10-03-open-residual-factorization.md):
  `(b,j,u,v)` states, one assignment, retained `Guard/Phi`, and a conditional
  finite stable-context premise.
- [Finite context closure §§2–4](../design/2026-10-03-source-context-finite-closure.md):
  ordered multi-parent hyperedges retain all parents without granting their
  assumption union; a finite context carrier and sound context transitions
  are inputs. Its §6 explicitly leaves same-pivot source admission open.
- [Source guard derivation §5](2026-10-05-source-guard-finiteness-derivation.md):
  this exact two-parent seam is the missing source transition.
- [Operation instances §8](../design/2026-10-02-operation-instance-binding-package.md),
  “User-selected level discipline and the kernel's limit” and “Deriving
  lexical prefixes for the admitted unsealed equality core”: every admitted
  derived comparison re-enters the guard; deferred equalities retain their
  generating context; sibling opening identities remain distinct. These are
  necessary constraints, not subtype-replay admission or witness transfer.

Write each original context schematically as

```text
ji = (Gamma_i, L_i, W_i, E_i, Phi_i-refs, K_i-refs, D_i-refs, consumer_i)
pi = (bi, ji, qi(lower_i), qi(upper_i))
```

`Gamma_i` contains only assumptions available to that source check; `L_i`
retains opening ownership/order; `W_i,E_i` retain typed witness/evidence ports
and their incidence to endpoints and original symbolic coordinates. The
`Phi_i/K_i/D_i` notation denotes references into the original joint ledger,
not a claim that it factors into independent parent-local constraints.
Absent coordinates remain absent.

One `nu` interprets the whole ledger. There is one actual pivot identity
`q(X)` in both parents. Sharing that pivot neither equates the other endpoint
ports nor equates binder or witness ports. A context occurrence can retain a
reference to a private fact without granting that fact as an assumption in
another source check. Concrete outcomes and adapters are not replay inputs.

## 3. Minimal context-interface obstruction

Consider an abstract retained-context interface with an owning context `g`
and two distinct sibling openings:

```text
L1 = g / o1       L2 = g / o2       o1 != o2
owner(X) = g     p1 uses X          p2 uses the same X
```

This is the minimal two-parent context shape in the seam identified by source
guard derivation §5. It is not a claim that an executable source term already
generates arbitrary chosen endpoint/witness data. The operation-instance
unsealed equality construction permits separate sibling opening identities
and owning-context captures, subject to its checks; it does not establish
this shape's arbitrary subtype judgments or sealed lifecycle.

Keep the original incidence maps `I1,I2` for every parent witness/evidence
port, including `K,D` references where supplied. Thus a port `w1` owned by
`o1` and a port `w2` owned by `o2` remain distinct even if their names, levels,
types or interpreted values coincide. If a source linking map explicitly
identifies an imported port, retain that identity instead; do not manufacture
sharing from same-pivot presence. No actual request, packet or new witness is
postulated by this interface example.

The input determines the two saved contexts and common pivot, but supplies no
generating occurrence for a new `A <: B` check. In particular:

1. Selecting `j1` or `j2` as the child's full context requires a transport of
   the other parent's endpoint/evidence incidence into that context. None is
   supplied; merely retaining a parent pointer does not prove transport.
2. `g` is the common lexical ancestor in this shape. It does not make either
   private opening available there. Restriction to `g` would need its own
   checked endpoint/witness transport and cannot be inferred from equality's
   permission intersection theorem for arbitrary subtype replay.
3. The union `Gamma_1 union Gamma_2` is not one of these lexical contexts.
   It can expose sibling-private assumptions. Intersecting assumptions avoids
   that exposure but still does not construct the child's typed witness map,
   original `K,D` correspondence, guard or conversion consumer.
4. The pair `(j1,j2)` can be saved as derivation data. Treating it as a new
   independent checking environment requires a defined judgment and scope
   guard for that environment. The supplied finite-template theorem assumes
   this definition; it does not provide it.

Consequently the existing policies constrain but do not define a function
`ReplayContext(p1,p2) = j3`. More sharply, they do not provide a total replay
transition at all: no child may be needed. Equal numeric depth is insufficient
even in this smallest sibling shape. There is no demonstrated unbounded
context growth and no conclusion that finite contextual replay is impossible.

## 4. A tiny witness against unconditional mandatory admission

Use only the selected optional-Record outcomes recorded in concrete
compatibility §2. The finite endpoint inventory is

```text
S = string     I = int
A = {foo?: S}  Z = {}  B = {foo?: I}
nu(X) = Z
```

There is one flexible pivot, two original inequalities, empty lexical
contexts, `Guard = true`, `Phi = true`, and no `K,D` or request-witness ports.
The original ledger is interpreted under the single displayed `nu`. Direct
resolution of its two original tasks succeeds; direct resolution of
`A <: B` fails. This uses the three already recorded pairwise outcomes;
it does **not** compose their successes or propose a new comparison law.

Let `Orig(nu)` mean satisfaction of both originals under their own retained
contexts. If every such pair added `A <: B` as a mandatory rejecting check,
then this `nu` would satisfy `Orig` but fail the augmented ledger. Therefore

```text
Orig(nu) => Resolve(A <: B, j3, nu) succeeds
```

is false for unconditional admission even in the empty-context subcase. The
context obstruction cannot be repaired by selecting a context alone.
Eligibility might exclude this configuration, or an internal route might
serve another proven source-preserving purpose; neither is specified by the
two-parent pattern. This finite semantic witness is not an executable source
counterexample or a refutation of mandatory-Record structural transitivity.

## 5. What the safe hyperedge retains, and the exact missing proof

The information-preserving research interface is a provenance envelope:

```text
H = (ReplayRoute,
     ordered_parents = (p1,p2), pivot = q(X),
     source_incidence = (I1,I2), joint_ledger_ref,
     child = absent until justified)
```

Keep both originals as roots. `H` references their original `nu`-interpreted
ledger, contexts, ordered endpoints, scopes and evidence. It neither grants
combined assumptions nor introduces `K3,D3`, witness equalities, concrete
outcomes or an adapter. Parent conjunction lives on the provenance envelope;
it is not a shortcut replacing the two originals. This envelope is a proposed
research notation, not a selected solver representation or admitted rule.

A complete source-preserving rule must supply an admission certificate `a`
and an explicit transport `tau`, derived from an identified source route:

```text
(p1,p2; a,tau) --> H with child (b*,j3,q(A),q(B))
```

`b*` must have a stated source identity/derivation reference; a fresh path ID
cannot silently become an original source site. `tau` must determine the
child's available assumptions, lexical opening order/ownership, endpoint and
witness incidence, original `Phi/K,D` references and actual consumer. It must
specify which dependencies invalidate the child's guard/evidence. Resolving
the child re-enters the same guard before specialization, including on
recursive feedback; `GuardFailure` stays separate from structural failure.

For a mandatory child, prove for every one shared admissible `nu` that the
augmented ledger has exactly the original solutions/observable realizations.
Since retaining both originals already gives one direction, the nontrivial
direction is that the certified source route warrants this child and its
consumer evidence without introducing extra rejection. A failure of an
uncertified candidate child cannot refute the original ledger. Concrete
successes are never the premises of this proof. A finite closed structural
fragment consequence is not enough to establish general source replay.

Only after that rule is established can a finite closure argument identify
the finite ports/rule labels used by `a,tau`, prove their canonicalizer
preserves every distinction, and close recursive references by graph edges.
Writing `H` or the bound `|B| |J| |P|^2` alone proves none of these premises.

## 6. Checks, omissions and handoff

Method: bounded committed-source inspection and the five-entry endpoint
inventory in §4. No executable experiment was needed; experiment processes
and measurement samples: 0. No code, tests, builds, Git mutations, question
files, task/index/design/theory or existing progress writes were performed.
Whitespace check: `git diff --no-index --check -- /dev/null
notes/progress/2026-10-05-source-subtype-replay-context-candidate.md` passed
without diagnostics (exit 1 denotes the added-file difference).

Changed path: this note only. No independent review is claimed. Source-wide
context finiteness, executable source realization, eligible replay routes,
extrusion, scheme freshening, sealed witness lifecycle, conversion placement
and complete resolver semantics remain omitted. Shared record integration
belongs to the primary.

Fresh semantic approval is required if the research interface is promoted to
an admission/context/consumer rule; recording this obstruction selects none.
The next useful input is one concrete source route that supplies `a,tau`, or
a proof that replay is unnecessary for its chosen slice. Reusing a finite
context theorem or importing equality's lexical intersection does not supply
that route.
