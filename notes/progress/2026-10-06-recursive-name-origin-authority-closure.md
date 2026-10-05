# Recursive Name origin: authority closure and the interface-supply frontier

Date: 2026-10-06
Status: Draft research derivation / not independently reviewed / no authority change
Baseline: `ee9bc4bdf03bfe76be2d56aed86844f7a38e73cd`
Branch: `research/simple-sub-intrusion`
Exclusive lease: this file only; no implementation authority

## Result and exact authority

Authority closes origin conservation for **supplied interfaces** at Name/Result
synthesis, and requires transport of existing scope/dependency relationships
through generalization/use. It does not supply an origin-bearing recursive
interface formation/use judgment. Origin uncertainty can be concentrated at
that supplier: circulating a label around finite copy edges cannot ground an
introduction. Actual source seeds or another justification rule remain unknown.

The exact governing sections are:

- [Result synthesis §§1,3–5](../design/2026-10-02-source-result-synthesis-choice.md):
  inert lookup; `Synth(name x)=Gamma(x)`; `Result(Value(A))=Comp(empty,A)`;
  `Result(Computation(E,A))=Comp(E,A)`; correlated profile/`K,D` transport;
  complete recursive checking/generalization remains a proof gate.
- [Charter §§1–2,20–23](../design/2026-09-29-scc-intrusion-redesign-charter.md):
  retirement of F5 successor contracts; request-witness correspondence;
  ordinary parameter role and fresh inferred value endpoint; every-derived-
  comparison existential guard; variable-only levels. Section 24 selects
  ordinary unannotated literals' Pure role, but introduces no origin rule.
- [Inferred Function call views §§1.1,2,5](../design/2026-10-05-inferred-function-call-views.md):
  source/public/internal layers differ; shared source relationship, stable
  positions and lexical scope survive generalization/instantiation; exact
  judgments and preservation proofs remain open.

The [experimental transport](../design/2026-10-04-intrusion-experimental-transport.md)'s “Bounded implementation gate” and
preceding scope paragraph expressly leave source-local IDs, member bounds,
root generation and transported evidence validity as inputs, not decisions.
The [collection foundation](../design/2026-09-20-constraint-collection-scc-foundation-draft.md)'s “Deferred semantic gates” expressly defers
freshening/generalization variables and recursive Function skeletons. Neither
transport approval nor open/closed scheduling therefore fills this origin rule.
The index is a locator. The public reference paths are absent from this branch,
but the primary retrieved their exact versions from main at
`d4c8bc8fc8a49173180932cd25921a2c41057354` through the GitHub connector:
[Values & Types](https://github.com/momota1029/yulang/blob/d4c8bc8fc8a49173180932cd25921a2c41057354/web/docs/reference/types.md)
documents polymorphic Function values, fresh instantiation of quantified
variables and permitted recursive Function SCCs;
[Type Inference Theory](https://github.com/momota1029/yulang/blob/d4c8bc8fc8a49173180932cd25921a2c41057354/web/docs/reference/type-theory.md)
explicitly describes itself as a public guide, not a full solver specification.
Neither supplies recursive R source origins, §22 introduction levels, or the
occurrence-row correspondence. These references refine the compatibility
inventory; they do not restore retired F5 requirements or impose a successor
value restriction. Prior notes supply research evidence only.

## Envelope and three different uses of existential language

Fix normal parsing/resolution of

```text
my f x = g
my g y = f
my h_i = d_i       (1 <= i <= m, m finite, d_i in {f,g})
```

There are no other items, anchors, annotations, requests, handlers or alias
uses. Observe completed incoming routing before later alias generalization.
This research envelope selects no new supported-language boundary.

Three notions cannot be substituted for one another:

1. `exists nu. Sat(C,nu)` in a graph/member relation quantifies mathematical
   assignment witnesses. It neither opens a source package nor declares a
   type variable subject to §22.
2. F5 `Q/R` classify legacy scheme storage. Here `Q=[]`, `R=[r0]`; a use
   allocates one fresh solver row `rho_h` for the repeated R ordinal.
   Recursive guardedness and fresh identity do not classify source origins.
3. A source introduction has an event, a binder/variable correspondence and
   an introduction level. Charter §20 selects request package opening and
   distinguishes hidden binders from solvable inference existentials. Only
   an actual correspondence to the selected §22 antecedent licenses its
   guard. The examined syntax has no §20 request-opening event.

The member-scheme bridge's witness shifts (`rho=F(s_g)`; parameter witnesses
eliminated by Top) prove conditional projected relation equality. They supply
no variable-origin transport: a constructor expression is not a variable-level
introduction certificate; eliminated coordinates do not certify R's origin.

## Derived closure: a supplied interface is conserved

Write `O(I)` for the source introduction-event identities and their joint
binder/scope/dependency correspondence already carried by interface `I`.
This is proof notation, not a proposed runtime field or a definition of which
events count as §22 introductions.

**Conservation lemma.** For any already valid supplied interface, the selected
Name and Result rules preserve its existing origin correspondence and contribute
no additional source binder introduction in those steps:

```text
O(Synth(name x)) = O(Gamma(x))
O(Result(Value(A))) = O(Value(A))
O(Result(Computation(E,A))) = O(Computation(E,A)).
```

Proof. Name copies exactly the premise interface with its source positions.
`Result(Value(A))` adds the selected pure computation wrapper, containing no
fresh binder; the computation case forwards the existing interface. None has
a package-opening, fresh type-variable or witness-selection premise. Sections
1 and 4 reject an implicitly inserted extra layer or a public result-choice
parameter. Section 3 retains the corresponding profiles and symbolic `K,D`.
Charter §20 additionally forbids treating a copied request witness as an
independently solvable witness. These statements concern these synthesis
steps; they do not classify the derivation supplying `Gamma(x)`.

Generalization/use must preserve a relationship already selected by the source
component, its position identity and lexical scope (call-view §2). This necessary
authority constraint does not complete the source-to-row map or prohibit every
unspecified inference-variable introduction at that boundary.

The two bodies copy supplied `Gamma(g),Gamma(f)`; each alias copies its supplied
use interface `I_(d_i,u_i)`. Inertness, purity, unusedness and occurrence
freshness cannot remove an existing origin. Name synthesis cannot explain
a new origin at that occurrence.

## Finite SCC consequence, without assuming least recursive semantics

**Finite-copy theorem.** Let a finite directed rule graph represent only the
Name/Result transport edges above, with a separately supplied set of grounded
origin events at its frontier. Every origin having a finite justification
consisting of a frontier event followed by copy edges is reachable from that
frontier. Reachability stabilizes after at most `n-1` edges on an `n`-vertex
graph. A copy cycle contributes no new grounded introduction event.

Proof. Induct on the finite justification length for the first claim. Erase
repeated vertices from a reachability path for the bound. An introduction
must occur at its grounding event; traversing a copy edge only retains it.
This proves closure of supplied origins for all finite alias inventories,
without a carrier, subtyping law, solver execution or generalization algorithm.

Actual recursive-interface supply is not proved to use this construction.
Equations `O_f=O_g`, `O_g=O_f` admit empty and arbitrary common decorations:
circulating a label does not ground it. Selecting the least set would add an
unselected formation rule. Neither least recursive semantics nor
`O_f=O_g={}` follows from finiteness or absence of requests.

Charter §21 supplies a further **real frontier event**: ordinary `x` and `y`
receive fresh inferred value endpoints `A_x,A_y`. That settles their role,
allocation freshness and entry behavior. It does not say whether creating
such an endpoint is a §22 existential introduction, supply its introduction
level/history, or give its correspondence to a retained recursive interface
variable. Calling it an inferred endpoint does not force non-Ex status; calling
it fresh does not force Ex status. Recursion/interface formation may also need
endpoints whose source rules remain unspecified. They cannot be discarded
merely because the parameter is unused.

## A single residual judgment and its minimal demanded output

Name the residual source obligation `Supply22(G,d,u)`:

```text
input:  the complete resolved closed source envelope G, member d in {f,g},
        external occurrence u and its alias boundary, fixed parameter roles
output: the supplied source interface I_(d,u), grounded introduction ledger,
        and scope-correlated realization at the occurrence, alias root
        and recursive use variables consulted by comparisons; binder mode,
        original declared bounds and the source role of each routed check
```

Its **undecided semantic clause** is the introduction policy of ordinary
binding/inferred/recursive interface endpoints and ordinary use-time freshening:
which of these events, if any, introduce a §22 existential, and which existing
introduced variables/dependencies they transport. All Name/Result copying
after its output is already decided. This is one named source formation/use
judgment, not a proposal to install B/G/U as three new policies. It may be
implemented or proved compositionally, but no selected source currently gives
its origin-policy input/output relation.

For `L_h <: rho_h`, that output must distinguish a constraint on an ordinary
inference witness, restoration of an originally declared bound of a rigid
opened binder, and a new attempted restriction of that binder. Charter §20
permits uniform checking under declared bounds, while forbidding use of caller-
private specialization as an arm premise. A production “restoration” label
alone establishes none of those source roles. No new replay exemption is
selected here. An origin bit alone would therefore not decide full permission.

The minimal guard certificate restricts that output to variables actually
consulted by the guard, retaining introduction identities and levels.
For one alias the known rows and comparisons are

```text
c_h <: R_h
L_h <: rho_h; rho_h <: Top; L_h <: c_h; L_h <: R_h
L_h = PureFun(Top,PureFun(Top,rho_h)).
```

`c_h` is the distinct occurrence row, `R_h` the alias root. No collected
`c_h <: r_f` or endpoint equality is supplied. The prior reviewed source-guard
trace gives the finite comparison/replay inventory; it does not supply this
certificate. Total classification of every unused source coordinate is more
than this local guard question needs. Full source adequacy may need more.

There is a sharp local seam without any composite level convention, conditional
on this pair realizing a generated source comparison governed by §22:
let `Ex(v,l)` certify that `v` is a §22
existential introduced at level `l`. Both `c_h,R_h` have current level 1.
For their variable/variable pair the §22 guard veto is exactly

```text
(exists l >= 1. Ex(c_h,l)) or (exists l >= 1. Ex(R_h,l)).
```

Each disjunct suffices because the peer's level is at most the introduction
level; otherwise this pair supplies no §22 veto. This decides only that guard.
Current level 1 does not prove introduction level 1. Deciding the pair needs
its certificate or an authority-derived invariant making it redundant;
Name copying and Q/R storage supply neither.
For the structural/root comparisons, the supplier certificate must additionally
compose with the still-open §23 variable/extrusion coverage theorem. Thus no
complete permission or acceptance theorem follows just from this local seam.

## Falsifiers, checks, omissions and frozen handoff

The conservation claim fails if a selected Name/Result rule itself gains an
opening/intro operation, or a realization erases a previously carried binder
or splits its joint dependencies. The finite-copy claim fails if an alleged
copy edge introduces an event, or a circular label is counted as its own
grounding. The local guard formula requires the stated variable levels and
the exact §22 antecedent; it says nothing about unclassified dependencies in
composite-type comparisons. A future authoritative `Supply22` rule would
supersede the residual, rather than retroactively make this note its proof.

Checks: pinned `git show` reads, `git ls-tree` absence checks, narrow section
reads, final whitespace/line-count inspection and direct-input equality check.
Truncated initial captures were reread narrowly. No build, test, executable
oracle, enumeration, formatter, question bundle, child agent or Git mutation.
Source/solver adequacy, complete seeds, full guards, principality, lifecycle and
acceptance remain unverified. One lightweight process at a time; CPU/RAM
unmeasured; 20-minute initial budget.

Commit packet: exact path is this note; baseline is the SHA above; direct inputs
were read from that revision, not concurrent edits; review status is unreviewed
Draft research. Proposed commit: `research: reduce recursive Name origins to interface supply`.
Deferred shared-record delta: record supplied-interface conservation, finite
grounded-copy closure and its non-least-semantics limit; replace repeated global
N/B/G/U requests with the exact `Supply22` origin-policy and demanded guard
certificate. Keep source adequacy and variable/extrusion coverage open. No
task, theory map, design index or other writer's file was changed.

Writes stop at submission; this path is frozen for independent review.
