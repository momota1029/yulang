# Multi-anchor selector witness for structural regularity

Date: 2026-10-04
Status: conditional theorem result; theorem and finite-checker proof
independently reviewed; no implementation or language authority
Scope: regular-witness existence for a finite pure structural package
Depends on: `2026-10-04-source-generated-callback-structural-theorems.md`, §6–7,
and `2026-10-04-direct-main-gate-attacks.md`
Authority: no new language or solver authority
Reviewed-by: independent compiler_referee and spec_auditor delta review,
2026-10-04; initial minor findings corrected and finite-checker extension
reviewed.

## Result

Theorem S's one-open-anchor clause is sufficient, but not necessary for the
anchor-collapse construction. Extend it, for the components covered below,
with a finite **anchor-selector certificate**. This admits multiple distinct
open anchors when one of the already present anchors directly satisfies every
incident directed bound after the selected components are collapsed to their
chosen anchors.

The condition is checked on the normalized source package and finite
descriptor graph. It does not assume arbitrary satisfiability, a regular
solution, or principal projection. For a fixed certificate, the construction
has a restricted witness form: selected components map to one of their
incident descriptor roots, no-anchor components map to `{}`, and the
certificate supplies the chosen root-only witness for every all-closed
component. The direct checks are exact for that particular constructed
assignment. This does not make the condition necessary for unrestricted
regular satisfiability or even for the broader anchor-valued form when
unanchored and root-only assignments are allowed to vary.

## Package and certificate

Use the normalization and notation of Theorem S §§5–6. Keep every original
oriented bound. Build the same auxiliary graph whose vertices are free classes
and whose edges are free/free bounds, ignoring orientation only for connected
components. `Anch(C)` is the same finite set of incident descriptor roots.
Retain Theorem S's permission condition that every input rigid is permitted at
every free class.

For each component `C` with at least one open anchor, choose
`s(C) ∈ Anch(C)`. For a component with no anchors choose the empty Record
root `{}`. Components whose anchors are all closed may instead use the
existing root-only construction from Theorem S; the selector condition can
also be used for them when an anchor passes the checks below.

For selector components, redirect every free-class root in `C` to `s(C)`,
preserving all descriptor heads, exact Record masks, and child edges. For
no-anchor components redirect to `{}`. For all-closed-anchor components
handled by the root-only case, attach the finite joint witness constructed by
Theorem S. Keep descriptor-child references to these resulting roots. This
produces a finite guarded graph `W_s`: descriptor-child edges are constructor
edges, so every cycle remaining after redirection is constructor guarded. It
therefore denotes a simultaneous regular assignment.

For every retained free/descriptor bound incident to a selected component,
interpret both endpoints in `W_s` and supply a finite coinductive structural
simulation certificate for that original oriented comparison. A certificate
is a finite set of node pairs closed under the already specified structural
rules: matching fixed heads, mandatory Record width and field obligations,
and declared variance descent. Check the roots and closure locally. No
successful comparison is composed transitively. Free/free bounds lie within
one component and become reflexive under redirection. Bounds with two fixed
descriptor endpoints have already been discharged by normalization; if the
normalizer retains any, include their existing direct certificates too.

Call a source package **selector-certified** when this finite construction
and all direct certificates check. For components handled by the root-only
case, include the actual joint finite witness in the certificate and check it
against its root-only obligations. If an open selected descriptor reaches
one of those roots, its direct comparison certificate is checked after that
same root-only witness is attached; a different root-only witness cannot be
silently substituted.

## Theorem

If the finite normalized package is selector-certified and satisfies the
stated rigid-permission condition, then it has a simultaneous regular
solution preserving every original descriptor equation and directed bound.

### Proof

The redirected graph is finite and constructor guarded, hence gives a regular
assignment. Original descriptor equations hold because redirection changes
only free-class roots; descriptor heads, masks, and child edges are retained.
In selector and no-anchor components, each free/free bound has endpoints in
the same component and therefore unfolds to identical roots. Each
free/descriptor bound incident to a selector component is one of the
certified direct simulations. Free/free and free/descriptor bounds in
root-only components are satisfied by Theorem S's existing joint
construction. Fixed descriptor bounds hold by normalization or their
retained certificates. These cases exhaust the original bounds. Every rigid
reachable from a redirected free root is an input rigid, so the
all-free-classes permission condition preserves scope. Thus the assignment
is a regular solution. QED.

The proof uses the same structural comparison relation and descriptor graph;
it adds no carrier, transitive closure, or change to the principal residual.
This is an existence witness only and does not collapse variables in the
residual relation.

## Finite source checker

The selector premise has a terminating positive checker on this package
class:

1. Run the existing finite normalization and root-only construction for the
   all-closed-anchor components.
2. Compute the finite free/free components and their finite anchor sets.
3. Enumerate one of the finitely many incident-anchor choices for every
   component with an open anchor; use `{}` for no-anchor components.
4. Build the finite redirected graph and check each retained oriented bound
   by the finite greatest-fixed-point simulation on pairs of graph nodes.
   The check follows only the existing head, width, and variance rules for
   that one original bound.

Each stage terminates. There are finitely many components and selectors, each
candidate graph is finite and guarded, and its pair universe is finite. For a
fixed candidate, descending elimination from all node pairs computes the
greatest relation closed under the local structural rules. A surviving root
pair is exactly a finite coinductive certificate for that direct bound. The
procedure returns a regular witness when a selector passes; failure only
means this selector construction found none, not that the package is
unsatisfiable. It therefore gives an effective source-checkable sufficient
fragment, not a decision procedure for unrestricted regular satisfiability.

The verifier can also accept an explicit finite `W_s` and per-bound
simulation certificates instead of performing selector search. That proof
object uses the existing descriptor and comparison evidence; it is not a new
semantic carrier or solver relation.

## Strict extension over one open anchor

Let `F` be Function, `E={}`, `R={f:Int}`, and let `Y` be a free class. Use
finite descriptor equations and bounds

```text
A = F(Y,E)
B = F(Y,R)
B <: X
X <: A
```

Before witness construction, both distinct anchors `A` and `B` are open
because each reaches `Y`; the free component of `X` therefore violates
Theorem S's one-open-anchor predicate. The selector chooses `A` for `X` and
`{}` for the unanchored `Y`. Then `B <: A` is certified directly: the
Function arguments are reflexive and the result obligation `R <: E` follows
from mandatory Record width. `A <: A` is reflexive. The resulting assignment
is regular and satisfies both original bounds. This demonstrates strict
extension of the one-open-anchor sufficient class, not a counterexample to
Theorem S or a proof that all multiple-anchor packages are solvable.

The selector condition is also strictly stronger than unrestricted regular
satisfiability. Let `E={}`, `A=F(Y,{f:Int})`, `B=F(Y,{g:Int})`, and impose
`X <: A` and `X <: B`. Before assignment both anchors are open through `Y`.
Neither existing anchor can serve as `X`, since `{f:Int} </: {g:Int}` and
`{g:Int} </: {f:Int}`. Yet `Y={}` and `X=F({}, {f:Int,g:Int})` is a regular
solution: both Function argument checks are reflexive and the result Record
is wider than either upper result. This package fails the anchor-selector
test while remaining structurally satisfiable, so the premise is not a
restatement of regular satisfiability.

## Separate source-generation check

The source-generated structural clauses in the reviewed theorem package
already allocate finite endpoints, finite descriptor graphs, and original
bound identities before solving. A source-level checker can build the free
incidence components and anchors from that output, verify a proposed finite
selector, construct `W_s` together with its chosen root-only witnesses, and
check each finite simulation certificate. A source derivation accompanied
by a passing selector certificate therefore satisfies this theorem's premise
by a finite check that does not query arbitrary-tree satisfiability or ask
whether any regular solution exists.

For the current production HIR's named **structural value shadow**, the source
generation theorem is stronger: its generated structural package has no
directed inequalities, so every free component is unanchored. Assign each
such component `{}`; the finite descriptor graph and equations are retained,
and there are no directed comparison certificates to check. Thus this source
generator satisfies the selector premise for that shadow fragment. The
separate audit in
[`production HIR empty-Record shadow`](2026-10-04-production-hir-empty-record-shadow.md)
proves the generator inventory. This still does not apply the theorem to
F5's actual coupled four-port Function facts.

This establishes a conditional source-generation theorem for the existing
structural generator: every emitted package with a passing selector
certificate has a regular witness. It does not show that every Yulang source
package has such a certificate, nor that failure means ill-typed. The current
production HIR **structural value shadow** has the stronger `Λ=∅`, no-bound
property already recorded in
[`production HIR empty-Record shadow`](2026-10-04-production-hir-empty-record-shadow.md).
That shadow still is not equivalent to F5's coupled four-port Function
constraints, so this result does not bridge the actual effect-bearing
production endpoint.

The selector check is a finite, non-tautological sufficient condition tied to
an explicit witness shape. It strictly extends Theorem S's one-open-anchor
condition on the displayed compatible-anchor family, while the second
example shows that it remains incomplete for satisfiable packages. Its
comparison certificates are part of the existing directed bounds. No
necessity, weakest-assumption claim, decidability for unrestricted packages,
or complete Yulang source theorem is asserted.

No compiler code, tests, or design authority changed.
