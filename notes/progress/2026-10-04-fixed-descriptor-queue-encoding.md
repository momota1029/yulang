# Queue encoding probes: descriptor, marker, and pair activation

Date: 2026-10-04
Branch: research/simple-sub-intrusion
Status: scoped negative results about three encoding patterns; no language or solver decision
Reviewed-by: Astra bounded fixed-descriptor, flexible-marker, and pair-activation probes; primary Sol adjudication
Implementation authority: none

## Question

Can the coexistence of descriptor-prefix equations and comparison-child
extension directly encode queue-machine computation in the admitted
mandatory-Record / ordinary structural comparison fragment?

This probe tests the specific finite-control encoding in which a control state
is a fixed recursive descriptor and a configuration (s,w) is represented by
the descriptor address (Q_s,w). It does not decide whether a different
encoding can express such a reduction.

## Attempted encoding and obstruction

For transition function δ, the direct descriptor package would use:

    Q_s = Record { a : Q_δ(s,a) | a is an enabled leading symbol }

The intended pop step is the exact regular-tree equation:

    (Q_s, a·w) = (Q_δ(s,a), w)

This equation is bidirectional: it identifies the child subtree with the
finite control descriptor. If every transition child is again one of the
finite set of control descriptors, induction over the word reduces every
defined (Q_s,w) to one of those finitely many descriptors:

    (Q_s,w) = (Q_δ*(s,w), ε)

Thus the represented subtree depends only on the finite control reached after
consuming w; this is a finite-state summary, not unbounded queue storage.
Distinct words must eventually collapse to the same represented descriptor.
For example:

    q = {a:q}

identifies (q,ε), (q,a), (q,aa), and every further a-extension. A local head
or field-presence test at these addresses therefore sees the same descriptor.
In q <: q, structural descent through a returns the same ordered pair and
original bound; it does not create a queue transition.

The proposed append step is also absent. Structural comparison descent extends
both endpoints by a common child coordinate, with argument reversal at
Function arguments. It does not directly provide a unary transition that
removes a leading symbol from one represented queue and appends an output word
to its other end. Record width launches required comparisons only for fields
present in the upper endpoint; lower-only fields do not launch them.

There is also a finite-closure check on the fixed-descriptor subcase. The
reviewed normalizer memoizes each state (original bound, finite guard context,
lower descriptor node, upper descriptor node). With finitely many such nodes
and contexts, comparison descent has only finitely many states. A repeated
state is a recursive structural obligation, not a fresh queue configuration.
This rules out using derivation depth alone as unbounded storage when all
machine controls and comparison endpoints remain fixed descriptors.

These two facts defeat this fixed-control-node encoding. In particular, it
cannot faithfully distinguish the empty queue from the one-symbol queue in a
machine whose behavior differs on those configurations, nor can it use
comparison descent alone as the missing append transition.

## Scope

The result is about the proposed representation, not every possible reduction
into regular structural constraints. It does not rule out encodings using
flexible descendants, multiple interacting comparison tracks, or other
cross-component equalities. It proves no undecidability theorem and supplies
no general decidability result for Yulang's open structural fragment.

This is consistent with the reviewed boundary of the root-only synchronous
automaton: descriptor equations such as q = Function(x,e) require shifted
cross-track subtree equality and lie outside that automaton. See
[the root-only regular-witness theorem](2026-10-04-root-only-regular-witness.md)
and [open residual factorization](../design/2026-10-03-open-residual-factorization.md).

## Flexible-descendant marker-transfer probe

A second attempt allowed an open descendant and used forced field presence as
the unary configuration marker. It tried to combine prefix transport through
descriptor equations with child descent that appends one output symbol. The
following finite package refutes that specific marker-transfer pattern.

Use distinct labels a,c,b and these exact descriptors plus a flexible class y:

    e = {}
    r = {b:e}
    h = {c:r}
    x = {a:h}
    q = {a:y}

    β: q <: x
    γ: h <: y

Define Reach_s(u) as field b being present at address u in fixed descriptor x;
define Reach_t(u) as field b being forced at address u in every solution for
flexible descriptor y. The proposed step is

    Reach_s(a·w) => Reach_t(w·b)

Take nonempty tail w=c. The exact descriptor x has b at address ac. Bound β
decomposes as:

    q <: x       gives y <: h
    y <: h       gives y.c <: r
    y.c <: r     gives y.cb <: e

So β forces c and then b along y's path; its final comparison y.cb <: e does
not constrain lower-only fields at y.cb. Bound γ supplies the other side:

    h <: y       gives r <: y.c
    r <: y.c     gives e <: y.cb

For structural Record subtyping L <: U, every label of U must occur in L.
Because the lower endpoint e={} has no labels, e <: y.cb forces y.cb to have
no fields. Thus Reach_t(cb) is forbidden, although Reach_s(ac) is fixed true.
The package is satisfiable with y=h, so the proposed forced-marker implication
does not follow from these constraints. If one adds the target marker as a
constraint, γ exposes the designated failure e <: {b:e}.

This checks both inequalities and preserves their original bound identities
and positive orientation. It only refutes this encoding pattern: a unary
forced-field marker transferred through prefixes is not automatically renewed
at the payload child created by comparison descent. The active child
obligation is still β at y.cb against e; retaining that paired obligation as
control would be a different gadget and has not been proved to implement an
append transition uniformly. The obstruction uses a flexible descendant, but
does not address activation-based encodings or every use of shifted
cross-component equations.

## Cyclic upper and active-pair probe

A third candidate uses an active ordered endpoint pair, rather than field
presence alone, as its configuration marker. Let V be the recursive Record
with both labels and U the wrapper requiring only a:

    V   = {a:V, b:V}
    U   = {a:V}
    Q_s = {a:X}          // X is descriptor-free

    β: Q_s <: U

The package has the regular solution X=V. At the root, β descends only through
upper field a. The resulting active comparisons are:

    trace ε:       Q_s <: U
    trace a:       X <: V
    trace a·w:     X.w <: V
    trace a·w·b:   X.wb <: V

for every w in {a,b}*. Because upper V requires both fields, once X <: V is
active its descendants cover every word over {a,b}. Thus β's active trace set
is exactly {ε} ∪ a{a,b}*; the original bound id and positive orientation stay
attached to every descendant.

The descriptor prefix equation rewrites the lower endpoint as Q_s(a·v)=X(v).
After stripping that a from the endpoint representation, the projected pair
set is {(X.v,V) | v in {a,b}*}. This is wider than the transition outputs
{w·b | w in {a,b}*}: it already includes target addresses ε and a, which do
not end in b. The child comparison for an appended b exists, but the cyclic
upper forces the same active pair at all intervening and non-output nodes.
The append implication is therefore not symbol-conditioned by endpoint-pair
identity alone.

Filtering the original traces to a{a,b}*b before projecting pairs would
recover the desired output language as a mathematical definition. This
package supplies no structural rule that makes later obligations or a
designated failure depend on that filtered subset instead of all active β
descendants. An external trace filter would be a new operational control and
would need its own derivation from the admitted constraint rules. This scoped
obstruction does not rule out other descriptor graphs, variance patterns, or
joint bounds that implement such control.

## Next exact theorem probe

A stronger reduction attempt must now exhibit a finite symbol-conditioned
one-step gadget not defeated by these three tested patterns, for designated
encodings of controls and words, of the shape

    Reach_s(a·w) => Reach_t(w·v)

uniformly over the queue tail w, inside the admitted constraint fragment.
The proof must show that the consequence has a finite derivation from
descriptor equations and descendants of original inequalities; other leading
symbols and the empty queue do not trigger it; descriptor transport does not
identify unintended configurations; and optional assignment structure cannot
evade the intended failure condition. Only after such a gadget is derived
would a global simulation or undecidability argument be in scope.

If no gadget emerges, the current evidence supports only the narrow statement
above. Do not treat the queue analogy itself as an impossibility theorem.
