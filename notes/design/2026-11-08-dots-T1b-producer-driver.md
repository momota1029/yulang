# T1b: concrete two-endpoint producer and retained-state driver

Status: Draft implementation plan, 2026-11-08. Base: 4a9a6a16f.

## Target and admission boundary

The target is the T1b plan entry, not a new language rule. Start with the
structural two-endpoint observation fragment: declarations use the existing
finite unary heads/templates and the actual declaration checker. A hit has
two independently inspected original endpoint payloads. This excludes head
narrowing that makes an initially nonmatching endpoint match; it is not a
complete source candidate rule for all open intervals.

The source producer exposes every original ordered requirement of the selected
head. Its `Local` judgment is inductive and does not call the producer. Prove
for every checked registry and request that every actual `Child Local` is a
`CommonRoleOpenDescent.Step`; derive accessibility, not an input certificate.

## State driver

A stateful driver must call the producer again with each updated state, retain
all ordinary atoms, and recompute the parent. An accumulator given a list of
updates in advance does not meet this requirement. The restricted operational
boundary uses a finite endpoint-slot allocation and generates each capture
update from the actual selected head and two returned payloads. Slots may be
shared. Their connection to the source graph is a separate proof obligation:
no arbitrary slot allocator is to be advertised as a source provenance proof.

The intended independent driver judgment records local production, a finite
ordered list of child derivations with the returned state threaded through,
and final recollection. A theorem for all state/input/output values should
relate the executable driver to this judgment without an assumed frontier
exactness or accessibility. Such a theorem is still not full source
`resolve_exact` unless the allocation and narrowing bridges are closed.

A conjunction is insensitive to permutation of siblings' generated atoms.
We may prove that operational fact without choosing a language-visible sibling
scheduling policy. Any unresolved source order policy is deferred to the owner.

## Honest endpoint

We will report separately: actual producer accessibility; driver exactness;
source/slot provenance; interval narrowing; X13–X16 outer entry. No conjunction
of local theorems will be relabelled as the missing source theorem.
