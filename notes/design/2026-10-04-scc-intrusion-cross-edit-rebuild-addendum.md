# SCC-intrusion cross-edit rebuild boundary

Status: Authoritative
Scope: cross-edit lifecycle and invalidation boundary for the SCC-intrusion successor
Approved-by: user, explicit direction on 2026-10-04
Approved-at: 2026-10-04
Drafted-by: primary
Reviewed-by: architect, narrow charter/F3/F4/F5 compatibility review on 2026-10-04
Supersedes: none; adds to the SCC-intrusion redesign charter §§3–4
Implementation authority: none

## Decision

The successor assumes differential inference. It does not require intrusion,
variable-level, bound-propagation, or SCC internal state to be reverse-updatable
across source edits. When an edit changes an inference component, that component
may be rebuilt and solved from its current source inputs.

Prefer a representation with a generalized canonical interface at the
component boundary. When a rebuilt component's complete generalized canonical
interface is unchanged, downstream **inference** invalidation may stop at that
boundary and reuse dependent inference results whose other inputs are also
unchanged.

This is a direction for the successor representation and cross-edit lifecycle,
not a requirement to implement editor integration now. It does not prohibit
safe reuse or forward incremental solving within one solve attempt. The
single-attempt obligations in the existing SCC/F4 designs—including live
internal uses, component visibility ordering, bound propagation, and atomic
publication—remain in force within their scopes.

## Interface comparison boundary

The canonical interface must contain enough published generalized information
to justify downstream inference reuse. Equality of printed type text, arena
identities, or value-port projections alone is not established as sufficient.
The successor must prove that its chosen canonicalization and equality test
preserve every downstream-observable generalized constraint, coupled effect,
scope relationship, and required evidence.

This addendum does not choose the interface fields, canonical form, equality
algorithm, component granularity, dependency representation, or treatment of
SCC split/merge and changed enclosing environments. It also makes no claim
that an unchanged inference interface permits reuse of code-generation or
other non-inference artifacts; their invalidation dependencies remain a
separate design obligation.

Reconstruction must publish atomically. If rebuilding fails, no partial or
mixed-version inference result may become visible, following the existing
failure/publication obligations of the redesign charter.

## Compatibility and gate

The charter's semantic target and theorem obligations remain unchanged.
Successor proofs must still establish soundness and principality for the
claimed source envelope. This does not restore F5's closed-scheme architecture
as a successor requirement. Existing F5/F3/F4 contracts continue only within
their declared scopes; no cross-edit reversal requirement is inferred from
them.

Before implementation, the representation gate must define the complete
published interface, canonical comparison, inference dependency boundary,
rebuild atomicity, and the cases that invalidate consumers. Review witnesses
must include a body edit with unchanged interface, a changed interface, SCC
split/merge, changed enclosing non-generic state, and reconstruction failure.
Resource review must distinguish rebuilt inference components from regenerated
non-inference artifacts. These are open proof/design obligations, not decisions
made by this addendum.
