# Cycle251: expression-target requests and actual child structure

Status: Draft compiler extension.

A generated request's target must be an expression as well as its RHS variables:
a child variable center can be an old singleton endpoint, while its capture bounds
are a new aggregate. Introduce RoleRequest(pattern, target term, mode), compile
with the existing total pattern translator, preserve unknown on translation failure,
and state an independent Holds judgment over successful translations. Prove
unknown=false iff every request translates. Holds alone can be vacuous on unknown;
never call it readiness or source acceptance.

Actual child demand structure supplies variable-pattern bounds from env.capture,
variable centers from env.binder, compound bounds/centers from the actual legacy
allocation names through env.target. Output-only variable RHS targets use the
binder role; other output targets use the actual clause equation allocation. This
keeps clause identity and role, and does not prove allocator freshness.

Next construct actual child and emitted/root request lists without routing all
targets through a single Nat mapping. Independent child Fits and successful
translation judgments are the reference semantics. Scope claims must still name
supplied fallback/binder/target expressions and any source generation obligations.
