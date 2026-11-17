# Cycle238 equation normalization and preserved meaning

Status: Draft, proof plan. Scope: equation subsystem and semantic equivalence,
not an unconditional EvidenceNode or installation existence result.

Cycle237 constructed a well-founded aggregate-equation solution but did not
connect it to an existing model. For any finite descending coherent equation
ledger and any assignment already satisfying those equations, prove that the
constructed solution is pointwise semantically equivalent (rows unchanged).
The core induction is on numeric target IDs, not an assumed termination of
operational steps. Lift RHS evaluation using full nominal carrier congruence.
Then specialize to every historical aggregate ledger in a real mixed trace:
existing full journal models supply the equations, so historical normalization
cannot arbitrarily change any type's meaning. This does not show that adding
prospective equations preserves an old model, or solve compound output targets.

Proposed quantified theorem: for all entries, base, coherent, descending, and
forall entry in entries, All base (equations entry.target entry.rhs), for all n,
Equivalent (solution entries base n).type (base n).type and row equality.
No desired conclusion is included as a hypothesis; equation satisfaction is
already a proved projection of historical Models. Any further journal transport
requires a separate semantic congruence theorem, not literal assignment equality.

Parallel counterexample-first work checks actual source prefixes for the two
cycle237 diagnostic fixtures. No semantic change or refutation is inferred from
conditional local obstructions. Exact target refutations stop that target.
