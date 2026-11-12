# Cycle149 finite associated materialization

Generalize the prior singleton associated-output theorem to arbitrary finite
root demand output lists and arbitrary finite associated equation lists.
Every requested output target is the already constrained nominal head source;
every actually looked-up associated right hand side translates to the inspected nominal query.
The declaration remains checked and terminal; finite binder sharing remains
arbitrary. Derive generated materialization, rather than assuming it.

Proof plan: schema model validity restricts along test/variable membership;
finite folds of copies of a schema inherit validity including cross-copy
coherence. Extract requests from actual rootRequests and apply the checked
terminal elimination of emitted where clauses. Combine this with the existing
source/coherence/merge characterization of BranchModels. This is a helper for
the same-model V5 boundary, not a proof that all selected foci have this shape.
No singleton or nonempty output restriction. Unknown requested output names
remain a separate RootDefined obligation, and are not certified by this lemma.

## Distinct but equivalent output sources

`GeneralNominalAssociatedSourceTransport` removes syntactic equality of output
source IDs. For every requested output its assigned value must be equivalent
to the inspected nominal head. Nominal projections transport along this actual
carrier equivalence; materialization test obligations transport transitively.
The finite-fold theorem derives coherence even across uses originating in
different requested outputs, not just separately for each schema.

The exact branch residual retains the same source/coherence/merge obligations,
with output equivalences supplied separately. Actual ordinary equality paths
can discharge these equivalences using the cycle149 journal-path theorem.
Arbitrary unrelated outputs, nonterminal where clauses, and arbitrary translated
RHS expressions are not covered. RootDefined remains separate.

The translated nominal query discharges the generated schema's `unknown` flag.
`request_ready_iff` proves that the exact remaining RequestReady condition is
RootDefined for arbitrary head bounds and arbitrary output source IDs. This
keeps name definedness explicit instead of silently treating absence as success.

## Nonterminal where-child fragment

Next extension keeps actual nonempty where clauses. Each child input pattern
normalizes to a bare variable, so its interval is supplied by capture and it
emits no compound-input materialization requests. Child named output RHSs
translate to the inspected nominal query; their actual allocated output targets
are equivalent to the inspected head. Output-only binders are explicitly absent,
not inferred from terminality. Extract provenance from canonicalEmit using its
permutation theorem and from actual emit structures. Derive all generated
materialization including cross-root/child and child/child coherence. This does
not construct child dictionaries or discharge semantic where obligations.
