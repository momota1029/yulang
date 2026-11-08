# Cycle 9: all-candidate structural allocation

The previous cycle closes all structurally matching candidates' children, including alternatives hidden by current ambiguity. This cycle computes one finite syntactic-type table over that closure and *all* matching payloads, rather than the selected head alone. For every visible declaration subset and every request in the original potential closure, actual production payloads and state-gated child endpoints must decode to their original syntax. Connect this allocation to the existing prepare exactness theorem.

No new language design: endpoints remain fixed structural Ty values. Distinct unknown source identities, endpoint narrowing, general state saturation, dictionary/classification, and general B4 remain out of scope. No claim that a syntactic-type allocator solves source-variable provenance.

Validation: focused module build and focused axiom prints; no full build or verify-lean in this worker. Publish only work/dots-main.
