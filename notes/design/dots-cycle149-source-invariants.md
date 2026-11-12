# Actual support-source invariants

Derive seed preservation and ordinary-constraint inclusion directly from every
actual guarded support step, including refresh and certified reobservation.
Refinement already specifies seed preservation and ordinary inclusion; revision
changes only nominal descriptors. Installations require the stored context to
equal the current one and append private constraints.

Combine the actual packet installation origin with these invariants to prove
that every SourceFormed historical packet has the current allocation seed.
Finite syntactic RecordedPath certificates therefore persist through all actual
support updates, not merely a semantic consequence in one model. These are
operational facts, not extra BranchModels hypotheses.
