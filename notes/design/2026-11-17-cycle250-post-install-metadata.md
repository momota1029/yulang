# Cycle250: distinguish old-snapshot and post-install metadata

Status: Draft implementation plan. No new language rule.

JournalAppend250 handles obligations interpreted BEFORE refresh. It is not the
right interface for a newly installed packet whose references mean the NEW
aggregate values. For that case attach the new Delta AFTER rebase, without
rewriting it through old definitions. Its old-side obligation is Delta evaluated
under the freshly constructed solution, represented finitely by substitution
with `mapping fresh`. This can constrain the old public models, as installation
should; do not drop this obligation or split its witness from the old journal.

With persistent target domains, both old and fresh solvers erase all incoming
private values. `solve fresh (solve old a) = solve fresh a` follows from existing
ordered absorption. The new delta respects full nominal equivalence by the
250 all-field congruence proof, so a satisfying fresh state recovers the SAME
new delta after transporting back through old. This proves the reverse projected
model direction without assuming source completion or model existence.
