# cycle244 technical recovery: full journal dependency cache

This is an execution-resource issue, not a language-semantics decision.

At about16:35 UTC the execution workspace was replaced, deleting the local full
Lean object cache. Public243 remains intact. Six244 unpublished source drafts
were reconstructed and quarantined under notes/recovery/cycle244. They must not
be imported as verified results without rebuilding and auditing their exact
reconstructed bytes. Their SHA256 manifest is in verification/cycle244.

Recommended deferred route: keep the14 independently reverified244 modules and
all prior public proofs, retain the six drafts, and have the supervisor's normal
full verification environment rebuild and audit those drafts. Do not repeat a
large full build in this resource-limited Dot process: its required journal
closure is1425 modules. The small actual Presence core closure36 was restored
successfully with2workers under5min and is available for bounded work.

If a reusable verified build cache is made available, it must match Lean4.35.0
and the current source/import hashes. Recheck changed modules and full new-module
axioms after materialization. A cache alone is not evidence that reconstructed
sources were checked. No need to change language rules or relax any proof gate.
