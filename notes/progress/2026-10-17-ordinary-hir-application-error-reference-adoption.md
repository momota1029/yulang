# Adoption receipt: ordinary HIR aggregate error-reference accounting

The user explicitly approved the reviewed resource correction: “計算量は修正して構いません。” This adopts the exact output-sensitive replacement proposed in
`notes/design/2026-10-17-ordinary-hir-application-error-reference-accounting-amendment.md`
(SHA-256 `e8b53a773675ba54f0cb5dcc4d62a993e8dd16954e0c92c58fdfc80c620d411e`)
and its exact handoff (SHA-256
`23f637cdb64ef6ab237fef6dacb4abeec06bf19efa75d8f8f2d0202c09a67d80`).

This supersedes only adopted rev4 §2’s claim that every retained aggregate
error-ID reference and its construction are linear in expression nodes. The
adopted account separates `V` unique retained nodes, `E` distinct operand-error
events and `R` physical `HirErrorId` references across all flat Apply lists:
node/control work is `O(V)`, error/diagnostic events are `O(E)` with `E <= V`,
and required flat-list assembly is `O(R)`. The total is `O(V+E+R)` and may
be `O(V^2)` in `V`. The frozen lower-bound family has `V=2m+1`, `E=m+1`,
and `R=m(m+3)/2`.

The correction preserves rev4’s admitted grammar, complete ordered descendant
error lists, public `Box<[HirErrorId]>` representation, diagnostics and dense
IDs, source keys and identities, carrier behavior, source acceptance and
failure-atomic publication. No original theorem claim or quantifier changes.
This resource correction proves no Call typing, source/native adequacy,
soundness, principality, termination or parent theorem conclusion.

Independent sequential reviews were completed on the exact frozen artifacts:
compiler referee CLEAN for the lower bound and `O(V+E+R)` construction;
spec auditor and architect CLEAN technically, each identifying the user
approval gate now closed by this receipt. The architect’s implementation
conditions are binding: materialize each Apply error list once; Group forwards
without cloning lists; use checked child-length, cumulative-R, byte-size and
ordinal arithmetic; reserve complete destinations fallibly before publication;
abort without partial module/stage or truncated/duplicated diagnostics; and
report `R` plus actual reference allocation/storage for clean and unresolved
spines and Group-wrapped cases. Exact reviewed artifacts remain frozen.

Adopted by the user on 2026-10-17 after the three sequential review receipts.
Original theorem gates closed: 0.
