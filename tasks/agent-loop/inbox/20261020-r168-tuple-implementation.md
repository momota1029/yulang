# R168 ordered-tuple implementation design handoff

- Sprint: `ordered-tuple-construction-20261020-r168`; proposed revision 1; no lease or launch.
- Contract SHA-256: `cb33b37ce48b7b2131e56cf3c3e510c5e24ac9177f743145966abf94479b8ce8`.
- Assignment: `R168-TUPLE-IMPLEMENTATION-DESIGN`, revision 1; Luna primary.
- Baseline/source pins: contract and Luna refresh before grant.
- Objective: write an implementation design against actual syntax/HIR, solver, closed type, and runtime consumers; reconcile all exact paths with the proof matrix. Do not edit code.
- Exact outputs: `notes/design/2026-10-20-r168-tuple-extension.md` and this handoff only.
- Code leases: NONE in revision 1. A sequential contract revision must list every exact path/hash and pass prospective independent review before any code edit.
- Constraints: arbitrary finite ordered tuples per R149; no pair encoding; no destructuring; preserve Unit/Group distinctions, element type/effect order, source provenance, and left-to-right single evaluation.
- Budget: 300 seconds within 6000; no carryover. Implementation's 2700-second lane is conditional on the reviewed matrix and revised exact code leases.
- Review: `/root/r157_contract_review`, independent and fresh for the revised code boundary and final diff.

---

## Luna candidate design result — revision 2

Candidate note: `notes/design/2026-10-20-r168-tuple-extension.md`. It records the syntax/HIR admission seam, distinguishes Unit/Group/tuple, and describes source identity, positional type, and left-to-right runtime requirements. **This is not a proof of coverage and grants no code path.** Exact constructors/consumer matrix from the proof lane is still pending; no implementation revision can be prepared until that result is frozen and independently reviewed.

Candidate note SHA-256: `87eb621f6e956c68d8fb4cc950af0e66671817dfb5914b2cc5b514b44479a269`.

The proof lane's live partial matrix found (1) candidate graph export has a fixed four-child accessor and `render.rs` assumes every structural node is Function, separately from the F5 closed-type/finalization consumers; (2) tuple runtime frames need to preserve each element's received view across continuation cloning, beyond a bare `ValueHandle`; (3) the term interner clones nodes into page storage, dedup keys, and route journal, so dynamic child storage must cover all ownership/rollback paths; and (4) a new Tuple instruction would not acquire a module initializer class, which remains under R167 and is explicitly out of scope. Exact owners/hashes and a complete matrix remain with the proof lane.

Observed work so far: read-only local owner inspection and this candidate cross-layer design; no code edits, tests, builds, compiler/runtime/sample execution, or Y2/Y3 activity. The frozen proof/matrix at `notes/theory/2026-10-20-r168-ordered-tuple-construction.md` (SHA-256 `c88ce484dd1a6456f4e29cfcd932438db9ef6579f30584bc826aab9e4975a886`) was independently CLEAN reviewed by `/root/r157_contract_review`. It verifies the candidate graph/closed scheme split, exact source arity seams, runtime view/capture obligations, and matrix boundary; it does not grant code leases or certify a native tuple implementation.

Luna outcome: **NO_SAFE_CODE_SLICE for the adopted arbitrary-finite source→inference→evaluation tuple extension in R168**. The adopted source authority does not settle all parser-accepted singleton/newline forms; the checked candidate graph and renderer are not the closed public scheme path; native constructor families are absent; tuple binding startup has no source fetch-class law. A partial pair or one-layer change would not meet the reviewed R149 boundary. No code leases were granted and no code edits occurred. R168 closes unfinished with the parent goal unchanged.
