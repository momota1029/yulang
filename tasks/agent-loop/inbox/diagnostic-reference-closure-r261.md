# R261 assignment handoff — frozen revision 1

Handoff ID: `R261-DIAGNOSTIC-REFERENCE-CLOSURE-r1`.
Author: `/root/sol_r261_diagnostic_reference_closure`; no coauthors/descendants.
Status: **PREREQUISITE OBSTRUCTION / PARTIAL SOURCE DERIVATION**, independent
review pending. Writer stops after this handoff's final hash receipt.

Frozen theory:
`notes/theory/2026-11-02-diagnostic-reference-closure-r261.md`, SHA-256
`ed49a78f4e5f6fc6e768a4f31211389716206cf05676a8b2f9b7978e5ea7f8a5`.
This handoff's own SHA-256 is returned in the cessation message, avoiding a
self-referential hash. No further edits are authorized by this freeze.

## Parent and actual result

Unchanged parent: Yulang inference soundness and Rust implementation, full
accepted source domain, original Simple-sub A/B, arbitrary independent
satisfying assignments, shared witnesses, F1/FK1 and foreign continuations.
Immediate edge: `R70-ORDINARY-EXTRUSION-ENTRY-RETURN-1` / R250 SUFFIX250's
diagnostic-reference premise at an actually reached Diagnostics cut.

Use exactly R249/R250's initialized non-test successful-forward domain,
including successful prefixes producing diagnostics. No eventual Diagnostics
or successful-helper theorem is assumed. Reused: R249 retention and reviewed
R260 ORDER260 under their exact premises; R250 SUFFIX250 remains conditional.
R259 is route-specific evidence, not universal reference coverage.

Established source fact `DISPATCH-MEMO261`: every actual Value task whose
dispatch returns successfully has a Value memo for that exact raw task key on
dispatch return. Current-pair shortcut requires an existing raw memo; the
other successful Value branches admit one. Context consumption gates Effect
application, not Value memo admission. Explicit alias/rewrite/structural child
items have an actual admission/enqueue/dispatch chain; enqueue alone is not
memoization. This supplies only that local step of their reference argument.

At SUFFIX250, ORDER260 removes the ack-order premise. The above fact supplies
memo existence for real children at their successful dispatch step; carrying
each child to the cut in the required state remains necessary. No all-cut
diagnostic-reference theorem or parent premise is declared closed. Parent/A/B
delta **0→0**. Lean theorem/type/axiom audit NOT APPLICABLE; checker NOT RUN.

## Exact first remaining premise and owner evidence

`R261-COPIED-BOUND-FIBER-1` / R71 prerequisite, owner Luna for next admission:
establish adequate executable-child coverage from accepted constructors,
preserving physical source slot, raw BoundKey, canonical BoundKey and actual
fiber. A full origin-to-fiber bijection is neither required nor proposed.

Exact first scoped constructor: extrusion::candidate_insert_copied_bound,
`crates/yu-solver/src/candidate_extrusion.rs:619–633`, SHA-256
`80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61`.
Work::Bound is produced by the physical-slot snapshot at :135–181 and consumed
at :398–417. With canonicalization C:

```text
Kraw = BoundKey(r,p,b)             selected physical source slot
Kcanonical = BoundKey(C(r),p,C(b))  potentially different lookup
Kto = BoundKey(C(copy(r)),p,C(copied(b)))
```

The scoped constructor imports evidence_snapshot(Kraw,None) carrying
MissingOriginAssociation, then physically appends Kto via BoundTransport.
effect::candidate_bound_origin_with_evidence (:899–908) gives scoped
BoundTransport relation=None. effect::candidate_transfer_bound_origins
(:1045–1089) first walks exactly context.bound_cursor(Kraw), transporting
each real fiber to Kto, then separately copies diagnostic origins with
MissingOriginAssociation and no relation. This proves transport of known
fibers; physical readback/origin metadata does not establish a nonempty exact
source fiber head. Missing association is not a theorem that the head is empty.

Direct effect owner SHA-256:
`4becefc07b81c1b298cafa190a3698e9e15e94656e1f17390eee13435dcb9b15`.
Context owner SHA-256:
`a6e8bde3a187369ddf847a31f2ae6eb443434a34d819e44a7fc72c9788809905`.

Replay seam: extrusion:1091 records parent→Value child k before
context::candidate_context_begin_replay (:4428–4481) reads exact canonical
input fiber heads and enumerates new-lower×all-upper / old-lower×new-upper.
Ordinary dependency/frontier suppression may emit no fresh vector child;
incoming-use resets old frontier but cannot create a product from an empty
head. To discharge the recorded edge, derive an actual child item or retain a
prior real child with this exact diagnostic key and correct cut-local state.
ORDER260 says nothing about this existence/authenticity condition.

Equality canonicalization transports already known raw fibers to canonical
keys (:4649–4671); it does not supply the converse physical-slot coverage.
ParentCopy uses the same split copy/transport before merge redirection
(intrusion:640–664). Source qualification/recapture can activate pending
Parents but does not fill this association. These facts explain an unproved
R71 prerequisite, not an accepted-prefix counterexample or production defect.
No numeric row/relation execution was constructed.

## Coverage, omissions and next step

The theory inventories alias, fresh/reused rewrite, Function/Tuple/Record/
Variant, ordinary replay, Context Allowance discharge, restoration/FreshUse,
settlement reopening/merge replay and graph-inactive legacy/test fallback.
It follows actual dispatch memo shortcuts and delta admission. It identifies
Complete/Pending consumption and checked witness extension without certifying
all their premises.

Omitted after the required R71 stop: accepted-source physical/raw/canonical
coverage; suppression's prior child for the same diagnostic owner; source-wide
FreshUse/capture coverage; nested-start shared scratch lifetime; all-cut
Pending/delta ownership; external Complete status; witness-helper success.
All remain OPEN, together with eventual Diagnostics, R70 W, evidence, F1/FK1,
foreign continuations and full soundness.

Next in-scope recommendation to Luna: admit a bounded executable-child coverage
packet at Work::Bound/ParentCopy with exact input-fiber witness, then carry its
real child through frontier suppression and cut completion. Falsifier: an
accepted finite prefix records a child from a selected physical source slot,
has no adequate exact-input fiber or prior authentic child route, and reaches
Diagnostics without that child's admitted memo. R261 supplies no such prefix.
Do not require a stronger bijection to prove the needed existential coverage.

Implementation stays **NO_SAFE_CODE_SLICE**. Copy/transport and replay/
diagnostic owners were both inspected. No compiler change or approved
implementation TODO follows; provisional evidence TODO is only the association
and exact accepted-prefix falsifier above.

## Authentication, resources and cessation

Before any source-body read, manifest
`f6138d36052934093328e34c01102fc9155ea9d8a0ccfd19182af6e7e2d946ef`
and all **36/36 direct path/hash pairs MATCH**, zero mismatches. Four R260
inputs and nine listed reviewed R249/R250/R259 inputs also MATCH.
Contract `dd0858cc37c7512a9cfcc8ef17b7c045fd6464afd631a0e1769662c4a052a8a7`;
admission `fde144815d39f1c78445e181feb23e9534bb1ef3c542f03496389b3023469713`.
Administrative-only baseline movement is accepted from the primary admission;
no Git command was used by this worker. No owner outside the manifest was read
for source evidence. Remaining direct hashes and predecessor authors are
preserved in the authenticated manifest/inputs and theory.

Requested Sol/high; observed model/effort UNKNOWN. Allocation: 2,400 active
seconds, at most three substantive stages. Two stages used; active-time
measurement UNKNOWN because no entry clock was taken, no budget expansion.
Freeze clock observed `2026-11-02 08:45:54 UTC` before final artifact writing.
Read-only cat/sed/rg, python3 hashing, sha256sum and clock were used.
The initial `python` hash command failed because python is absent; python3
repetition passed. No Lean/build/tests/probes/Cargo, source edits, Git,
descendants, scratch/cache, central state or other workers' writes.

All new/written paths: exactly the theory above and this inbox. No scratch
paths. **WRITER STOP: after final hash receipt, no further writes; no active
research continuation remains running while awaiting Luna's intake/review.**
Producer does not independently certify this packet.
