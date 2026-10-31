# Sprint R94 — exact-input check for the R93 occurrence candidate

Sprint ID: `EFFECT-PERMISSION-LOGICAL-OCCURRENCES/20261101-R94`
Status: admitted by Luna on `yulang3`; see the paired admission receipt.
Branch / baseline: `yulang3` / `120db95f8f4ad9505ae245884f3c3ab7e8d18c71` / `origin/yulang3`
Contract revision: 1
Input manifest: `tasks/agent-loop/sprints/effect-permission-logical-occurrences-20261101-r94-inputs-r1.json`
Input manifest SHA-256: `e8a15ae3e3f749101cbb38631b7776dd8a36db0c68c59712158db34fe97bc370`

## Fixed outcome

Independently review the exact in-memory Lean input for the unchanged R93
candidate, then run one bounded Lean check and capture the elaborated theorem
types and complete axiom reports for all ten declarations, or record one
precisely classified diagnostic. R93 remains a statically reviewed candidate
with zero Lean calls until R94 produces execution evidence. The original
source-preservation theorem and all its quantifiers remain unchanged.

The exact input is the byte concatenation, with no inserted separator bytes, of
`OriginalSourceSyntax.lean`, `OriginalSourceGeneration.lean`, and
`SourceLogicalOccurrencesR93.lean`. Keep `import Std`; remove only the
inter-module imports `import YulangClosure.OriginalSourceSyntax` from the
generation source and `import YulangClosure.OriginalSourceGeneration` from the
candidate. The exact flattened input is 106,897 bytes with SHA-256
`8bd62910afba8530f2140bd5b0db0d5fb5281c4651b87a88f78c51dc53d0d7`.

Success evidence is a reviewer-confirmed reconstruction of those exact bytes,
then one Lean process that accepts all ten declarations and reports their
complete transitive axioms. Any byte/hash mismatch, extra or missing import,
missing or duplicated query, elaboration error, or unacceptable axiom blocks
acceptance. No repair call belongs to this packet.

## Lanes and exact permissions

**Independent input review — fresh `compiler_referee`, at most 300 seconds.**
Read only the manifest-pinned candidate, its two source dependencies, and the
listed R93 handoffs/review/outcome. Independently reconstruct and hash the exact
stdin, inspect the ten `#check`/`#print axioms` pairs and their import context,
and write only
`tasks/agent-loop/inbox/effect-permission-logical-occurrences-r94-input-review.md`.
No Lean, Lake, build, test, scratch, cache, Git, or source writes.

**Primary execution and integration — at most 300 seconds.** After a passing
independent review, write the exact authorization and timestamps to
`tasks/agent-loop/inbox/effect-permission-logical-occurrences-r94-verification.md`,
commit and push that authorization, then invoke the pinned Lean executable
once, with stdin only, one process, one CPU, at most 1,024 MiB and 120 seconds.
Do not run a Lake build or create output files, caches, project copies,
worktrees, or scratch. Record the full command, exit status, stdout/stderr,
resource receipt and all ten axiom reports in the same primary-owned receipt.
No second call or repair is authorized.

**Fresh result review — at most 200 seconds.** An independent reviewer who did
not author the candidate or input review checks the exact command/result and
all ten theorem and axiom outputs. Write only
`tasks/agent-loop/inbox/effect-permission-logical-occurrences-r94-result-review.md`.

Aggregate envelope: 800 seconds; Astra: 0. The primary may tighten these limits
to the actual available runtime. Each worker records actual start/stop evidence;
unknown elapsed use is charged at the full grant. R93's unknown reviewer time
remains closed and is neither reused nor reset.

## Boundaries and closeout

Only the three R94 inbox paths and compact sprint records explicitly assigned
to Luna are writable. The R93 candidate and all dependencies remain frozen.
No Rust edit, semantic admission change, or compiler behavior change is
authorized. No new environment, worktree, project copy, cache, scratch, Lake
build, or test is allowed.

This check does not prove source-owned semantic admission, selected-formal
readout, source/native correspondence, the original A/B claims, effect hygiene,
principality, termination, or production. Those obligations remain OPEN.
Stop on any hash disagreement, missing runtime evidence, resource exhaustion,
diagnostic, or required scope/dependency expansion. Any repair needs a separate
bounded packet and fresh review.
