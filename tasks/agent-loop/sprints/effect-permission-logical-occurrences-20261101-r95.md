# Sprint R95 — corrected exact-input verification for the R93 candidate

Sprint ID: `EFFECT-PERMISSION-LOGICAL-OCCURRENCES/20261101-R95`
Status: admitted by Luna on `yulang3`; see the paired admission receipt.
Branch / baseline: `yulang3` / `9a80a223ebb8b82eaf49fecc9454c5acfe1a636d` / `origin/yulang3`
Contract revision: 1
Input manifest: `tasks/agent-loop/sprints/effect-permission-logical-occurrences-20261101-r95-inputs-r1.json`
Input manifest SHA-256: `0cc19b0cc76cd5b9a456d62bb3a7d48d656698afefd22c1bc3eccfbd4ed4142c`

## Fixed outcome

Correct the R94 authority-record digest typo, independently verify the exact
unchanged R93 input, then run one bounded Lean check and capture the elaborated
theorem types and complete axiom reports for all ten declarations, or one
precisely classified diagnostic. R93 remains a statically reviewed unchecked
candidate; R94 closed before execution. The original source-preservation
theorem and all its quantifiers remain unchanged.

The exact stdin is the byte concatenation, with no inserted separator bytes, of
`OriginalSourceSyntax.lean`, `OriginalSourceGeneration.lean`, and
`SourceLogicalOccurrencesR93.lean`. Preserve `import Std`; remove only
Generation's `import YulangClosure.OriginalSourceSyntax` and R93's
`import YulangClosure.OriginalSourceGeneration`. The exact input is 106,897
bytes, SHA-256
`8bd62910afba8530f2140bd5b150db0d5fb5281c4651b87a88f78c51dc53d0d7`.

Success evidence is a passing independent check of the corrected authority
records and exact reconstructed bytes, followed by one Lean process that
accepts all ten declarations and reports their complete transitive axioms. Any
byte/hash disagreement, import/query mismatch, elaboration error, or
unacceptable axiom blocks acceptance. No repair call belongs to this packet.

## Lanes and exact permissions

**Independent exact-input delta review — at most 60 seconds.** Review only the
R95 contract/manifest correction, the prior R94 hash-block receipt, and the
manifest-pinned unchanged source/candidate inputs. Independently reconstruct
and hash stdin; confirm the corrected 64-hex digest matches the exact bytes and
the ten query pairs remain unchanged. Write only
`tasks/agent-loop/inbox/effect-permission-logical-occurrences-r95-input-review.md`.
No Lean, Lake, build, test, scratch, cache, Git, or source writes.

**Primary execution and integration — at most 180 seconds, including one Lean
call capped at 120 seconds.** After a passing input review, write the exact
authorization and timestamps to
`tasks/agent-loop/inbox/effect-permission-logical-occurrences-r95-verification.md`,
commit and push that authorization, then run the pinned Lean executable once
with the reviewed stdin, `-j1 -M1024`, one compiler process and no output files.
Capture full command, exit status, stdout/stderr, elapsed time, resource receipt,
all ten elaborated types and complete axiom reports in the same primary-owned
receipt. No Lake build, cache, project copy, worktree, scratch or second call.

**Independent result review — at most 120 seconds.** A reviewer other than the
input reviewer checks the pushed authorization, exact command/input digest,
exit status and all ten type/axiom outputs. Write only
`tasks/agent-loop/inbox/effect-permission-logical-occurrences-r95-result-review.md`.

Aggregate envelope: 360 seconds; Astra: 0. Unknown elapsed use is charged at
the full grant. R94's 32 seconds remain charged to R94; R93's unknown reviewer
time remains closed and is not reused.

## Boundaries and closeout

Only the three R95 inbox paths and compact sprint records assigned to Luna are
writable. The R93 candidate and its dependencies remain byte-identical and
frozen. No Rust edit, source-policy change, semantic admission change, or
compiler behavior change is authorized. No new environment, worktree, project
copy, cache, scratch, Lake build or test is allowed.

This check does not prove source-owned semantic admission, selected-formal
readout, source/native correspondence, original A/B, full effect hygiene,
principality, termination or production. Stop on any hash disagreement,
diagnostic, resource exhaustion or scope expansion. Repair requires a separate
bounded packet.
