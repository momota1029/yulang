# Current task: freeze `syntax-v0` and resume vertical implementation

Updated: 2026-09-17. Branch: `yulang3`; do not modify frozen `main`.

## Current user decision

The user's 2026-09-17 instruction closes the previous exhaustive per-slot CST-schema prerequisite and adopts the implementation-first completion policy in
[`2026-09-17-syntax-freeze-and-vertical-implementation-amendment.md`](../notes/design/2026-09-17-syntax-freeze-and-vertical-implementation-amendment.md).

The old loop of selecting the next bounded unmapped `Missing`/`Error`/`Invalid` candidate solely because catalog coverage remains open is finished. Do not restart it.

The current accepted grammar and direct Rowan topology are frozen as `syntax-v0` for the next implementation phase. Syntax may reopen only for a concrete structural collision, accepted-input/recovery bug, requirement exposed by the active vertical slice, or an explicitly approved new language feature.

## Governing authority

- Completion policy and freeze: [`2026-09-17 syntax freeze amendment`](../notes/design/2026-09-17-syntax-freeze-and-vertical-implementation-amendment.md).
- CST-derived diagnostic destination architecture: [`2026-09-09 CST-derived diagnostics amendment`](../notes/design/2026-09-09-successor-cst-derived-diagnostics-amendment-draft.md), narrowly superseded by the 2026-09-17 completion policy.
- Accepted input and recovery authority: [`2026-09-08 successor recovery authority`](../notes/design/2026-09-08-successor-recovery-authority-amendment.md).
- Direct Rowan CST and recovery topology: [`Rowan CST-only amendment`](../notes/design/2026-09-09-successor-rowan-cst-only-amendment-draft.md) and [`Error/Invalid topology addendum`](../notes/design/2026-09-09-successor-error-invalid-topology-ordering-addendum.md).
- Catalog/evidence: [`successor CST slot schema catalog`](../notes/design/2026-09-10-successor-cst-slot-schema-catalog.md) and [`coverage record`](../notes/progress/successor-cst-slot-schema-coverage.md). These are evidence and later certification inputs, not an automatic blocking queue.

## Retained hard invariants

- Parsing has one durable lossless Rowan CST. Do not introduce an AST/materializer, second syntax tree, opaque Error replay/relexing, or hidden recovery classifier.
- `Missing`, raw `Error`, and structured `Invalid` remain the structural recovery facts. Environment-only facts do not mutate the CST.
- Final diagnostics are CST/environment-derived. The existing parser diagnostic ledger is temporary migration state only.
- Preserve accepted syntax, UTF-8/CRLF source ownership, current-Item ownership, retry/continuation, caller and fence handoff, and effect-free rejection unless a concrete separately approved correction requires otherwise.
- Do not add CST wrappers or nodes merely to improve diagnostic wording. A new structural distinction needs a real information-preservation requirement.

## Phase status

### Syntax-design prerequisite

Closed for ordinary implementation.

The existing evidence spans multiple independent structures: declarations, expressions, patterns, Rule/String literals, Item/Separator/Close sequences, raw Error retry, nested/same-offset Missing, foreign-close/caller boundaries and fence handoff. That is sufficient representative proof that the CST-only architecture is viable.

Remaining unmapped owner/caller/trivia/nested/fence permutations are not individually blocking. They become work only when a concrete trigger requires them.

### Direct Rowan state

Direct Rowan construction and Error-token/structured-Invalid topology are already implemented. The legacy public parser cutover is complete. The temporary recovery/diagnostic machinery still exists: `HeaderInfo` retains recoveries and `ParsedFile::diagnostics` has not yet been retired.

Do not delete that temporary machinery before the new shadow interpreter is exercised. Also do not treat its continued presence as permission to make it a final dependency.

## Immediate next work: shadow CST diagnostic interpreter

This is the active implementation gate.

Status: the walk **shape** is fixed at test level in
`crates/yu-syntax/src/tests/recovery_output.rs` (see
`notes/progress/daily/2026-09-17.md`, "Gate 1 shadow CST diagnostic interpreter -
walk shape fixed"). The production walk itself is still unwritten.

Confirmed from CST alone, so the production walk can rely on it:

- a structured `Invalid` is the outermost recovery node at its offset, and no
  two sibling nodes ever start at the same offset;
- a maximal run of adjacent `Error` leaves at one immediate parent is already
  one committed record, so grouping the leaves is faithful, not lossy;
- same-slot same-offset occurrences are distinguishable only by preorder
  ordinal. Two encounters of the *same* kind at the *same* offset would be a
  genuine collision to report, not to merge.

Implement a whole-tree structural diagnostic walk in `yu-syntax` while leaving the temporary parser ledger intact for migration comparison.

Required behavior:

1. Walk every Rowan syntax child in deterministic source/preorder order.
2. Derive zero-width `Missing`, maximal adjacent same-slot/immediate-parent raw `Error` groups, and structured `Invalid` preorder from CST only.
3. When an occurrence matches an existing precise catalog entry, emit the precise schema-derived slot/expectation information.
4. When an occurrence is not yet precisely cataloged, emit a conservative generic structural diagnostic derived only from its CST occurrence: kind, range, occurrence/parent path and deterministic ordinal. Specialized expected alternatives/primary wording may be absent.
5. Do not consult parser recovery records to classify the new walk. No parse replay, Error relexing, hidden episode inference or synthetic recovery nodes.
6. If an occurrence cannot even be represented uniquely by the CST facts needed for distinct diagnostics, record the concrete collision and return only that owner to design. Missing specialized wording alone is not a collision.

### Focused evidence for this gate

Use a small representative set, not a coverage campaign. Include:

- one precise cataloged `Missing` case;
- one raw Error-group case with continuation/retry;
- one nested or same-offset case;
- one structured `Invalid` case if the current reachable topology supplies one;
- one UTF-8/range-sensitive witness;
- one deliberately uncataloged case proving the generic fallback is total and deterministic.

Do not add sibling permutations unless a failing implementation path requires them. Do not run a workspace-wide suite until a coherent phase boundary unless shared infrastructure changes make that necessary.

## After the shadow interpreter

Proceed in this order unless a concrete blocker changes it:

1. Complete the non-diagnostic effective operator-table unification so parsing and analysis use the same accepted table/site information.
2. Select the smallest **existing accepted** fixture that can exercise a useful valid-program path from source -> Rowan CST -> HIR/type analysis. Do not design new syntax for this slice.
3. Build that vertical frontend slice. Let implementation expose missing design information instead of pre-enumerating it.
4. Refine only the schema/recovery cases that the vertical slice or failing tests actually require.
5. Once the shadow interpreter has real frontend exercise and total CST-derived handling, perform the coherent parser-ledger/API retirement migration.
6. Reserve broad catalog completion, fuzz/property matrices and presentation specialization for explicit release/certification work.

## Concrete triggers that may reopen syntax/schema design

A new bounded schema or topology investigation needs one named trigger:

- a CST occurrence cannot be interpreted safely by the precise or generic path;
- two required facts are structurally indistinguishable in the CST;
- accepted input or required recovery continuation regresses;
- the active vertical implementation needs a precise distinction not currently present;
- explicit release/final certification requests exhaustive coverage;
- the user explicitly approves a new language feature or grammar change.

An unmapped catalog row by itself is not a trigger.

## Work-budget rule

Do not measure progress by schema coverage percentage during this phase. Do not select a new owner merely because the previous owner closed cleanly. Each syntax/recovery investigation must name what concrete implementation/release work it unblocks.

Use the lightest existing M0-M3 mode that covers the actual change. Repeated non-convergence returns to design under the existing round limit; it does not justify an expanding reviewer panel or an expanding malformed-input permutation table.

## Historical navigation

The former `tasks/current.md` exhaustive-gate log remains available in git history before this 2026-09-17 reset. Durable older evidence also remains under `notes/progress/`, especially `successor-cst-slot-schema-coverage.md`, `successor-typed-recovery-ledger.md`, daily records, and the 2026-09-12 handoff/navigation snapshot.

Do not copy that history back into this current-task file. Keep this file focused on the active gate, blockers, and immediate next action.

## Completion criterion for this task

The current task is complete when the shadow CST diagnostic interpreter is total over encountered recovery structure, the representative focused checks pass, and the next valid-program vertical frontend slice is selected from existing accepted fixtures. Full per-slot catalog completion is explicitly not part of this task.