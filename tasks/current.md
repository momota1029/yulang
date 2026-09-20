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

## Gate 1: shadow CST diagnostic interpreter

Status: implemented (2026-09-18). The production whole-tree walk lives in
`crates/yu-syntax/src/structural_diagnostic.rs`; its focused witnesses are in
`crates/yu-syntax/src/tests/structural_diagnostic.rs`. The temporary parser
ledger is untouched. See `notes/progress/daily/2026-09-18.md`.

The walk derives zero-width `Missing`, maximal adjacent same-immediate-parent
raw `Error` groups, and structured `Invalid` preorder from the CST alone. It
emits precise schema information for the mapped expression-delimited `Missing`
and raw-`Error` rows, and a deterministic generic fallback (kind, range,
ordinal, ancestor path) for every other occurrence. It does not consult parser
recovery records, replay parsing, relex `Error`, or synthesize recovery nodes.

Known deferred items, not blockers:

- the two mapped structured `Invalid` owners still take the generic fallback;
- trivia-interleaved forms of the mapped delimited row are classified by the
  nearest structural sibling and are fixed by a focused witness rather than by
  a separate catalog row.

## Gate 2: effective syntax-table unification

Status: implemented (2026-09-18). The planner in
`crates/yu-syntax/src/operator_compilation.rs` builds the effective table without
diagnostics (`effective_full_parse_operators`), and `conflicting_local_operators`
derives conflicts by reading the accepted site in that same table. `ParsedFile`
retains the exact table the parser used and exposes it through `operators()`.
The temporary diagnostic ledger is unchanged. See
`notes/progress/daily/2026-09-18.md`.

Known limitation, not a blocker: the operator-chain CST is flat and binding
powers do not change it, so "parse and analysis consult the same accepted site"
is proved by the shared table instance plus analysis agreement rather than by a
tree-shape difference.

## After the shadow interpreter

Immediate next action: Gate 3, the approved first `yu-hir` slice. The user
approved `notes/design/2026-09-18-hir-operator-association-first-slice-draft.md`
on 2026-09-18 (D1a/D2b/D3a/D4a): a whole-CST operator-chain association pass
producing a minimal pre-HIR product, with no type. `yu-types` remains empty.

Gate 3 is implemented (2026-09-19). `yu-hir` now associates every encountered
`OperatorChain` from the exact `ParsedFile` operator table into the minimal
owned pre-HIR product. Nested chains are associated exactly once and retained
only through their enclosing `HirExpr`; `AssociatedChains` retains top-level
chains only, under the user-approved ownership amendment at
`notes/design/2026-09-19-hir-associated-chains-ownership-amendment.md`.
Focused M2 verification and final delta review are clean. No type, declaration,
name-resolution, `DefId`, diagnostic-publication, CST, or `yu-types` work was
introduced.

The approved simple module-resolution slice is implemented (2026-09-19).
`lower_module` now produces a total immutable `HirModule` for direct-root simple
bindings, plans stable module-local identities before body lowering, and resolves
identifier bodies against that completed namespace. It consumes one exact-table
association result per body and one CST-derived structural recovery projection;
no whole-file associated-tree copy or parser-ledger dependency is retained.
`yu-types` remains empty and no type attachment, imports, module graph, parameter
patterns, application syntax, or core IR entered the slice.

Immediate next action: perform the coherent parser-ledger/API retirement
migration now that the CST-derived structural interpreter has real frontend
exercise through `lower_module`. Preserve syntax diagnostics' public behavior
while removing the temporary parser recovery ledger as a final dependency; do
not combine that migration with type attachment or a new HIR feature.

Gate 4 repair decision (user-approved 2026-09-20): the proven BracketRow
Item/Close structural collision is a concrete `syntax-v0` reopen trigger and
must be repaired at BracketRow CST ownership without Error-text inspection or
parser-private state. Preserve accepted input, recovery continuation,
current-Item ownership, fence handoff, and lossless source. The exact durable
topology remains subject to a narrow reviewed supersession record before its
implementation; this bounded correction does not authorize unrelated grammar
changes.

Gate 4 parser-ledger/API retirement is implemented and verified on 2026-09-20:
`ParsedFile::syntax_diagnostics()` now derives the public syntax projection from
the lossless CST plus the retained syntax environment, and the temporary
`recovery_record` module and all parser-private recovery classification plumbing
are removed. Parser-local construction phases remain only where they preserve
retry/continuation control; they are not diagnostic metadata. The public
diagnostic payload exposes schema-owned occurrence identity, path, ordinal,
slot, and expectations. Test contracts now distinguish coarse recovery censuses
from exact CST/public-schema assertions and retain TypeML context-restoration and
effect-free selector witnesses.

Verification: `cargo check -p yu-syntax --tests` is warning-free;
`cargo test -p yu-syntax --lib -- --test-threads=1` passes 1368 tests with one
intentional ignore; `cargo test -p yu-hir -- --test-threads=1` passes 26 tests.
The only remaining Gate 4 blocker is the separately recorded BracketRow
Item/Close collision: its narrow durable CST topology supersession and exact
implementation still require the user-approved topology choice. The collision
witness remains intentionally preserved and must not be weakened.

The question of how a type attaches to an associated expression is captured, not
decided, in `notes/design/2026-09-18-hir-type-attachment-open-questions.md`.

Proceed in this order unless a concrete blocker changes it:

1. Select the smallest **existing accepted** fixture that can exercise a useful valid-program path from source -> Rowan CST -> HIR/type analysis. Do not design new syntax for this slice.
2. Build that vertical frontend slice. Let implementation expose missing design information instead of pre-enumerating it.
3. Refine only the schema/recovery cases that the vertical slice or failing tests actually require.
4. Once the shadow interpreter has real frontend exercise and total CST-derived handling, perform the coherent parser-ledger/API retirement migration.
5. Reserve broad catalog completion, fuzz/property matrices and presentation specialization for explicit release/certification work.

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
