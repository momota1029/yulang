# Syntax freeze and vertical-implementation completion-policy amendment

Status: Authoritative

Approved-by: user

Approved-at: 2026-09-17

Date: 2026-09-17

Scope: completion policy and construction order for the Yulang3 syntax successor. This amendment narrowly supersedes the exhaustive pre-implementation completeness requirement in `2026-09-09-successor-cst-derived-diagnostics-amendment-draft.md`. It does not change accepted Yulang syntax, direct Rowan construction, recovery continuation, current-Item ownership, fence handoff, lossless-source ownership, or the final one-CST/no-hidden-ledger architecture.

## Motivation

The previous construction gate required a complete independently audited schema for every `Missing`, `Error`, and `Invalid` slot before implementation of the CST diagnostic interpreter could begin. In practice that requirement decomposed into an unbounded stream of individually bounded M1 evidence slices. Each slice was locally reasonable, but the sequence had no project-level completion budget and produced diminishing architectural information while consuming the available model/review budget.

The purpose of design work is to make implementation safe and informative, not to prove every malformed-input permutation before implementation exists. Yulang3 therefore changes from

`design -> exhaustive slot proof -> implementation`

to

`design -> representative structural proof -> syntax freeze -> vertical implementation -> counterexample-driven refinement`.

## Retained invariants

The following remain binding.

1. The parser's durable syntax product is one lossless Rowan CST. No AST, materializer, second output tree, parser-private recovery classifier, or compatibility side tree is reintroduced.
2. `Missing`, raw `Error`, and structured `Invalid` remain the structural recovery facts. Environment-only facts such as operator conflicts do not mutate the CST.
3. Final syntax diagnostics are derived from the CST plus the selected syntax environment. The temporary parser diagnostic ledger may remain during migration, but it is not final architecture and must not become a new source of truth.
4. Accepted syntax and existing recovery continuation/ownership contracts remain unchanged unless a concrete contradiction or accepted-input bug requires a separate user-approved correction.
5. A recovery owner may not fabricate CST structure merely to improve wording or to satisfy an evidence table. Structural nodes are justified by syntax/recovery information that must actually survive parsing.

## Representative sufficiency replaces exhaustive prerequisite

Construction no longer waits for every recovery-bearing slot to have a bespoke audited catalog row.

Before leaving syntax-design mode, the implementation must have representative direct-CST evidence for the mechanisms on which the architecture depends: required-child `Missing`; terminal/local close `Missing`; same-offset nested recovery; maximal raw `Error` grouping and retry continuation; sequence Item/Separator/Close phase distinction; structured `Invalid` with nested retained syntax; caller/foreign-close/fence handoff; and non-ASCII/source-layout cases where byte ranges or ownership differ materially.

The existing Yulang3 evidence already spans declarations, expressions, patterns, Rule/String literals, delimited and sequence recovery, nested same-offset closes, retry paths, and fence handoff. That is sufficient to close the old exhaustive *pre-implementation* prerequisite. Existing catalog and coverage artifacts remain valuable evidence and release-certification inputs, but their unmapped rows are not an automatic work queue.

A new schema row is required before implementation only when one of the following concrete triggers exists:

- an implementation or test encounters an occurrence that cannot be interpreted safely;
- two required structural facts collide in the CST and cannot be distinguished from occurrence path/order/ancestry;
- an accepted input or recovery-continuation contract is violated;
- the current vertical implementation slice requires precise expectations or ownership that the existing schema does not provide;
- final release/certification work explicitly requests exhaustive coverage.

The mere existence of an unmapped owner, caller, nested form, fence variant, trivia variant, or malformed-input permutation is not a trigger.

## Conservative CST-derived fallback

The CST diagnostic interpreter must be total over recovery structure even while the precise catalog is incomplete.

For a cataloged occurrence, it emits the precise schema-derived diagnostic as previously specified. For an uncataloged occurrence, it may emit a conservative generic structural diagnostic derived only from the CST occurrence and source: recovery kind (`Missing`, raw `Error` group, or `Invalid`), source range, occurrence path/immediate structural parent, and source/preorder ordinal. Precise expected alternatives, primary choice, and specialized wording may be absent until that slot is refined.

This fallback may begin as an internal/shadow-collector representation; this amendment does not require an exact public Rust enum or stabilized presentation wording. What is required is that the fallback be deterministic and CST-derived. It must not consult parser diagnostic records, replay parsing, relex an opaque `Error`, infer a hidden recovery episode, or create synthetic recovery nodes.

A missing specialized expectation is therefore not a design blocker. A genuine structural collision is a blocker: if two diagnostics that must remain distinct collapse to the same indistinguishable CST fact, return only that owner to design and repair the CST schema at its source.

## `syntax-v0` freeze

The current accepted grammar and direct-CST topology are frozen as `syntax-v0` for the next implementation phase.

Do not change grammar, recovery ownership, or CST topology merely because a more elegant form is imaginable or because an exhaustive catalog row is still open. Reopen syntax only for a concrete collision, failing accepted-input contract, vertical-slice requirement, or separately approved language feature.

Documentation and schema precision may improve without reopening the grammar when the underlying CST and accepted behavior do not change.

## Revised construction order

### Gate 0 — representative structural sufficiency and freeze

Status: closed by the existing evidence base plus this user-approved amendment.

Record the freeze, stop selecting the next unmapped slot solely for completeness, and preserve the existing catalog/coverage documents as evidence rather than a blocking queue.

### Gate 1 — shadow CST diagnostic interpreter

Status: implemented (2026-09-18) in `crates/yu-syntax/src/structural_diagnostic.rs`; see `notes/progress/daily/2026-09-18.md`.

Implement a whole-tree structural diagnostic walk in `yu-syntax` without removing the temporary parser ledger yet.

The walk must:

- derive `Missing`, maximal same-slot/immediate-parent `Error` groups, and `Invalid` preorder from Rowan CST;
- use precise catalog entries where available and the conservative fallback otherwise;
- preserve source order and deterministic equal-range order from CST occurrence order;
- walk every syntax child even if later semantic work would fail;
- have no parser mutation or hidden recovery-state dependency.

Test representative existing witnesses, including at least one precise catalog match, one same-offset/nested case, one raw Error group, one structured Invalid case when available, one UTF-8/range case, and one intentionally uncataloged fallback case. Do not add per-owner tests merely to increase catalog percentage.

### Gate 2 — effective syntax-table unification

Perform the previously specified non-diagnostic effective-operator-table work. Parsing and analysis must consult the same accepted table/site information. Keep environment conflict analysis outside CST mutation.

### Gate 3 — first valid-program vertical frontend slice

Begin real frontend implementation without waiting for catalog completeness or parser-ledger retirement. Select the smallest existing accepted fixture that can exercise a useful path from source through Rowan CST into HIR/type analysis. Do not invent syntax for the slice.

The purpose of this gate is to make implementation expose missing design information. Any syntax/schema reopening must name the concrete counterexample produced by this vertical work.

### Gate 4 — atomic diagnostic migration

After the shadow interpreter is exercised by real frontend work and the encountered structural cases are covered precisely or generically, remove parser recovery-record state, reservations/IDs/frozen diagnostic reconciliation, and `ParsedFile` diagnostic storage in one coherent migration. Preserve accepted input, lossless source, recovery continuation, and the selected syntax environment/table.

Complete per-slot precision is not required for this migration; total deterministic CST-derived interpretation is required.

### Gate 5 — release/certification refinement

Only at a release or explicit certification boundary should the project spend broad budget on exhaustive catalog generation, fuzz/property coverage, cross-owner malformed-input matrices, or presentation-quality specialization. Prefer generated/mechanical coverage over one-agent-per-slot manual enumeration.

## Project-level work budget

The orchestration budget still applies to each local change, and this amendment adds a project-level rule for syntax completion:

- Do not create a new bounded schema task solely because another unmapped row exists.
- Every new schema/recovery investigation must state its concrete trigger and the vertical/release work it unblocks.
- When a focused implementation can continue safely with the generic CST fallback, continue implementation rather than expanding the schema proof surface.
- Repeated investigation of the same owner that fails to converge after the normal M3 round limit returns to design; it does not justify more reviewers or more permutations.
- Broad schema percentage is not a progress metric during vertical implementation.

## Narrow supersession

This amendment supersedes only the following parts of `2026-09-09-successor-cst-derived-diagnostics-amendment-draft.md` and dependent task wording:

1. the sentence requiring every affected slot to be listed before implementation;
2. Construction gate 1 as an exhaustive complete-schema prerequisite;
3. any task instruction that says to select the next bounded unmapped candidate merely because catalog coverage remains open;
4. the implication that missing specialized expectations/primary wording is itself enough to block interpreter construction or frontend work;
5. the old construction ordering insofar as it prevents shadow interpreter or valid-program frontend work before exhaustive catalog completion.

All one-CST ownership rules, Error/Invalid topology, environment-diagnostic separation, lossless-source requirements, and the final parser-ledger retirement direction remain authoritative.

## Completion criterion for the current phase

The syntax-design phase is complete enough to leave by default. Future work returns to syntax design only on a named concrete trigger. The next normal action is implementation, beginning with the shadow CST diagnostic interpreter and then a valid-program vertical frontend slice.