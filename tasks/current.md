# Current task: F5 general Function scheme foundation

Updated: 2026-09-22. Branch: `yulang3`; do not modify frozen `main`.

## Active F5 gate

The reviewed proposal is
[`2026-09-21-f5-general-function-scheme-foundation-draft.md`](../notes/design/2026-09-21-f5-general-function-scheme-foundation-draft.md).
It carries the production source witness `my f x = x` through shared Pattern ML
application, one-parameter Lambda HIR, live polarized Function constraints,
SCC generalization, disjoint Q/R closure, and fresh incoming instantiation.

M3 architect, semantic, specification, and performance review is clean. The
user approved the atomic gate on 2026-09-21, with rollback to the design if
implementation contradicts it. The user also approved delimiter-scoped
non-binding Pattern evidence: `cast((f x)): A` is the production shared-grammar
witness, while direct Cast depth retains `PATTERN_STOP_ITEM` ownership. Immediate
next action: F5a is complete. Its focused syntax suite passed 1380 tests with
one ignored; `yu-hir` passed 46 unit/integration tests and five compile-fail
doctests; `yu-solver` passed 56 tests; workspace check, formatting, and diff
checks passed. Compiler-referee, specification, and regression review are
clean. F5b architecture inspection found two blocking API-lifecycle decisions
before its implementation may start:

1. `yu-types` must keep raw closed-arena mutation private, but downstream
   `yu-solver` must construct F4 Bottom/Int schemes and later F5c schemes after
   public `ClosedValueScheme::new` is removed. Select an inter-crate sealed
   high-level finalization gateway or change the ownership boundary; Rust has no
   friend-crate visibility.
2. The current standalone public `ConstraintStore::new(Arc<HirModule>)` admits
   Terms from an independently owned `ConstraintBatch`. The approved TermArena
   lifecycle instead moves that exact arena into the store during `solve`.
   Select removal/privatization, a batch-bound constructor, or an explicit
   transfer/share capability.

The user selected sealed finalization and a batch-bound store on 2026-09-22,
then approved logical Term-lineage clone ownership and fixed 256-slot Term
pages. The now-Authoritative amendment at
`notes/design/2026-09-22-f5b-closed-finalization-term-owner-draft.md` specifies
sparse branch storage, reusable closed-finalization staging, and deterministic
failure injection after clean M3 review. The independently authorized F5b
lifecycle substage is complete: `yu-types` owns the sealed generative
finalizer, transactional exact-capacity accounting, and fallible terminal
finish; `yu-solver` maps only the existing aggregate counters and publishes no
partial result on finalization failure. Collected `Term`s are now opaque,
batch/store-owned lineage handles; clone branches use disjoint sparse fixed
pages and standalone HIR-only store construction is removed. Immediate next
action: F5b is complete. `InferenceSession` now owns the checked dense live
value/effect rows, levels, origin/non-generic metadata, typed synchronous
frontier, one typed pair memo, delta-local canonical diagnostic completion,
and fallible workspace growth. `ConstraintBatch` retains immutable recipes
only, while final projections derive from live rows. The M3 semantic,
specification, and performance delta reviews are clean; retained F4 facts,
ordering, no-mutation, counter, and production-frontier contracts remain
covered. Next action: continue the already-approved F5c general-scheme closure
(polarity census, eligibility, Q/R closure, transactional component
publication, and fresh incoming instantiation). The F5c blocker around closed
`Top`/`Bottom` children is resolved by the user's choice on 2026-09-22:
introduce private closed-extreme Term nodes and extend the exact §32 TermView
surface as needed, preserving zero fresh Q/R allocation for structural
extremes. F5a continues to emit no source Function facts until F5d. F5e's
detailed public resource families and 1k/2k/4k certification remain deferred.

The current F5c implementation slice now has private closed-extreme Terms,
whole exact-bound Union/Intersection drafts, guarded self/opposite-polarity R
coverage, transactional all-member draft visibility, fresh R lower/upper
restoration, structured incoming routing with one public source route for a
normalized union whose public fact uses the canonical first-member
representative, and focused closure/round-trip tests. The user approved this
representative-fact policy on 2026-09-22; route publication still needs the
transactional rollback closure required by the amended design.
The gate remains open: component-scoped iterative summary sharing, complete
ineligible-variable rejection, non-pure effect closure, full closed-DAG
instantiation memoization, and end-to-end per-use failure rollback still need
implementation before F5c can be marked complete. F5e public observation and
scale/resource certification stay deferred.

The older syntax-v0 vertical-implementation record below remains historical
context and does not override this active F5 gate.

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
Item/Close structural collision is a concrete `syntax-v0` reopen trigger. The
Authoritative `2026-09-20-successor-bracket-row-close-topology-supersession`
selects direct `BracketRow > Error+` for Item and
`BracketRow > TypeDelimitedForeignClose > Error+` for each local Close retry.
It preserves accepted input, recovery continuation, current-Item ownership,
fence handoff, and lossless source without Error-text inspection or
parser-private state.

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
Gate 4 is complete: the approved BracketRow close wrapper is implemented,
generic CST-derived diagnostics retain distinct occurrence paths, M2
recovery/spec delta reviews are clean, and final verification passes. The next
frontend work must be selected by a new concrete vertical-slice trigger; do not
reopen completed parser-ledger retirement or the BracketRow topology without a
new contradiction or scope expansion. The next approved vertical slice is
direct-root `OperatorChain` HIR lowering under
`2026-09-20-hir-direct-root-expression-slice.md`; that neutral expression-owner
boundary is complete. The proposed next gate is the separately designed
`ConstraintBatch` collection boundary. Its exact expression-identity/type
semantics are Authoritative in
`notes/design/2026-09-20-directed-subtyping-integer-slice-draft.md`: the user
approved integrated choice 1 on 2026-09-20, and its M3 construction is complete.
The direct-root decimal-integer slice now ends at a total `SolvedModule` with
directed value/effect bounds and local `Unknown` results. Do not broaden it to
names, bindings, equality relations, generalization, annotations, or Core IR
without a new approved gate. Immediate next action: select the next concrete
vertical semantic slice from existing accepted input and the established
subtyping model.

The next binding-body-to-definition-root semantic gate is Authoritative in
`notes/design/2026-09-20-binding-body-definition-root-directed-subtype-draft.md`.
The user approved its recommended integrated choice on 2026-09-20 and its M3
construction is complete. Admitted bindings now own artifact-branded definition
roots; recovery-free integer bodies emit the value-only fifth relation, while
definition roots remain `Unknown`. Definition effects, name propagation,
equality, and generalization remain deferred. Immediate next action: select a
new approved vertical semantic gate; do not extend this relation implicitly.

Fixture-led identity inference is withdrawn as the active implementation
sequence. The active Authoritative design is
`2026-09-20-constraint-collection-scc-foundation-draft.md`: first collect the
complete definition/root/constraint/use structure, then build a sealed static
SCC/condensation plan and integrate its artifact-checked queries into the batch.
The frozen Yulang lifecycle is the semantic oracle; its superlinear incremental
graph mechanism is evidence rather than a code template. Identity-function
polarity remains later evidence. Open-root connection, closed-scheme
instantiation, generalization, and publication remain later gates. Immediate
F0 immutable collected definitions and dependency-only resolved binding-body
uses are complete with clean M3 implementation review. Collection remains one
HIR traversal plus one collected-endpoint pass; Name type/effect projections
and integer fact counts are unchanged. F1's standalone static SCC kernel is
also complete after three bounded M3 review/repair rounds. It uses iterative
Kosaraju over `parent -> target` arcs and freezes deterministic dependency-sink-first
components with exact internal/incoming use partitions. F2 batch integration is
complete after two bounded M3 review rounds: `ConstraintBatch` now owns one plan
frozen only after complete F0 endpoint resolution and exposes crate-private,
artifact-checked indexed queries without executing component semantics. The
F0-F2 foundation is complete. Immediate next action: design the first semantic
SCC execution gate over internal open uses, dependency-closed instantiation,
and atomic component publication before implementing any of them. Scheme/generalization
representation, recursive-cycle result,
Function syntax/types, application, methods/roles, and Core IR remain later
structure gates rather than fixture-specific extensions.

The F4 candidate is now drafted in
`notes/design/2026-09-21-oracle-aligned-f4-int-scheme-scc-draft.md`. A user
correction and direct Simple-Sub/Yulang2 audit rejected the intermediate
`Bottom | IntQueued | IntDrained` model: live inference retains exact
lower/upper bounds and propagates canonical constraint pairs; only
generalization performs positive coalescing, polar-variable elimination, and
the final `Bottom | Int` simplification. The revised delta has no remaining
blocking or major compiler-referee finding. The user approved the corrected
complete gate on 2026-09-21; F4 is now Authoritative and its atomic
implementation is active.

F4 implementation reached a material performance rollback condition: the
required 4,000-member unbounded-cycle debug witness remained active beyond 80
seconds because every root recursively re-expanded the same cycle. The narrow
draft addendum
`notes/design/2026-09-21-f4-bound-membership-summary-addendum.md` proposes an
exact `IntPositive` lower-bound membership bit owned and updated only by the
canonical `constrain` path. It adds no graph/worklist or second type authority.
Implementation of that summary was paused for M3 review and user approval; the
safe F4 core and complete synthetic scale matrix remain uncommitted while the
approved repair is applied.

The remaining pair-cache decision is resolved: the user selected fixed-size
session-local endpoint keys on 2026-09-21. The cache will use only integer leaf
tags and dense value-row ordinals; `Term`, definition spelling, and module-path
hash/equality are excluded. The addendum completed clean M3 semantic,
specification, and performance review and is now Authoritative. Implementation
may resume against the exact private classification, value-only counter split,
peak accounting, and staged 1k/2k/4k measurement contract.

The authorized summary/key implementation hit its explicit rollback gate: the
exact 1,000-definition unbounded-cycle test did not complete within 30 seconds,
so 2k/4k and broad tests were not run. Static audit derived the owner as cubic
opposite-row replay over an alternating 2N-row cycle, not summary or hashing.
The new draft
`notes/design/2026-09-21-f4-direct-bound-frontier-addendum.md` replaces only
physical transitive Var-pair materialization with synchronous direct adjacency
and generic atom-bound frontier transmission. Existing uncommitted F4 work is
preserved. The addendum completed clean M3 semantic, specification, and
performance review. The user approved it on 2026-09-21, so it is now
Authoritative; implementation, exhaustive reference evidence, and staged scale
certification are active.

F4 implementation and certification are complete on 2026-09-21. The solver
now executes the frozen dependency-sink-first SCC plan with exact lower/upper
Simple-Sub bounds, synchronous direct adjacency plus atom-frontier propagation,
atomic component scheme publication, and incoming instantiation. Finalized
definition roots project through their closed `Bottom | Int` schemes; resolved
binding-body Name occurrences remain exact `(Unknown, Empty)`. `Never` remains
ordinary bottom. The private fact-store rebuild lane contributes to the public
aggregate without expanding the approved counter API.

The final scale evidence uses isolated single-size 1k/2k/4k capped processes
and a separate actual-observation ratio witness over all listed fields. Final
semantic, specification, and performance reviews are clean. Immediate next
action: select and design the next structure-first type-inference gate; do not
extend F4 implicitly to direct-root Name, Function/application, local
parameters, methods/roles, imports, Core IR, or dynamic dependencies.

Direct frozen-oracle inspection superseded the user-approved R2 executor model
on 2026-09-21. R2's Failed/Blocked SCC outcomes, dependency blocking, generic
backend, completed-session conversion, lifecycle query, added availability API,
and tests are withdrawn in full. The Authoritative successor is
`notes/design/2026-09-21-oracle-aligned-static-scc-inference-session-draft.md`:
Yulang3 will use one concrete inference session, retain F2 as the static
dependency-sink-first scheduler, and continue erroneous definitions through
ordinary SCC closure/generalization as Yulang2 does. `Never` is ordinary bottom,
not an error sentinel. F3a safely archived and removed the uncommitted R2 code,
restoring the exact F0-F2 solver baseline. F3b is complete: the unchanged solve
state and admission/result-building path now live in one private concrete
`InferenceSession`, with no component traversal, placeholder executor, public
API change, or extra source-sized work. F4 now implements the approved scheme
payload, occurrence components, generalization, and instantiation under the
fixed ordering obligations.

The broader associated-expression type attachment question remains open in
`notes/design/2026-09-18-hir-type-attachment-open-questions.md`; this foundation
does not attach inferred types to HIR.

For the active SCC-foundation successor, the user's explicit structure-first
direction overrides the older existing-fixture-only ordering below. F0-F2 use
definition-use records and a static plan over current resolved-name HIR; do not add Pattern ML
application merely to obtain a surface witness for these gates.

Proceed in this order for work outside the SCC foundation unless a concrete blocker
changes it:

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

Use the lightest existing M0-M3 mode that covers the actual change. A repair
round that makes no material progress returns to root-cause or design
reconsideration; it does not justify an expanding reviewer panel or an
expanding malformed-input permutation table. Numeric review/repair round
limits do not apply.

## Historical navigation

The former `tasks/current.md` exhaustive-gate log remains available in git history before this 2026-09-17 reset. Durable older evidence also remains under `notes/progress/`, especially `successor-cst-slot-schema-coverage.md`, `successor-typed-recovery-ledger.md`, daily records, and the 2026-09-12 handoff/navigation snapshot.

Do not copy that history back into this current-task file. Keep this file focused on the active gate, blockers, and immediate next action.

## Completion criterion for this task

The current task is complete when the shadow CST diagnostic interpreter is total over encountered recovery structure, the representative focused checks pass, and the next valid-program vertical frontend slice is selected from existing accepted fixtures. Full per-slot catalog completion is explicitly not part of this task.
