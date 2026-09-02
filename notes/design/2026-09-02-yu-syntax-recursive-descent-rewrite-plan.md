# Authoritative: yu-syntax recursive-descent parser rewrite

Status: Authoritative

Approved-by: user

Approved-at: 2026-09-02

Scope: Replace the execution architecture of the `yu-syntax` parser with the
`chasa-recover 0.2` procedure-oriented core and explicit owner-to-owner item
transfer. This document defines only parser execution, migration, and
compatibility authority. It does not alter Yulang surface syntax, CST
vocabulary, AST shapes, diagnostic meaning, operator semantics, or Yumark's
written-language specification.

Drafted-by: primary agent from architect and compiler/recovery investigation

Reviewed-by: M3 compiler/referee, specification, and regression review; all
accepted findings closed by scoped delta review on 2026-09-02

User decisions recorded: on 2026-09-02, immediately suspend the
*uncompleted* legacy Yumark Gate 3b owner-adoption implementation and intend
its Authoritative adoption matrix to become required rewrite acceptance
evidence, rather than completing soon-to-be-removed legacy adapters first.
That operational pause preceded this approval. The same approval selects every
§6 execution decision and authorizes Gate 1 only; later gates remain subject to
their stated promotion evidence.

Authority: this document narrowly supersedes only:

- `2026-08-20-yu-syntax-chasa-architecture.md` §§159–267 and §§398–816, only
  insofar as those sections prescribe chasa parser values, `SourceInput`, or
  the `ParseLocal` implementation as the parser-execution procedure; and
- for *uncompleted owners only*, Gate 3b amendment §2's procedural
  representation and legacy AST/direct transport requirement: the
  `CanonicalRecoveryEpisode` object and its `LegacyAst`,
  `EmbeddedObservedAst`, and `Direct` transport modes; and
- for *uncompleted owners only*, Gate 3b amendment §4's requirement to adopt
  the remaining owners through that legacy procedure.

It does not supersede language, CST, AST, diagnostic, recovery-identity,
header/full, flat-`OperatorChain`, or Yumark contracts. In particular, Gate 3b
amendment §2's owner-local recovery fact and continuation outcome contract,
§3's identity and transaction semantics, and §§5–7's invariants and evidence
remain normative. Adoption matrix §§1–7 remain exact rewrite acceptance
contracts. This successor changes only the implementation route by
which an uncompleted owner produces those results; every finite owner still
requires completion evidence or an exact direct-owner-unreachable proof.
Completed E2, D11b, and D12a work remains a historical control, but those rows
must be re-executed and reclosed by their assigned rewrite gates rather than
counted complete solely from that history. The matrix is rewrite acceptance
evidence under this Authoritative plan.

No further uncompleted legacy owner-adoption slice is started. This plan does
not authorize a `yu-syntax` production-dispatch change before Gate 9.

## 1. Problem and ownership boundary

The rewrite addresses ownership rather than parser spelling. The current
implementation spreads cursor/boundary ownership, speculative state,
AST/direct recovery decisions, and commit-aware output across chasa parser
values, `ParseLocal`, scanner helpers, and adapter pairs. Replacing individual
combinator calls while retaining those owners would reproduce the same
ambiguity in a new API.

The new core owns only:

- recursive-descent grammar control;
- the direct-function contract that a fallible function does not consume input
  when returning `None`, with chasa-recover verification of that fact and an
  `R` checkpoint/rollback around the invocation; tuple/choice, not the direct
  function, own their enclosing input rollback;
- explicit handoff of one scanned item between grammar owners;
- owner-local recovery decisions and their continuations;
- committed direct mutation after an owner accepts a branch.

It does not own operator association. Dynamic expression parsing continues to
produce the authoritative flat, source-order `OperatorChain`. “Pratt” below
means NUD/tail dispatch with explicit item return, never a numeric
binding-power tree parser.

## 2. Non-negotiable compatibility contracts

Every promotion gate preserves all of the following.

1. The public `parse_file` product, full-source losslessness, and green-tree
   structure remain exact.
2. Existing parser-side AST projections remain exact where current tests or
   adapters require them. No AST/CST walk, source-range reparse, event buffer,
   or production shadow parse is introduced.
3. A recovery retains its typed owner/slot, kind, range, unexpected evidence,
   expectation union, primary expectation, diagnostic identity, and source
   order. A Missing remains zero-width; an Error consumes its designated
   malformed run or stops at its designated owner boundary.
4. A caller-owned close, stop, or layout boundary remains available to that
   caller. A child may not settle or consume it accidentally.
5. Header discovery and full parsing remain the existing approved two public
   phases. Header/full `DiagnosticId` reconciliation and immutable operator
   table construction remain exact.
6. Ordinary recursive descent has no language-defined nesting cap. Yumark
   retains its separately approved explicit frame stack for streaming document
   structure; this does not require a frame machine for ordinary parentheses.
7. The parser remains one-forward and source-backed: no eager whole-file token
   vector, replay, or AST/CST reconstruction path. The target static bound is
   `O(bytes + structural work)`.

The Gate 3b adoption matrix remains a normative recovery and rollback register
and is exact rewrite acceptance evidence. Its uncompleted legacy
owner-adoption implementation remains paused.

## 3. Core model

### 3.1 Input and source capture

The live input is a source cursor, initially `&str`, not a global token vector
and not a hidden token field in parser-local state. Source capture has two
public forms:

```rust
i.with_str(|i| value)                 // (value, consumed_str)
parser.with_str()                     // Option<(value, consumed_str)>
```

Both capture the dynamic interval consumed by their nested parser/procedure;
they do not mean “inspect the current remainder”. Capture is exact, UTF-8
safe, and borrowed for the `&str` implementation. A unit-state non-match still
preserves its input index and rolls `R` back; capture never performs input
correction.

The immutable root source remains available for byte-range derivation and
Rowan emission. `I = &str` uses common-root pointer-derived offsets: every
live remainder and borrowed capture must derive from the parse entry's root
slice, and offset derivation checks that its start and end lie in that root.
No origin-cursor wrapper replaces `&str`. Gate 1 proves this contract for
nested captures before `SourceInput` is removed.

### 3.2 Recoverable and committed state

```text
I = source cursor and capture capability
R = mutation that a speculative non-match must restore
S = non-recoverable simple state, used only after commitment
```

`FnOnce(In<I, R, ()>) -> Option<T>` is the direct grammar-parser form. The
fallible function itself does not transactionally restore input. Its contract
is that it must not consume input when returning `None`; chasa-recover compares
only the cheap input `Index` and panics without cursor correction if the
function violates that contract. The invocation marks `R`, runs through a
short reborrow, and rolls `R` back on `None`. Tuple and choice parsers own their
own enclosing input checkpoint/rollback. `i.check(parser)?` remains the
readable invocation spelling and does not add a second transaction.

`S` is one composite committed state containing the Rowan sink and committed
recovery/diagnostic publication. Fallible direct function parsers never
receive it. The supplied `then`
continuation is total; a non-unit custom `ParserOnce` must likewise be total
or leave `S` unchanged on `None`.

`ParseLocal` is not copied into a new monolith. Every current field has exactly
one eventual destination in the cumulative ownership map:

| destination | permitted contents |
| --- | --- |
| immutable context | root source, syntax environment, `OperatorTable`, selected header facts |
| explicit owner/frame value | grammar owner, non-numeric level, delimiter/stop/layout context that is threaded by the driver |
| `R` | speculative line/layout/delimiter/lexical/ambient state, expectation state, diagnostic allocation, and persistent embedded recovery state when a rejected branch can observe it |
| `S` | direct Rowan emission and committed records only |
| eliminated | a field with no remaining reader, witnessed by the gate |

No field may move to `S` merely to avoid implementing rollback. There is no
`ParseLocal` compatibility adapter. Gate 2 maps
only the pilot's transitive dependency cone and cannot promote a production
owner. Before each production owner promotion, the complete transitive
dependency cone used by that owner must be mapped. Gate 9's cumulative map
covers every old `ParseLocal`
field exactly once. An `eliminated` destination requires a no-reader witness.

### 3.3 Item, boundary, and tail protocol

The scanner yields a lazy, one-item logical cache:

```text
Item {
    leading_trivia,
    payload: Token | Boundary,
}
```

Every `Boundary` retains the same leading trivia as the item from which it was
classified. Its exact vocabulary is `Close(Delimiter)`,
`BorrowedClose(Delimiter)`, `Dedent(LayoutEvidence)`, `Stop(StopKind)`, and
`EofAfterTrivia`. If classification inspected a scanned token, the boundary
also retains that token and its exact extent, together with the logical source
position. The scanner creates lexical `Close` and `EofAfterTrivia`; the active
layout frame alone creates `Dedent`; the active stop-set owner alone creates
`Stop`; and only the owner transferring a caller-owned close marks it
`BorrowedClose`. A trivia-caused dedent and a caller-owned close with leading
trivia must be returnable and reclassifiable byte-identically without source
rewind.

A scanner builder first owns the current item's leading trivia. It either
classifies that same item as a trivia-caused boundary, or reads exactly its own
payload token to complete `Item { leading_trivia, payload }`. The latter is
current-item completion, not lookahead: no second logical item is read, cached,
or hidden in state. The completed item retains its logical identity, scanned
extent, and leading trivia; no retained bytes are rescanned.

The Pratt-style protocol is local to a tail driver:

```rust
tail(level, item, ...) -> Result<(), Item>
```

Within this protocol only, `Err(item)` means that the owner has not accepted
that item. It is neither `ParserOnce::None` nor a general recovery result. The
rejection is an owner transaction: it restores every owner-local `R` component,
including line/layout/delimiter/ambient state, expectation state, diagnostic
allocation, and persistent recovery state; restores explicit-frame mutations;
retains the exact pending `Item` identity; and leaves `IsCut` at its entry
value. It creates no Rowan, committed diagnostic, or committed recovery effect.
An implementation either checkpoints and restores all those values on `Err`,
or is structurally unable to mutate them before acceptance.

After accepting an introducer, the tail uses a total committed continuation
that emits or recovers to completion and returns `Ok(())`. It cannot use
`Err(item)` to undo an accepted introducer or any committed effect. Returned
items remain caller-owned.

`level` is exactly `TailPosition::Start | TailPosition::AfterOperand`; it is
never dynamic operator precedence. Delimiter, stop, and layout context live in
separate explicit frames. Pattern and TypeExpression may retain their own
fixed structural contexts where their existing language contract requires them.

## 4. Coexistence and promotion discipline

There is no old/new production crossing and no compatibility bridge. A
production replacement migrates the complete transitive callee closure of its
entrypoint, with one cursor, state model, and output path. It never executes
old and new parsers over the same owned source region, falls back from new to
old, rewinds a pending `Item`, or translates `IsCut`/`ParseLocal` across an
execution boundary. Existing frozen fixtures and matrices, not a replay
adapter, supply comparison evidence.

Gates 2–8 build and validate isolated new-owner closures only; they alter no
production dispatch edge. Gate 9 atomically replaces the root/canonical
production closure and removes all legacy callers. A stopped gate therefore
leaves the legacy production parser intact.

## 5. Migration gates

Every isolated owner closure and the final production closure use the same
acceptance template. It closes the exact Gate 0 coverage-ledger cells assigned
to that owner, including their ordinary controls, and preserves their existing
observations without editing expectations:

- exact parser-side AST/direct products and full CST hierarchy;
- lossless byte coverage, exact consumed range, and exact remainder;
- `ParseLocal::value_snapshot`, or an explicitly field-mapped equivalent for
  every value in the owner's transitive dependency cone;
- restoration of `R`, expectation sink, diagnostic allocator, `IsCut`, and
  pending-item identity after rejection;
- exact generic recovery node and committed-record identity, all fields, and
  source order; and
- embedded frame-pop cleanup and following-owner control where relevant.

A ledgered matrix row is closed only by this full template, not by a weakened
replacement assertion.

### Gate 0 — authority and decision closure

Before implementation:

1. record the approved §6 decisions and exact supersession scope;
2. update the design index and task routing;
3. reconcile the coverage ledger below against every finite matrix cell and
   owner slot; and
4. implement only Gate 1 after those records are synchronized.

No `yu-syntax` production edge changes in this gate.

#### Gate 0 coverage ledger

This is the exact and exhaustive routing ledger for the finite Gate 3b matrix,
not a list of illustrative citations. Family shorthand includes every listed
subcell and owner slot. Each cell must be re-executed and closed by its assigned
gate through the common acceptance template, or carry an exact
direct-owner-unreachable proof naming the matrix source location and the
production reachability edge that excludes it.

| finite matrix family or cell | migration gate and owner | mandatory controls |
| --- | --- | --- |
| E1–E14, including E7a–E7h and E12a–E12k | Gate 4 Expression owner | matrix §§2 and 5b plus the common acceptance template |
| P1–P8, including P7a–P7g | Gate 5 Pattern owner | matrix §§3 and 5b plus the common acceptance template |
| T1–T7, including T4a–T4h, T5a–T5h, and T7a–T7c; PV1 | Gate 5 TypeExpression and polymorphic-variant owners | matrix §§4 and 5b plus the common acceptance template |
| S1 and D1–D12, including every specified D3–D12 subcell; V1–V4 under both `Enum` and `Error`; NV1 under both owners | Gate 6 statement, declaration, and shared-variant owners | matrix §§5 and 5b plus the common acceptance template; the V3 four-slot and V4 two-close expansions are distinct cells |
| RB-E | Gate 4 Expression owner | matrix §6 rollback layer plus the common acceptance template |
| RB-P, RB-T, and RB-PV | Gate 5 Pattern, TypeExpression, and polymorphic-variant owners respectively | matrix §6 rollback layers plus the common acceptance template |
| RB-S, RB-D, RB-DRV, and RB-CMP | Gate 6 statement, declaration, Derives, and companion owners respectively | matrix §6 rollback layers plus the common acceptance template |
| committed-recovery → frame-pop → clean-following literal | Gate 8 Yumark adapter/frame owner | matrix §7 plus the common acceptance template |

Gate 0 must reconcile this ledger against every finite cell and exact owner
slot in matrix §§2–7 before Gate 1 begins. If the matrix names an exact subcell
or owner slot not contained in the finite sets above, it cannot be silently
erased: add it to the ledger or record a direct-owner-unreachable proof naming
its source location. Historical completion of E2, D11b, or D12a supplies a
control only; Gate 4 or Gate 6 respectively must re-execute and reclose it.
Gate 9 cannot promote until every ledger entry is closed or has that proof.

### Gate 1 — chasa-recover capture substrate

Implement `In::with_str` and `ParserOnce::with_str` with the §3.1 semantics.
Do not add unrelated combinators. Ordinary explicit Rust loops are used until
the first driver proves that generic repetition removes real duplication.

A generic fold is not implemented in Gate 1 or elsewhere in this plan. A later
approved plan may adopt an explicit `ControlFlow` fold only after a driver
proves real duplication. Its `Continue` must prove cursor advance or
replacement of the pending item; `Break` may retain the current item. A
zero-progress successful iteration is a contract panic, not an implicit
termination rule.

Evidence: nested captures, UTF-8, CRLF, rollback after failed capture,
zero-copy `&str` capture, and preservation of the existing direct-function
`None` / `R` / `S` contracts.

### Gate 2 — isolated execution shell

Introduce, without public dispatch:

- the Gate 0-approved `Item` / `Boundary` model and current-item completion;
- root-source range derivation;
- the complete `ParseLocal` field map for the pilot's dependency cone;
- speculative expectation and diagnostic-allocation state in `R`;
- committed Rowan/recovery publication in `S`;
- one owner-neutral control-flow driver with thin AST/direct materializers.

Evidence includes a token rejection, a trivia-caused layout boundary, and a
caller-owned close with leading trivia. Each returns byte-identically with its
exact item identity, scanned extent, logical position, and explicit EOF state
where applicable. The owner-rejection transaction proves restoration of every
selected `R` component, expectation/allocator/persistent recovery state,
explicit frames, pending item, and `IsCut`; no Rowan or committed diagnostic /
recovery mutation precedes acceptance. Accepted paths cover their bytes
exactly once. If any observation uses an old owner, it additionally proves the
legacy `IsCut` value is neutral at entry and unchanged at return.

### Gate 3 — fixed-tail pilot

Use Gate 3b E2 (`.` field and `::` path) as the isolated fixed-tail proof owner.
It is small but exercises leading trivia, returned boundaries, fixed-tail
dispatch, Missing/Error, ordinary AST observation, and direct Rowan. E2 does
not by itself prove borrowed-close ownership.

The complete existing E2 matrix control is retained unchanged: all embedded
`R(...)` rows, every applicable `A(...)` row, the ordinary direct primary
control, §5b primary-expectation assertions, and §6 RB-E input/local/sink/cut /
diagnostic-allocation/persistent-recovery-log assertions. Required literal
controls include `x.`, `x.@`, `x::`, `x::123`, and `x:: $name` wherever already
applicable. They assert the reusable acceptance template, including exact
remainder, CST parent, AST projection, recovery fact/record identity and order,
state snapshot, and no replay.

Gate 3 also attaches the Gate 0-ledgered matrix E3 borrowed outer-call close as
a supplementary inline reference/apply witness, retaining an attached
leading-trivia variation of its borrowed close. It proves the exact
borrowed-close owner, range, returned remainder, CST parent, and recovery order
without claiming that E2 supplied that evidence. The Gate 2 trivia-caused
layout-boundary control is retained alongside it. Both rejected-tail controls
prove the full §3.3 owner transaction, including `IsCut` whenever the old owner
participates. A special token stash in global state, source rewind, weakened E2
replacement, or owner-specific exception to the item protocol rejects the
pilot.

### Gate 4 — isolated expression-owner closure

Migrate the full expression owner and every transitive callee it needs under
the new tail driver in isolation. It changes no production entrypoint. Coverage
exhausts every existing
`OperatorChainItem` family: prefix, primary, nullfix, infix, suffix, every
`FixedPostfix` subfamily, ML argument, every `TerminalOuter` family,
`MissingOperand`, and `Error`. It also covers every reachable primary
structural form, delimiter and statement-block nesting, and dangling/malformed
operand recovery. Type annotation, `as`, and assignment `=` continuation
families are included whenever reachable from this owner; any family left for
a separate owner requires an exact boundary and reachability proof rather than
silent omission. Gate 4 closes every Expression cell and RB-E assignment in
the Gate 0 coverage ledger through the promotion acceptance template.

Closure evidence requires flat `OperatorChain` parity, including invariance of
CST/AST products under an operator environment change that changes only
association binding powers. The surface product remains BP-neutral and
source-ordered; no numeric precedence tree is built in this parser.

### Gate 5 — Pattern and TypeExpression owners

Build Pattern, then TypeExpression and polymorphic variants, as isolated
transitive closures. Existing mandatory-slot, delimited-sequence,
type-annotation, and outer-boundary recovery contracts remain the oracle. No
pattern/type family flag may leak into the shared item protocol. Each closure
closes every
P, T, PV, RB-P, RB-T, and RB-PV assignment in the Gate 0 coverage ledger with
the common acceptance template and has a complete transitive `ParseLocal`
ownership map before it enters the final root closure.

### Gate 6 — canonical statements and declaration shared owners

Build canonical statement/block sequencing and the shared declaration owners
before declaration shells: binding-style body, derives, declaration
companion, variant sequence/payload, then the individual declaration forms.
The Gate 3b matrix remains the finite recovery inventory. Each shared owner is
implemented once rather than reimplemented in every declaration adapter. Every S,
D, V, NV, RB-S, RB-D, RB-DRV, and RB-CMP assignment in the Gate 0 coverage
ledger closes with the common acceptance template before that owner enters the
final root closure.

### Gate 7 — header/full reconciliation

Build shared Use and operator-header grammar, then header discovery, in the
isolated closure. `HeaderInfo` carries
`HeaderSourceIdentity { SourceRevision, root_start, root_len }` plus frozen
header recovery records and their diagnostic IDs. `parse_file` rejects an
identity mismatch before reconciliation. Header allocation begins at zero;
full parsing starts after the highest frozen header ID and reuses a header ID
only for the same exact-site key. Any key mismatch is a failure; duplicate
publication and fuzzy diagnostic deduplication are forbidden. This preserves
valid-only header fact commit, opaque-body ownership, immutable operator-table
construction, header/full range coverage, exact expectation union/primary, and
`DiagnosticId` reuse.

Header scan and full parse remain existing separate public phase products, each
with one forward path. This is not a replay exception: neither phase permits
fallback, duplicate parsing of an owned region, `HeaderInfo` range/source/CST
reparse, or a replay adapter.

Public `scan_header` → `parse_file` witnesses include
`header-full-diagnostic-identity`,
`malformed-header-followed-by-valid-header`, and an unrelated-source/revision
mismatch. Each pins frozen header recovery record/id transport and exact
reconciliation.

### Gate 8 — Yumark convergence

Build embedded-Yulang adapters and remaining canonical recovery evidence onto
the isolated new-owner closure, retaining the Yumark frame stack, one-forward streaming, raw
fences, nested quote behavior, and frame-pop cleanup. “Multi-language
streaming” here means streaming only raw code-fence info and body bytes. Every
fence, including one whose info text is `yulang`, remains raw; this gate has no
parsed-Yulang-fence scope.

Named controls include the nested-quote/`yulang`-raw-fence rows in
`yumark_gate3_structural_driver_ast_direct_and_bridge_table`, the Authoritative
raw-fence table in the Yumark addendum Gate 3, and the adoption matrix §7
`\ref(x[,a]) \ref(1) [d]:f(2)` committed-recovery → frame-pop → clean-following
literal. Gate 8 retains the adoption matrix §7 frame-pop assertions and all
Yumark addendum Gates 3–7 acceptance tables. The Gate 0 coverage ledger's §7
frame-pop literal closes under the common acceptance template before the
approved Yumark grammar gates continue.

### Gate 9 — public cutover and deletion

Atomically promote root/canonical dispatch, remove obsolete legacy parser
entrypoints and adapters, and prove one production authority. Only after all
callers are gone may the old chasa dependency, `SourceInput`, and obsolete
session adapters be removed. Run the bounded package/workspace compatibility
gate once at this coherent boundary.

Gate 9 requires exact public fixtures or equivalent structured assertions for
`HeaderInfo` facts and ranges; the complete green-tree hierarchy and lossless
coverage; every typed diagnostic field and its source order; and imported/local
operator conflict paths. Syntax-kind counts alone are insufficient. The
cumulative `ParseLocal` ownership map covers every old field exactly once,
with no-reader evidence for each eliminated field. Every finite Gate 0 coverage
ledger entry is closed by the common acceptance template or has its required
direct-owner-unreachable proof naming the matrix source location. No old parser
caller, old/new crossing, temporary bridge, fallback, or duplicated production
owner remains.

## 6. Decisions resolved on approval

The user approved the following choices on 2026-09-02.

| decision | approved contract |
| --- | --- |
| source range representation | retain `I = &str`; use checked common-root pointer-derived byte ranges, never an origin-cursor wrapper |
| `Boundary` vocabulary and owner | `Close`, `BorrowedClose`, `Dedent`, `Stop`, and `EofAfterTrivia`, with the scanner/frame/owner classification boundaries in §3.3 |
| `level` representation | `TailPosition::Start | TailPosition::AfterOperand`; delimiter/stop/layout remain separate frames |
| final AST/direct structure | retain internal AST/direct adapters through Gate 9; any later removal needs a new approved plan after parity is proven |
| `ParseLocal` bridge | no compatibility adapter |
| committed `S` shape | one composite committed state for Rowan plus recovery/diagnostic publication |
| item completion | the scanner builder may read exactly the current item's payload token after leading trivia; this is not lookahead, and no second logical item is cached or rescanned |
| generic fold | excluded from Gate 1 and this plan; a future explicitly approved gate may adopt the stated `ControlFlow` / progress contract only after a driver proves real duplication |
| old/new crossing | no crossing: each production replacement is a complete transitive closure, and only Gate 9 changes production dispatch |
| header/full identity and transport | `HeaderInfo` carries `HeaderSourceIdentity { SourceRevision, root_start, root_len }` and frozen header recovery records/IDs; §5 Gate 7 defines mismatch, allocation, ordering, and reconciliation rules |

## 7. Stop and rollback conditions

Return to design before a further promotion when any of the following occurs:

- a rejected path needs to undo Rowan or committed diagnostics;
- an item or its leading trivia is lost, duplicated, or rescanned;
- a caller-owned boundary is consumed;
- an accepted loop iteration makes no progress;
- `R` becomes an unexamined replacement `ParseLocal`;
- a recovery fact leaks across a Yumark frame pop or changes its typed owner;
- AST and direct adapters make separate grammar/recovery decisions;
- numeric binding power changes parse output;
- a production fallback, dual parser, event buffer, AST/CST walk, or source
  replay becomes necessary;
- static resource reasoning finds whole-file tokenization, unbounded retained
  checkpoints, or non-linear rescanning.

A stopped owner gate leaves its prior production owner in place. It does not
authorize a partial cutover or a change to the existing compatibility fixture.

## 8. Review and verification budget

This plan and Gate 0 were M3. Independent compiler/referee, specification, and
regression review plus scoped delta review closed before user approval. Each
implementation gate selects the lighter M1/M2 reviewer set from its actual
risk; performance review is required only when static resource bounds are
uncertain or a gate adds material allocation/rescan risk.

Focused checks run per coherent gate. Broad package/workspace checks and timing
run only at the named phase boundary, not after record-only work or every
isolated owner.
