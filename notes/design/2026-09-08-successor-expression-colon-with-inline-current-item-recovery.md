# Expression Colon/With inline current-Item recovery

Status: Authoritative; private O3b inline construction complete

Date: 2026-09-08

Approved-by: user through the recovery-selection and simplification delegation
in `2026-09-08-successor-recovery-authority-amendment.md`

Drafted-by: primary from independent architecture, specification and lexical
Statement-admission feasibility audits

Scope: the inline current-Item recovery sites owned by
`rewrite/tails.rs`: ColonApplication initial RHS and locally-created inline
argument, With internal colon and inline canonical Statement body, plus a
mechanical lexical-only factoring of existing canonical Statement Item scanning
and admission needed for With's sealed Error run. The shared scan keeps the
existing canonical literal-first and selector order; it corrects the current
With-only omission of canonical literal admission without adding grammar.
Colon/With indented-block recovery-owner transport,
the architecture's active outer layout-sequence ownership correction, literal,
Statement/declaration owners, public dispatch and O4--O7 remain separate.

Authority: recovery-authority amendment §§1--3, typed-output amendment §§3--6,
expression-tail handoff addendum §§2.1 and 3--5, the architecture Colon
mandatory-slot tables and With typed-recovery/body-layout contract. The
architecture's current-depth comma-or-layout outer-sequence rule remains
authoritative; this narrow publication gate neither freezes nor certifies the
existing incomplete layout implementation.

## Slots and scope boundary

| owner / phase | role | expectation |
| --- | --- | --- |
| Colon initial inline RHS | `ColonApplication(Rhs)` | `Expression` |
| Colon inline argument after a locally owned comma | `ColonApplication(InlineArgument)` | `Expression` |
| With exact keyword without its owned lone colon | `WithBody(Introducer)` | `Punctuation(Colon)` |
| With present colon, or body retry after a missing introducer | `WithBody(Body)` | `Statement` |

Every Missing has the mapped role, zero-width site/expectation range, no
unexpected facts, exactly one expectation with `COMMITTED_RECOVERY_RULE` and
primary zero. Every Error has the mapped role/expectation and one
`OtherCharacter` token fact across its exact nonempty emitted run. Error
payload tokens retain native kinds; no accepted expression/declaration node is
fabricated inside Error.

`indented_statement_block_normalized` remains a shared Statement owner. Its
existing raw Missing/Error publication is not relabelled to
`ColonApplication(IndentedStatement)` or `WithBody(IndentedStatement)` here.
An absent or malformed indented body stays a named open transport gate; the
inline owner emits no duplicate record for child-owned indented recovery.

## Boundary, recovery and handoff

An accepted lone colon/With keyword commits a terminal tail. Inline slots
classify absence before accepting or emitting the current Item: abstract/fence
boundary, active stop, protected separator or close, ordinary EOF, explicit
line/layout boundary, and With's protected non-braced `{` or `::`. The initial
With colon absence emits exactly Introducer Missing; it does not cascade Body
Missing at the same boundary. A source lone colon selects Body, never
Introducer.

Every protected non-EOF Item and its remaining leading stays whole. Missing
anchors at the inspected abstract coordinate or remaining start. Ordinary EOF
may emit its remaining owner-leading before anchoring at EOF. Initial leading
of a malformed inline slot is emitted directly by its tail; internal leading
belongs to Error; retry/boundary leading stays outside Error. With's existing
accepted semicolon and outer comma/close ownership remain unchanged.

For a non-boundary non-admitted Item, emit one maximal nonempty lexical Error
run. Colon uses the total NUD current-Item lexer and stops before a protected
boundary or NUD retry. With uses the total canonical Statement current-Item
lexer and stops before a protected boundary or a lexically admitted canonical
Statement retry. That scanner first uses the existing canonical expression
literal payload rule, then the existing Statement payload rule; ordinary With
and sealed Error paths use this one lexical operation. Its admission check is
an exact lexical-only factoring of the current selector order: Struct, Enum,
Error, Mod, Type, Role, Impl, Cast, Act, For, visibility Binding, Use, then
non-visibility expression. It observes only the Item and live lexical
remainder; it starts no node, emits no token or record, invokes no grammar
parser and has no builder capability. Ordinary Statement dispatch retains a
thin wrapper over the same scanner and selector order.

After Error, suppress a second Missing for that slot and invoke ordinary outer
continuation with the retained Item, origin, line entry, stops, baseline, ML,
line/fence and ambient context unchanged. A Colon local comma starts the next
InlineArgument; an incoming outer comma remains unread. This change does not
implement the separate current-depth layout-newline authority correction. In
particular, the existing local-comma-before-newline ordering (including
`f:\n, x`) is retained without certification or a new expectation; correcting
it requires the current-depth outer-sequence frame and is its own gate.

## Required evidence

Exact fresh/frozen records must cover `f:`, `f:   `, `f: , x`, `f: x,`,
`f: @ @ x`, `f: @ ]`, local versus outer comma, active stops, EOF leading,
UTF-8/CRLF and quoted fences. Existing accepted colon terminality, flat chain,
outer comma and `::` controls remain unchanged.

For With, cover `f with`, `f with x`, `f with :: x`, `f with: `,
`f with:\nnext`, `f with: ;`, `f with ;`, malformed body retry to expression,
binding, use and declaration Statements, and a false declaration candidate.
Prove source/leading ownership, terminal semicolon/outer close handoff, nested
colon/With roles, seeded/frozen IDs and effect-free rejected With/fixed-tail
entry. Include accepted quoted and raw canonical-literal With bodies plus a
post-malformed-run literal retry, proving the shared literal-first scan. Retain
existing accepted With, fence and normalized owner controls.

## Execution boundary

This is M2: one implementation pass, at most one batched repair, and scoped
specification plus regression review. The lexical selector factoring is
mechanical and preserves exact accepted dispatch order; if any selector needs
output, grammar construction or a changed admission decision, stop this gate.
The static path is one current-Item lexical read and bounded selector probes;
there is no replay, retained run, rescan or new cache. Benchmark budget is zero
samples/processes. Synchronize task/index/ledger/daily before commit. No
public cutover follows.

## Construction result

Completed 2026-09-08. Colon initial and local-comma inline slots now publish
their typed records; With publishes Introducer and inline Body records. Their
Error runs use sealed lexical-only current-Item scans. Canonical Statement
scanning and admission are shared by ordinary With and the Error retry, with
the existing literal-first payload rule and declaration selector order retained.
The two protected malformed With controls retain their whole pending Item
instead of moving leading into the tail; their source literals remain unchanged.

The new recovery module passed 9 tests after implementation, and tails (14),
normalized (83), recovery-output (25), package check, scoped format and diff
checks passed. A Statement test for `my role = value` still fails, but the
primary reproduced the same assertion failure on detached baseline `de8e77f3`;
the test and its expectation remain unchanged. Independent specification and
regression delta reviews found no scoped defect. Benchmarks: zero
samples/processes. Indented recovery-role transport and the current-depth
layout outer-sequence correction remain explicitly open.
