# Expression indented Statement recovery-role transport

Status: Authoritative; private O3b construction complete

Date: 2026-09-08

Approved-by: user through the recovery-selection and simplification delegation
in `2026-09-08-successor-recovery-authority-amendment.md`

Drafted-by: primary from independent architecture and prewrite specification
audits

Scope: the shared indented canonical Statement block in
`rewrite/statement.rs`: caller-selected recovery-role transport and its
block-entry/child-slot Missing and lexical Error publication. It covers only
the direct normalized callers enumerated below. Braced/root Statement recovery,
caller body-introducer bypasses, nested declaration/literal recovery, the
current-depth Colon outer-layout-sequence correction, public dispatch and O4--O7
remain open.

Authority: recovery-authority amendment §§1--3; typed-output amendment §§3--6;
the architecture's Colon mandatory RHS, If, Case/Catch default-policy, For,
declaration-body and With typed-recovery contracts. The prior Colon/With inline
gate explicitly left this transport open. The user-delegated recovery selection
authorizes recording this finite implementation rule; it makes no new grammar
or role-vocabulary decision.

## Role transport

`indented_statement_block_normalized` takes a required caller-selected
`GrammarRole`. `StatementSequencePolicy::Indented` retains that value and
forwards it only to the shared block-entry and child-slot recovery sites. The
braced policy, its close recovery, and its existing role choices do not change.

Every role below has `ExpectedSyntax::Statement`.

| direct caller | transported role |
| --- | --- |
| ordinary indented-block wrapper; Colon tail | `ColonApplication(IndentedStatement)` |
| With tail | `WithBody(IndentedStatement)` |
| If / elsif / else body | `IfExpression(IndentedStatement)` |
| Case / Catch arm body | `ColonApplication(IndentedStatement)` (the architecture's existing default-policy block reuse) |
| For body | `ForStatement(IndentedStatement)` |
| Binding body | `Declaration(Binding(IndentedStatement))` |
| Mod body | `Declaration(Mod(IndentedStatement))` |
| Role body | `Declaration(Role(IndentedStatement))` |
| Impl body | `Declaration(Impl(IndentedStatement))` |
| Act body | `Declaration(Act(IndentedStatement))` |
| Cast body | `Declaration(Cast(IndentedStatement))` |

No new CaseLike role is introduced. A nested admitted Statement selects its
own recovery owner; the transported role never relabels nested recovery. No
role is stored in ambient context or inferred from a default inside the shared
kernel.

## Publication, boundary and retry

The opening boundary and a mandatory child Statement absence publish exactly
one Missing with the transported role, a zero-width site/expectation range, no
unexpected facts, one committed-rule `Statement` expectation and primary index
zero. Abstract/fence boundaries anchor at their inspected coordinate. Ordinary
EOF may first emit eligible remaining block-owned leading and anchors at EOF.
All other protected boundaries (separator, active stop, strict dedent or
unread close) retain the complete remaining Item and its leading; the Missing
anchors at the remaining start. This includes the dedent-leading ownership
rule: do not move boundary leading into the block merely to publish Missing.

For a non-boundary non-admitted Item, initial remaining leading is emitted by
the existing block/separator owner outside Error. One sealed
`emit_recovery_error_run` then emits a maximal nonempty lexical run using the
shared total Statement current-Item scanner and lexical selector only. It
stops before an admitted canonical Statement or any retry boundary. Internal
run leading belongs to Error; retry/boundary leading stays pending. The one
record has the transported role, expected `Statement`, and one
`OtherCharacter` fact spanning its exact emitted extent. No grammar parser,
node builder, source replay or retained Item vector is used inside Error.

Classify `payload.is_boundary()` before contextual active-stop observation in
both slot and retry boundaries. This preserves the total lexical-boundary
contract and prevents an abstract boundary from reaching a word-stop probe.
After Error, return a protected boundary unchanged without a second Missing,
or invoke ordinary canonical Statement admission outside Error with all
baseline, stops, line/fence, ambient context, successor coordinate and line
entry intact. Strict-indent admission, separator policy, sibling/dedent
progression and accepted layout remain unchanged.

## Required evidence

Add focused exact fresh/frozen tests for Colon and With empty written-indent
EOF (`f:\n  ` and `f with:\n  `), malformed initial and later siblings, retry
to expression/literal/binding/declaration, same-indent continuation and dedent
handoff. Cover every direct caller mapping above, nested owner preservation,
active comma/close/If companion, quoted fence before/after Error, abstract
boundary, UTF-8/CRLF coordinates and shifted origins. Assert full pending
Item/leading, successor origin and line entry where a boundary remains unread.
Retain accepted canonical Statement and normalized fence controls.

## Execution boundary

This is M2: one implementation pass, at most one batched repair, then scoped
specification/recovery and regression review. Static cost is one bounded role
value threaded through the existing loop and the existing linear lexical scan;
accepted paths allocate neither recovery records nor replay buffers. Benchmark
budget is zero samples/processes. Synchronize task/index/ledger/daily before a
coherent commit. Stop rather than broaden if a caller needs a new role, a
grammar operation inside Error, or a changed accepted layout/admission rule.

## Construction result

Completed 2026-09-08. The shared indented block now transports the finite
caller-selected role through its indented sequence policy and publishes typed
block-entry/child-slot Missing and sealed lexical Error records. The Error path
shares the canonical Statement lexical scanner, protects retry/boundary
leading, and short-circuits abstract boundaries before a contextual-stop
observation. Unread closes are a shared successor boundary, so they cannot
repeat the same Missing at equal indentation.

Seven focused tests passed; the direct caller, tails, inline, normalized,
recovery-output and Statement set passed 227 tests with the recorded baseline
visibility-collision assertion explicitly skipped, and the actual For module
passed 12. Package check, scoped format and diff checks passed. Independent
specification/recovery and regression audits found no scoped defect. Benchmarks:
zero samples/processes. Braced/root recovery, caller bypasses, remaining
Statement/declaration/literal owners and current-depth layout outer-sequence
correction remain open.
