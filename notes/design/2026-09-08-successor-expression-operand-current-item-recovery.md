# Expression required-operand current-Item recovery

Status: Authoritative; private O3b construction pending; checkpointed at the
user's pause request

Date: 2026-09-08

Approved-by: user through the ongoing successor-recovery selection and
simplification delegation. Drafted-and-checked-by: primary under the explicit
no-subagent direction; no independent certification is claimed.

Scope: `driver::required_expr_item_normalized`, its lexical scan and explicit
caller roles, plus the ForIterable boundary bypass to the same Missing helper.
Expression tails/delimiters, remaining If/Case/For recovery, literal and
Statement/declaration owners remain within the open O3b SCC. No public cutover,
accepted operator judge change, new role vocabulary or generic library API.

Authority: the current recovery-authority and typed-output amendments; the
architecture's dangling/malformed operator, If condition, CaseLike scrutinee/
guard and For statement contracts; the expression-tail handoff addendum's
three exits and retained child threshold/mode. Historical numeric-BP-removal
prose does not override that explicit handoff amendment. Yulang2 supplies
formally accepted-input evidence, not malformed-output equality.

## Roles and wrappers

The already-open OperatorChain owner passes an explicit initial recovery role
to the common kernel. The finite mapping is:

| caller | initial Missing/Error role | expectation |
| --- | --- | --- |
| accepted prefix/infix operand; ordinary required-expression wrappers | Expression(Nud) | Expression |
| If condition | IfExpression(Condition) | Expression |
| Case/Catch scrutinee | CaseLike(Scrutinee) | Expression |
| Case/Catch guard | CaseLike(Guard) | Expression |
| For iterable, including its newline/fence bypass | ForStatement(Iterable) | Expression |
| For inline body | ForStatement(Body) | Statement |

The For body expectation retains its statement-owner contract even though this
already-selected inline branch enters Expression. No wrapper is added or
removed: the kernel appends into its caller's open OperatorChain. Once a NUD
has been accepted, nested prefix/infix operands and other nested grammar owners
select their own roles. Do not relabel nested recovery to the initial caller.
ML arguments enter with an already-admitted NUD and have no independent raw
recovery site in this driver; nested prefix recovery is still Expression(Nud).

Each Missing has its role, zero-width site/expectation range, no unexpected
facts, one mapped expectation with COMMITTED_RECOVERY_RULE, primary index zero.
Each Error has the same mapped role/expectation and one OtherCharacter token
fact over its actual nonempty emitted run. Ordinary malformed payload token
kinds remain native; any operator payload in this rejected operand position
is a raw Operator token, not a fabricated accepted operator-use node.

## Boundary, recovery and handoff

Classify absence before accepting or emitting the current Item: abstract
fence/EOF boundary, active stop, explicit line stop, ordinary EOF, or an unread
close/non-NUD bracket opener. The last category currently returns silently;
it is a mandatory operand absence and must publish one Missing. Include it in
the shared absence predicate so caller condition/missing flags agree with the
kernel. A braced Expression NUD remains admitted unless its active stop owns
the opener; do not turn every brace into an unread boundary.

Ordinary EOF may emit its remaining leading in the open chain before anchoring
Missing at EOF. Every other boundary keeps its entire remaining Item/leading;
anchor at the inspected abstract coordinate or remaining-start. Leading
already emitted by a calling owner is not reconstructed or reassigned. Preserve
the exact current Item, suffix, successor coordinate and line-entry handoff.

For a non-boundary, non-NUD Item, emit its initial leading directly into the
open chain, then consume one maximal nonempty lexical Error run. Read forward
once per Item, stopping before a NUD or any absence boundary above. Internal
run leading belongs to Error; retry/boundary leading does not. Reuse the same
total current-Item/literal/operator scanner as ordinary Expression scanning,
through the existing sealed lexical Error-run capability. The active contextual
stop check uses the same lexical-only observation in both paths; it must never
call a grammar parser or builder from inside Error.

After Error, return a boundary unchanged with no second Missing, or append the
admitted NUD in the same child threshold, ML mode, stops, baseline, line/fence
and ambient context. Its leading is emitted by ordinary append logic outside
Error. Preserve normal completion/scan-again, same-Item unread-at-threshold,
and End/abstract-boundary propagation. No source replay, nested builder,
retained run/token vector, CST-derived extent or diagnostic sorting.

The ForIterable newline/fence bypass is a mapped publication site, not a
second recovery algorithm: call the common Missing helper with its existing
protected Item and role. Other caller bypasses remain explicitly open until
their owning construction step; no blanket owner completion claim.

## Pre-write evidence and adjudication

Start with the isolated mandatory operand callee receiving ` ]`, no active
close stop. Before the change the kernel hands the bracket out without a
Missing. Expected successor: one Nud Missing at the remaining gap start,
empty open-chain product, whole pending bracket Item unchanged. The proposed
full-entry `? ]` witness was rejected before entering the callee by the existing
operator judge; retain that literal as an effect-free rejection control, not
an invented accepted-prefix route or permission to change the judge.
Also prove ordinary EOF and an active comma/colon/close,
non-NUD bracket opener, line stop and quoted fence, before/after a raw run.

Verify malformed prefix/infix runs, retry to a prefix or literal, nested role
ownership, lower-threshold same-Item handoff and flat BP-independent output,
ML-mode preservation, UTF-8/CRLF/foreign-prefix extents, seeded/frozen records,
actual caller roles, rejected optional NUD and effect-free unread tail entry.
Caller-only tests may observe still-raw nested/sibling recovery but cannot
certify it as typed. Keep accepted source/control products unchanged.

Retain all existing source literals. The selected initial Error-leading change
and protected-boundary leading rule can change malformed-only CST parents,
Error text, insertion anchors and the new previously-silent absence. Audit
each affected assertion against these explicit rules before editing it.
Do not change operator-table selection, accepted whitespace/layout, wrappers,
threshold/ML propagation or literal grammar to make a test pass.

M2 primary-only, one implementation pass, at most two repair bundles. Static
cost remains O(bytes + structural work): accepted paths add bounded role/stop
checks, no recovery allocation, replay or extra source traversal. Benchmark
budget zero samples/processes unless material uncertainty is found. Run focused
new/operator/caller tests, the known related owner/output set augmented by its
direct caller/normalized controls, one package check and scoped format/diff.
Synchronize task/index/single ledger/daily before the coherent commit. O4 joint
certification, actual header/full/Yumark and atomic old-parser removal remain open.

## Pause checkpoint and exact reproduction

The user requested a stopping point before production implementation. No
production change was applied. The selected contract above remains the next
construction gate, not a completed implementation or independent review.
The production baseline is `7832ab2f`, after the completed Pattern-default
gate (539 related tests and package check passed at that checkpoint).

The temporary regression below was compiled as
`rewrite::tests::expression_recovery` and run with:

```text
cargo test -p yu-syntax --lib rewrite::tests::expression_recovery:: -- --test-threads=1
```

The corrected witness failed at its exact-record assertion: actual `[]`,
expected one `Expression(Nud)` Missing at `0..0`. Result: 0 passed, 1 failed,
1438 filtered out; build 39.68s, test execution 0.00s, existing 38 warnings.
The earlier attempt using `? ]` as an accepted entry failed at the optional
entry unwrap instead; it was not evidence of mandatory-callee behavior.
The retained test checks that source as effect-free rejection before entering
the actual isolated mandatory callee with ` ]`.

To keep the pause checkpoint bisectable, the temporary test/module declaration
was removed from the build and preserved verbatim below. Restore it to
`crates/yu-syntax/src/rewrite/tests/expression_recovery.rs` and add
`mod expression_recovery;` in `rewrite/tests.rs` when implementing this gate.
The required-callee signature below is the unchanged baseline signature;
thread the explicit Nud role when changing it. Do not rerun the optional-entry
investigation or relax the expected record. The current local test binary was
built with this temporary witness; use Cargo to rebuild before relying on a
direct test-binary run.

```rust
use super::*;
use crate::{
    rewrite::{ambient_claim::AmbientClaimView, driver::MlMode, statement::StatementLineHandoff},
    session::{
        DiagnosticId, ExpectationSources, ExpectedSyntax, ExpressionRole, GrammarRole,
        RecoveryKind, RecoverySiteKey, SyntaxExpectation,
    },
};
use std::sync::Arc;

#[test]
fn required_operand_unclaimed_close_publishes_missing_and_keeps_its_whole_item() {
    let operators = OperatorTable::from_declarations([OperatorDeclaration::new(
        "?", OperatorFixities::new().with_prefix(BindingPower::scalar(70)),
    )]).unwrap();
    let mut recover = Recover::new(&operators);
    let mut input = "? ]";
    let mut output = GreenNodeBuilder::new();
    output.start_node(SyntaxKind::Root.into());
    let rejected = expr_normalized(
        In::new(&mut input, &mut recover, &mut output), None, 0, 0, MlMode::All,
        StatementLineHandoff::OrdinaryLayout, 0, LineEntry::InLine, None,
        Some(AmbientClaimView::root_statement(0)).into(),
    );
    assert!(rejected.is_none());
    assert_eq!(input, "? ]");
    assert_eq!(output.recovery_slot_count(), 0);
    let mut input = " ]";
    output.start_node(SyntaxKind::OperatorChain.into());
    let (item, origin, line) = crate::rewrite::driver::expression_item(
        In::new(&mut input, &mut recover, &mut output), OperatorSite::Nud,
        0, LineEntry::InLine, None, 0, 0,
    );
    let exit = crate::rewrite::driver::required_expr_item_normalized(
        In::new(&mut input, &mut recover, &mut output), item, None, 0, 0,
        MlMode::All, StatementLineHandoff::OrdinaryLayout, origin, line, None,
        Some(AmbientClaimView::root_statement(0)).into(),
    );
    output.finish_node();
    output.finish_node();
    let (green, records) = output.finish_with_recoveries();
    assert_eq!(green.to_string(), "");
    let role = GrammarRole::Expression(ExpressionRole::Nud);
    assert_eq!(records, [CommittedRecoveryRecord {
        id: DiagnosticId(0), site: RecoverySiteKey { role, range: 0..0 },
        kind: RecoveryKind::Missing, unexpected: Arc::from([]),
        expectations: Arc::from([SyntaxExpectation {
            role, expected: ExpectedSyntax::Expression, range: 0..0,
            sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
        }]), primary_expectation: 0,
    }]);
    let NormalizedExit::Complete(Err(Either::Left(item)), LineEntry::InLine) = exit else {
        panic!("the same bracket must remain pending")
    };
    assert_eq!(token_kind(&item), Some(TokenKind::RBracket));
    assert_eq!(item.extent(origin).recovery_range(), 0..2);
    assert_eq!(input, "");
}
```

On resumption, implement the explicit-role kernel and shared lexical scan,
then its five caller sites (If condition, CaseLike scrutinee/guard, For
iterable/inline body) and the ForIterable bypass described above. Preserve
the selected ordinary wrappers' Nud role and the If condition's shared
absence flag. The wider exact-record, frozen, boundary, threshold/ML and
caller verification in the preceding section is still pending, not covered by
this one failing witness. No generic `chasa-recover` addition is needed for
the identified operation: existing `token`/`map`/`with_str` and the sealed
Error-run capability suffice.

This was M2 primary-only design/reproduction preparation with no completed
implementation pass, no production repair and no independent reviewer.
Benchmark usage: zero samples/processes. The final pause integration is
record-only; use diff/reference checks without rerunning broad suites. Task,
index, single ledger and daily record must all describe construction as pending.
