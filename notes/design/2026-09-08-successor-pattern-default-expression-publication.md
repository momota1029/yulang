# Pattern default-Expression Missing publication

Status: Authoritative; private O3b substep complete

Date: 2026-09-08

Approved-by: user through the ongoing recovery-selection delegation.
Drafted-and-checked-by: primary, without subagents or independent certification.

Scope: the two raw Missing sites in `record_default_after_equals`, their
required OperatorChain wrapper, and explicit caller-close handoff. No
Expression recovery-kernel redesign, accepted syntax change or public dispatch.

Authority: architecture RecordPatternDefault/DefaultExpressionStops and P7's
typed table (especially `{a =}`), matrix P7c, current recovery authority,
typed-output rules and the preceding Pattern sequence/slot amendments.

## Exact owning rule

An accepted literal field `=` requires one ordinary Expression product. A
recognized current NUD still enters the canonical `expr_from_nud_normalized`
with the same operator table, comma/right-brace stops, baseline, line, fence
and ambient context. Its nested Expression/literal diagnostics remain owned
by those callees and are not relabeled Pattern recovery. Those owners are
still part of the open O3b SCC.

If there is no current NUD, preserve the existing default-entry policy: emit
one empty OperatorChain containing one Missing, and return the current Item
to the sequence. A malformed ordinary Item is not consumed by the default
Missing; the sequence applies its own existing item/separator/close recovery.
This is not an Error-to-Missing conversion or a second Missing for a callee:
no Expression parser has been entered on this branch. There is no new default
Error producer or same-slot retry loop. PatternCompletion remains the existing
Pattern shape/context fact, not a claim that every embedded expression is valid.

The exact record is Pattern(RecordDefaultExpression), Missing, zero-width at
the selected anchor, no unexpected facts, one same-role ExpectedSyntax::Expression
expectation over that range, COMMITTED_RECOVERY_RULE, primary index zero.
It follows earlier nested-Pattern records and precedes sequence/close records.
A structured wrong-kind outer Record reserves before it, as already required.

The anchor is an abstract boundary's inspected coordinate, otherwise the
current Item's remaining start after only permitted leading emission. Forward
the existing explicit PatternCallerCloses through both default-entry routes.
An abstract boundary or explicitly carried nonlocal close keeps its entire
remaining Item/leading unchanged. Local RBrace wins over same-kind caller bits:
its preceding trivia remains field-owned, as does ordinary non-boundary leading
at comma/EOF/malformed input. The empty OperatorChain follows that permitted
leading; neither Missing nor its wrapper consumes a payload.

## Evidence and pre-write adjudication

Test `{a=}`, `{a=,b}`, `{a: p =}`, `{a: =}`, ordinary EOF, missing then
malformed sequence recovery, an unclaimed close, and a structured nested
Record default. Assert exact record roles/order, OperatorChain > Missing under
RecordPatternField, shifted coordinates and seeded/frozen output. For each
carried parenthesis/bracket, test bare and nested-Pattern defaults with spaces,
comments and newline leading; compare the whole Item and keep the actual outer
close owned by its parent. Cover quoted fences and same-kind local RBrace.
Accepted controls follow the existing default Expression and LC-5 grammars,
including nested defaults, newline NUD, ordinary expression literals and comma
ownership. No invalid-input legacy equality is required.

The existing `{a =}` test currently asserts a direct field-child Missing.
Retain that exact source but require the already-authoritative empty
OperatorChain wrapper and its Missing child instead. The existing normalized
fence test counts descendants and needs no expectation change. Any additional
failure requires explicit cause adjudication, not expectation matching.

Pre-repair acceptance audit: the newly added `{a="x"}` and `{a=~"r"}`
controls did not satisfy the governing maximal operator-shaped exact-Equals
rule. Both the direct guard and the prior Pattern lexical definition include
quote/tilde in that character class; `="` and `=~"` therefore do not introduce
a default. Do not change that lexical contract under this publication gate.
Retain both exact sources as rejected-Equals controls, with source/Recover
identity and no Equals/default product, and test accepted literal defaults as
`{a= "x"}` and `{a= ~"r"}`. This is a test-premise correction, not a new
recovery result or a claimed Yulang2 comparison. Nested literal recovery in
the rejected forms remains with the open literal SCC; those controls do not
certify its whole record inventory.

Implementation is one local fallback, the existing Pattern Missing kernel's
Expression expectation, and explicit close-capability forwarding. No new
chasa-recover/output API, source scan, stored context, recovery allocation on
accepted input, or change to the canonical Expression entry. Static cost is
constant work at the already-committed slot; no benchmark (zero samples/processes).

M2 primary-only; one pass, at most two repairs. Run the focused Pattern tests,
the known 533 related owner/output/literal/normalized-Pattern tests, one package
check and scoped format/diff checks. Synchronize task/index/single ledger/daily
before commit. This completes Pattern-owned raw sites only, not the recursive
Pattern owner, SCC, actual header/full/Yumark or atomic old-parser replacement.

## Construction result and verification

Both raw sites are consolidated into one typed default Missing fallback with
the required empty OperatorChain wrapper. Both bare and nested-Pattern field
routes forward the existing caller-close capability. There are now zero raw
Missing/Error constructors in `pattern.rs` and `pattern/`; the Expression and
literal callees remain explicitly open in the same SCC ledger.

The pre-change `{a=}` test failed for its missing typed record. Six new tests
now cover all listed roles, ancestry, full caller/fence Items, EOF, nested
reservations, exact-Equals rejection and accepted companions. The old `{a =}`
source is retained with the required wrapper. The first implementation run
passed 52/53; the only failure was the exact-Equals acceptance premise
adjudicated above (the related suite passed 537/538). No production repair was
needed after that run. The added pure lexical rejection test needed one
explicit LexIn type annotation; its input/Recover/operator identity checks pass.

- Focused Pattern: 54 passed, no failures/ignored, build 32.09s, tests 0.25s.
- Related owner/output/literal/normalized-Pattern set: 539 passed, no
  failures/ignored, 2.22s. Final binary inventory: 1,438 tests.
- Package check: passed, 6.96s; scoped formatting and diff checks passed.
- Existing warnings remain 38 test / 87 package. Benchmark use: zero
  samples/processes. No workspace suite or actual header/full/Yumark/public
  certification was attempted. Primary-only M2 is not independent review.
- Task, design/index, accumulating ledger and daily record are synchronized.

Exact final commands (the binary path records this build, not a stable API):

```sh
cargo test -p yu-syntax --lib rewrite::tests::pattern:: -- --test-threads=1
target/debug/deps/yu_syntax-b491637626fa8c73 \
  rewrite::tests::type_expr:: rewrite::tests::pattern:: \
  rewrite::tests::type_decl:: rewrite::tests::struct_decl:: \
  rewrite::tests::enum_decl:: rewrite::tests::error_decl:: \
  rewrite::tests::role_decl:: rewrite::tests::impl_decl:: \
  rewrite::tests::act_decl:: rewrite::tests::cast_decl:: \
  rewrite::tests::derives:: rewrite::tests::declaration_variant:: \
  rewrite::tests::normalized::normalized_type \
  rewrite::tests::normalized::ordinary_type_unmatched \
  rewrite::tests::output:: rewrite::tests::recovery_output:: \
  rewrite::tests::binding:: rewrite::tests::for_statement:: \
  rewrite::tests::case_like:: rewrite::tests::normalized::normalized_pattern \
  rewrite::tests::literal:: --test-threads=1 --quiet
cargo check -p yu-syntax
rustfmt --check --edition 2024 crates/yu-syntax/src/rewrite/pattern.rs crates/yu-syntax/src/rewrite/tests/pattern.rs
git diff --check
```
