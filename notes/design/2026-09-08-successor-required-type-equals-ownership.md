# Required-Type equals ownership and field forward progress

Status: Authoritative; private ownership/progress correction complete

Date: 2026-09-08

Approved-by: user through the current recovery-selection/simplification
delegation. Accepted syntax is unchanged.

Drafted-and-checked-by: primary under the user's no-subagent instruction;
pre-write specification and causal audit, not independent certification.

## Cause and owning rule

`is_required_type_boundary` currently treats every exact `=` as an outer
boundary, even when no caller owns it. A tuple field always enters the shared
mandatory Type slot after the sequence has dealt with comma/close/semicolon/
caller/fence boundaries. `struct S(=)` therefore returns the same `=` with a
Missing, adds a separator Missing, and retries without consuming input. The
same cause affects Enum/Error tuple fields; named fields also misclassify the
malformed RHS, although their name recovery happens to consume it later.

The architecture's SD-T and SD-R explicitly assign a nonempty malformed field
primary to Type::Primary, with one forward Error and no same-slot Missing.
PTA-O/R instead protect `=` only when the surrounding Pattern occurrence has
an active Equal stop. The required-Type kernel already receives
`TypeOuterBoundary::EQUALS`; cast targets, act heads and relevant derives
owners already select it. The unconditional additional test bypasses that
ownership protocol.

Remove the unconditional Equals boundary. A fresh or recovering required
Type slot treats `=` as a protected boundary exactly when its caller selected
the existing EQUALS boundary. Otherwise the ordinary Type::Primary Error run
consumes it and retries a valid primary or returns the first safe boundary.
Keep native Equals payload kind and Punctuation(Equals) unexpected evidence.
No loop cap, result inspection, fallback scanner, field-specific Equals
exception, new policy flag, stop bit or chasa-recover API is needed.

Pattern annotation forwards PATTERN_STOP_EQUALS into the existing immediate
TypeOuterBoundary::EQUALS value. Consolidate its three Type calls into the
existing boundary-bearing entry, retaining caller-close bits, conditional IN
transport and the exact current completion rule: primary-found is required
only for an IN-bearing occurrence. Nested Type episodes continue suspending
the immediate outer boundary; same-episode tails/recovery retain it.

Other required-Type callers that do not own `=` now recover it as malformed,
including standalone Type, field RHS, equality TypeDeclaration RHS, role/impl
heads/descriptions, act source and unclaimed variant payloads. This is one
ownership correction, not a claim that those bytes become accepted syntax.
Callers with explicit EQUALS remain protected. Remove the newly zero-caller
plain required-Type wrapper; make its remaining completion-only test adapter
test-only. Do not alter the field sequence's other raw recovery sites here.

## Pre-write test adjudication and bounded reproduction

Retain the literal `=A` from
`required_type_primary_preserves_boundaries_and_accepts_an_ordinary_primary`:
move its no-owner case to a new exact Error/retry test and separately require
the original Missing/pending Item with explicit EQUALS. Retain `x: =` from
`standalone_pattern_annotations_delegate_mandatory_type_recovery` unchanged:
pre-write helper tracing shows `run_pattern` uses PATTERN_DEFAULT_STOPS, which
already includes Equal. Add a no-Equal-stop occurrence through the explicit
context harness; only that occurrence has one Primary Error. Actual binding
controls must prove caller-owned `=` remains outside recovery. Other boundary
rows are unchanged. These changes follow SD-T/PTA-O and the selected rule
above, not current output.

Before production edits, run only a single required-Type attempt for `=A`.
It must fail the new Error/progress assertion promptly on the old kernel;
do not execute the known unbounded field loop. After the helper passes, run
actual tuple regressions in a subprocess capped at 5 seconds and 1 GiB
address space. A failure of this cap is a failed progress check, not a skip.

Cover initial, post-comma, after-valid and after-malformed Equals, repeated
Equals runs, same-slot retry, named-field RHS siblings, local/outer close,
EOF, quoted fence, and accepted TypeApply/empty/trailing-comma controls for
Struct/Enum/Error. Seeded fresh/frozen and shifted-origin records must agree;
unclaimed Equals must not cause caller-role Missing or zero-progress retry.
Existing raw field separator/close Missing sites remain raw in this gate and
must not be mislabeled as fully migrated declaration recovery.

## Verification budget and exclusions

M2 shared recovery/Pattern adapter correction, primary-only, one implementation
pass and at most two batched repairs. Start with the bounded helper failure,
then focused Equals/field tests, Type and Pattern filters, and the known-small
caller/output filter set plus binding/for/Pattern delimiter controls after
checking their inventory. One package check, scoped rustfmt/diff checks.
Benchmark budget: zero samples/processes; the capped run is a correctness
check, not a performance experiment. No broad workspace suite or independent
review. Complete typed-owner ledger, other raw recovery, matrix D4e and actual
embedded/header/full/Yumark/public gates remain separate.

Pre-fix reproduction: the single-attempt Equals test failed promptly with
empty emitted text rather than `=A` (one failed, 0.00s execution; build 46s).
No tuple loop was executed before the owning correction. Additional Pattern
callers inventoried: binding 7, for-statement 12, case-like 12 tests.

## Construction result

Removed the unconditional Equals boundary; Pattern now forwards its existing
Equal ownership through TypeOuterBoundary. Its three Type branches share one
call while retaining conditional IN completion. No field-loop exception or
new recovery/context API was introduced. The zero-caller plain Type wrapper
is removed and the completion-only ambient adapter is test-only.

Five new Type tests cover the bounded callee witness, exact explicit-Equals
handoff, Struct/Enum/Error named and tuple siblings, seeded/frozen/shifted
close/EOF/quoted-fence handoff, and accepted empty/TypeApply/trailing-comma
controls. Pattern and binding add two integration tests; the latter includes
ArrowRhs and nested Call recovery before the real binding Equals. The old
`=A` literal remains in both ownership modes. Default Pattern `x: =` remains
unchanged because its existing default stop set includes Equal. The separate
no-owner Pattern control now recovers it.

The `(A =T)` sibling retains its one existing raw field-separator Missing;
its distinct malformed Type record is Primary Error. Raw field/close sites
were not migrated or disguised as typed here.

Validation:

- Before/after: `cargo test -p yu-syntax --lib rewrite::tests::type_expr::equals_recovery::required_type_unclaimed_equals_consumes_and_retries_one_primary -- --exact --test-threads=1`
  failed before and passed after the production fix.
- `timeout --kill-after=1s 5s prlimit --as=1073741824 -- target/debug/deps/yu_syntax-b491637626fa8c73 rewrite::tests::type_expr::equals_recovery:: --test-threads=1`:
  all five passed in 0.06s; neither cap fired. No skip or timeout result was
  accepted as success.
- The same binary with the two new Pattern/binding test names: 2 passed.
  Type and Pattern filters together: 222 passed (196 Type, 26 Pattern).
- The same binary with the 16 filters listed in the required-Type checkpoint,
  plus `rewrite::tests::binding::`, `rewrite::tests::for_statement::`, and
  `rewrite::tests::case_like::`, `--test-threads=1`: 470 passed, zero failed/
  ignored, 1.10s execution.
- `cargo check -p yu-syntax`, scoped `rustfmt --check --edition 2024`, and
  `git diff --check`: passed, existing 87 package / 38 test warnings.

One implementation pass, zero repairs. Final test build took 1m08s; one
environment observation found active rustc at about 1.53 GiB RSS. Execution
remained small. Benchmark budget consumed: zero samples/processes. No
independent review, broad workspace check or public certification. Task,
design index and daily progress are synchronized; Type/PV ledger and D4e
documentation reconciliation are next.
