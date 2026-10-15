# Unary lambda parser and boundary correspondence

Date: 2026-10-15
Branch: `research/simple-sub-intrusion`
Approval baseline: `71f649bbc1a856c6255e34decf2304edd52ed5af`
Status: parser implementation and original local construction obligations complete, independently reviewed

## Authority and construction

The user directly approved the reviewed
[unary-lambda construction](../design/2026-10-15-unary-lambda-parser.md)
with `基本的にはそれでいいと思う`. Commit `71f649bbc` records that approval.
This authorizes complete unary identifier headers, direct lossless CST and
ordinary full-expression bodies with caller-owned recovery boundaries.
Inline-lambda HIR, callback typing and runtime remain separate gates.

The implementation reserves a complete source-only header before dynamic
operator lookup in both NUD and actual LED ML admission. It uses the existing
raw maximal identifier and exact-arrow rules, logical inline trivia and fence
classification. Actual header consumption uses ordinary current-Item lexical
transactions and owns Backslash, Identifier, Arrow and the body OperatorChain
under one LambdaExpression. The body resets the association threshold and ML
mode while retaining its enclosing grammar's boundaries.

The construction proof and its source bridge are recorded in
[parser preservation](../theory/2026-10-15-unary-lambda-parser-preservation.md).
The initial header results did not close body preservation: constructive
inspection found a nested mandatory-operand counterexample and drove the
owning implementation repair. Tests are execution evidence, not this proof.

## Review and causal repairs

M3 selected independent semantic and specification review, plus a static
header-cost review. Convergence requires no accepted blocking/major finding
and independently reviewed construction correspondence. Review/repair is
limited to changed lines and their actual dependency cones after the initial
full parser review.

The initial lexical/header/CST review was clean. Specification review required
retaining split-arrow and doubled-backslash negative controls when retiring
the old research-only raw scanner. An initially invented second-slash recovery
expectation was corrected after source audit: root malformed-run recovery
retains its existing behavior. No old expectation was changed to fit output.
The retired research adapter now consumes actual LambdaExpression children and
Rowan ranges. Its historical Error-token expectations described the approved
parser gap, rather than a language rejection contract.

Proof inspection found `\x -> y + @\nnext`: nested prefix/infix mandatory
recovery retried a same-level next-line identifier inside the lambda. The
primary reproduced the boundary failure while same-line/deeper controls passed.
An initial unconditional baseline check fixed that witness but failed the
established standalone `@\r\n界` required-expression contract. That test remains
unchanged. The correction therefore transports explicit lambda-descended
recovery activation; it does not infer a boundary from ambient claims,
`SequenceContext`, or the mere presence of a stop mask.

Two additional source-owner failures were found before closure. If recovery
retired the returned separator's leading trivia; immediate If/Case/Catch/For
consumers could also reconsider protected punctuation as a new introducer.
Fresh indented child recovery could absorb a dedent before its sequence owner
had a chance to inspect it. Clearing inherited activation assumed a child
invariant that the actual constructor did not enforce. The corrected invariant
retains activation while rebasing its test to each child owner's actual
baseline and local token stops, then restores the caller's retained context.

Two new test assumptions were separately rejected by prewrite specification
review: Case labels use apostrophe rather than `@`, and an operator before a
separating newline is not necessarily admitted. Their controls must exercise
the actual lexical owners without changing ordinary operator selection.

All accepted findings are closed. Fresh semantic/specification delta reviews
converged on the rebased construction; the final Catch handler patch passed
fresh compiler-referee review. The same independent referee then reviewed the
consolidated proof, without producing it, and found no findings in the original
four obligations. The primary independently verified all 45 current proof
dependencies and applied the theorem to this implementation. The failed
fresh-child premise is retained as history, not as an assumption in the final
induction. No new language decision was introduced by these owning repairs.

## Verification and resource accounting

The primary is the only Cargo owner. Focused commands use
`CARGO_BUILD_JOBS=2 timeout 180s`; the known bounded syntax library suite uses
`timeout 300s`; tests use `-- --test-threads=1`. Historical resource inventory
and the current test inventory were inspected before the package-wide run.
No workspace-wide test, benchmark or Oracle execution is selected.

Intermediate evidence, retained to explain the repairs:

- Initial `cargo test -q -p yu-syntax --lib unary_lambda`: 9 passed.
- `cargo test -q -p yu-syntax --lib tails`: 47 passed.
- Initial `cargo check -q -p yu-playground`: passed without warnings.
- Negative-control repair: one unsupported new expectation failed, then all
  10 filtered tests passed after its source-based correction.
- `malformed_operator_operand` initially had two incorrect Error-node checks;
  Error is a token. After correcting that new assertion, the decisive boundary
  control failed and the same-line/deeper control passed. The first source
  repair made both pass.
- First full syntax library run: 1408 passed, one direct-helper regression
  failed, one pre-existing ignored. The old expectation was preserved.
- First explicit-capability focused run: 12 passed, three failed. Two failures
  were the new test assumptions above; the third exposed actual child dedent
  ownership. The implementation/proof gate remained OPEN.
- Rebased-child focused run: 18 passed, one new raw-remainder assertion failed.
  Prewrite source review corrected it to inspect the pending Item: lexical
  acquisition may already own the last token even when raw remainder is empty.
  The Catch optional handler comma and initial handler Pattern also received
  capability checks after independent source review found those two consuming
  transitions could bypass the protected handoff.

Final implementation checks on the frozen repaired code:

| Command | Result |
| --- | --- |
| `cargo test -q -p yu-syntax --lib unary_lambda -- --test-threads=1` | 20 passed |
| `cargo test -q -p yu-syntax --lib required_operand_cst_keeps_nested_nud_and_terminal_recovery_distinct -- --test-threads=1` | 1 passed; old CRLF/Unicode expectation unchanged |
| `cargo test -q -p yu-syntax --lib -- --test-threads=1` | 1417 passed, 0 failed, 1 existing ignored |
| `cargo check -q -p yu-playground` | passed, no warnings |
| `git diff --check` | passed |

The one ignored test is the existing manual Gate 10 public production
measurement in `tests/public_boundary.rs`. The package-wide syntax suite ran
twice: the first exposed the direct-helper regression, and the final run
verified the repaired candidate. The playground package check likewise ran
once initially and once after the production repair. No broad checks are
repeated for later record-only changes. Scoped formatting was limited to the
new/touched parser files; no whole-tree formatter was run.

Static cost inspection found O(header-prefix bytes) lookahead and O(1)
auxiliary space, with an O(1) non-backslash reject. Recovery activation is a
private bit carried through existing by-value contexts and tested at existing
transitions. Timing processes and measurement samples: 0.

## Remaining gates

This record does not establish full Callback Hygiene source acceptance,
inline-lambda HIR binding/capture, expected callback-context delivery, imports,
loop/library support, receiver hygiene, selective Catch or native execution.
The next HIR owner is `module/local_source.rs::Builder::expression`, with
authentic anonymous-parameter provenance and lexical restoration required.
Existing named Lambda machinery does not itself prove direct-literal callback
context delivery.

The independent [signed-copy source bridge](../theory/2026-10-15-computation-signed-copy-source-bridge.md)
was reviewed, repaired and integrated separately at `77870d207`. It establishes
one source-generated AE/body/RE copy and FreshUse route; general shared/merged
histories and global inference/runtime theorems remain OPEN.

The user subsequently requested archiving the resolved local parser question
and direct-resolution receipt. Their two-file historical archive records that
instruction and preserves the original question body; no separate
answering-primary bundle is fabricated. The completed HIR follow-on is
recorded separately at `266da3dd6`; callback-context work remains OPEN.
`tasks/current.md`, `tasks/research-lab.md` and the design index are synchronized.
