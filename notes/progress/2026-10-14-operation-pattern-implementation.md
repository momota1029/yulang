# Operation-pattern parser and answered-question integration

Date: 2026-10-14
Branch: `research/simple-sub-intrusion`
Code baseline: `02c62f32139d76ba1b48758a8282a1e9747a8237`
Status: approved parser slice complete; operation-arm inference and hygiene remain OPEN
Mode: M2 parser implementation, two reviewers; M0 question archival; zero measurements

## Authority and delivered construction

The user approved the [reviewed operation-pattern contract](../design/2026-10-14-operation-pattern-tails.md)
with `まあだいたいこれでいいと思う．` and requested archiving the answered
question. Approval was recorded before code implementation; the parser contract
is Authoritative. No new handler or annotation semantics were selected.

Shared Pattern now constructs `PatternPathTail` for `::name` and
`PatternCallTail` for glued `(...)`, after any admitted prefix and at all
existing minimum precedences. Calls reuse Pattern's delimiter owner/loop;
internal payload commas and the following Catch continuation comma retain
their respective owners. Path members use native identifier retry and protected
Item/frontier behavior. Missing members, contextual guards, layout handoff,
chained tails and carried versus uncarried foreign closes follow the selected
contract. New kinds append at 285/286; all prior discriminants are unchanged.
Generic structural diagnostics retain owner, path, range and recovery kind.

The internal `PatternState` keeps native recovery readiness and the unresolved
path-member fact separately. Only an unresolved member sets the latter; a
successful member retry does not. ML/alternation and delimiter children,
contents and following tails retain it, including early/deferred exits.
Completion-returning boundaries project it to the existing two-variant
`PatternCompletion` API. No CST scan, global parser state or provenance
reconstruction is used. Cost is constant local state and OR operations at
existing constructor/merge points; source scanning and structural work retain
their existing asymptotic behavior. No material performance uncertainty
required another reviewer or timing experiment.

The source spelling `signal::ping(), k -> ...` now parses through ordinary
Catch/Pattern owners. Operation resolution, payload/raw-resumption binding,
eligible residual input construction and the hygiene bridge remain dependent
HIR/solver work. Parser success does not certify those gates or expand the
candidate's currently supported normal-return Catch slice.

## Review and repairs

Independent `compiler_referee` reviewed parser/recovery semantics and direct
state transport. Independent `spec_auditor` reviewed exact contract, kinds,
diagnostic publication and retained expectations. The latter also supplied
pre-write approval for additive discriminant assertions and fixture repairs.

Focused verification caught a lexical-token naming error and two new fixture
mistakes: continuation Pattern text includes its native leading space, while
the next arm's leading belongs to CatchBlock; complete bodyless Cast sources
require a semicolon. Only the new fixtures were corrected to these established
contracts. Existing assertions and semantic test names were not changed.

Review found unresolved path completion could escape an enclosing ML frame.
An initial general conjunction then conflicted with the full existing native
recovery table (`A | | B`, `A as | B`, `A | @ :`). The final owning repair
separates the two construction facts above and removes both that conjunction
and interim per-case neutralization. The original readiness operations remain
unchanged. Both reviewers accepted the final delta, including all path-fact
transport/early-return seams. No blocking or major finding remains. All child
leases are frozen/completed; no review or Cargo job remains active.

## Verification

Primary Cargo commands were serialized with `CARGO_BUILD_JOBS=2 timeout 300s`;
tests used `--test-threads=1`. Final code checks:

| Command after `cargo` | Result |
| --- | --- |
| `test -q -p yu-syntax --test operation_pattern_tails -- --test-threads=1` | 9 passed |
| `test -q -p yu-syntax --lib pattern:: -- --test-threads=1` | 88 passed |
| `test -q -p yu-syntax --lib -- --test-threads=1` | 1,399 passed; 1 existing ignored |
| `test -q -p yu-playground --test cli -- --test-threads=1` | 17 passed |
| `test -q -p yu-hir --features shadow --test catch_local_source --test conditional_local_source -- --test-threads=1` | 3 + 6 passed |
| `check -q --workspace` | Passed, no warnings |

The 88 Pattern cases are included in the full syntax result, not additional
unique cases. The package run covers Case/Catch, declarations/For/Cast, kinds,
structural diagnostics and public parse consumers. Before the final repair,
the focused CaseLike run also passed 30 cases. No full workspace test suite,
ignored test, benchmark or performance sample was run. Scoped rustfmt,
`git diff --check`, frozen artifact hashes and local link checks passed.
No broad rerun followed record-only updates. Deterministic tests do not stand
in for independent review or handler metatheory.

## Answered question and integration

The exact q1/r1 [negative-formal answer bundle](../../questions/2026-10-13-negative-formal-permission-field-law/approved-answer.md)
was validated by identity, exact embedded content, approved SHA-256,
provenance, branch, unchanged governing sources and pre-stage stability.
Question/draft/answer were committed together at `ef579dfd3`; current-file
equality with that commit was checked before consumption. Its
[receipt](../../questions/2026-10-13-negative-formal-permission-field-law/receipt.md)
and parser approval were integrated at `42ca58899`. Both commits were pushed
after full outbound-range inspection. The answered directory is tracked,
with original finalized contents and historical receipt retained. The answer
corrects the concrete-io example; it selects no complete A/B/C field map.

Primary synchronization covers `tasks/current.md`, `tasks/research-lab.md`,
the approved design and index, the question receipt and this checkpoint.
No shared record is deferred. The next executable gate is source-owned
operation/payload/raw-resumption formation using the parsed topology and the
already reviewed native residual primitive, while establishing its authentic
eligibility premise. No repeated approval of this parser contract is needed.
