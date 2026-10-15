# Playground requests and normal Catch

Date: 2026-10-15
Branch: `research/simple-sub-intrusion`
Baseline: `2dc90eaeb78dd9b13277bb3f41b6d10dbf60759a`
Status: local suspension/normal-return gate complete; full objective OPEN

## Authority and owning implementation

Existing source-call scheduling, declaration Value/Computation roles, selected
ordinary computation semantics and Oracle shallow-Catch rules govern this gate.
No new source semantics or production backend is selected. Operation invocation
retains a whole inert argument, performs declaration-derived entry, creates a
request carrier and returns before its separate result consumer exposes it.
The missing result-effects annotation does not erase the operation's own event.

The machine now publishes exact resolved operation identity, fresh event, payload
and an opaque continuation handle. Normal Catch consumes its first total value
arm outside the removed delimiter; absence of a value arm preserves the original
value. Value-only and positively resolved nonmatching operation arms forward.
Matching or unknown candidates still require explicit handler evidence.

The raw suffix preserves original order, lexical/cell references and the exact
validated original receiver activation. It contains no store or active-stack
snapshot, and has no executable Resume consumer. A first unit receiver marker
lost constructor-known lineage; the accepted major finding was repaired at the
capture owner, then independently reviewed.

Verification exposed literal trivia in HIR spellings. The HIR owner now retains
only the Integer token or exact StringStart-through-StringEnd byte slice, leaving
all interior bytes and source identity intact. A further heredoc failure came
from Case/Catch's initial raw opener scanner. Its optional-label fallback now
uses the established literal-aware expression scanner, preserving coordinates,
fences, stops, recovery and label precedence. The Authoritative direct-literal
cone already specifies complete quote-run acquisition; no grammar choice changed.

Follow-up on 2026-10-16: the full shadow-HIR suite exposed one inline-lambda
test that intentionally equated integer payload with the whole trivia-bearing
node text under the earlier inline-HIR record. The reviewed literal-owner fix
supersedes that payload expectation while preserving C5's authentic node/range
contract. Pre/post specification review approved asserting payload equality to
the unique original Integer token and separately joining the branded source key
to the unchanged IntegerLiteral range. No trimming or range adjustment occurred.
All six `cargo test -p yu-hir --features shadow --test inline_lambda_local_source
-- --test-threads=2` cases pass (two build jobs, 300-second timeout).

## Proof and review

The [original request/control theorem](../theory/2026-10-15-playground-request-control-simulation.md)
is derived over every finite assigned machine prefix, including requests during
entry and nested continuations. It proves native-return-before-exposure, normal
Catch and exact nonmatching forwarding, suffix order/shared cells and original
receiver lineage. Final artifact before status synchronization:
`7a6159410ed97095dc4c863c7da273afb36d6e39c47fb90ced318fbc5cd84601`.

M2 uses two reviewers: `runtime_semantic_review` for actual source/control proof,
lineage and parser cause; `runtime_contract_review` for declaration/Catch/literal
contracts and pre-write regression expectations. All final/delta verdicts are
clean. The parser's three added tests retain all existing expectations and cover
labelled/unlabelled Case/Catch, normal and width-three/four strings, rule literal
openers and the exact original binding reproduction.

The independently reviewed [execution-owner theorem](../theory/2026-10-15-runtime-execution-owner-correspondence.md)
separately establishes the actual Invoke stack invariant. Module execution has
an ambient owner even when the receiver stack is empty; Force/global materialization
inherits the current owner. A tagged ModuleRun/Invocation decoder and installation
snapshot are the next implementation handoff, not existing handler evidence.

## Verification and resource budget

Primary-only Cargo, `CARGO_BUILD_JOBS=2`, `timeout 300s`, test threads two:

| Command | Final result |
| --- | --- |
| `cargo test -p yu-hir --features shadow local_source -- --test-threads=2` | 5 passed |
| `cargo test -p yu-playground -- --test-threads=2` | 55 passed |
| `cargo test -p yu-syntax case_like -- --test-threads=2` | 35 passed |

Earlier runtime-control runs exposed exterior-trivia and heredoc-opener defects;
the final 12 control cases pass, including both reproductions. No expectation
was weakened. Existing full ordinary-gate workspace check is historical evidence;
the next shared HIR phase will supply its fresh workspace boundary check.
No broad solver/backend suite or timing/benchmark process ran (zero samples).
Request propagation moves one frame per transition; capture does not clone stores
or active receiver vectors. Existing fuel bounds transitions, not all allocation.

Records synchronized: current task, research laboratory and design index. Public
README describes the current runtime boundary. The resolved parser question
remains archived at `aefa527a7`; no pending question is included in this checkpoint.

## Original remaining gates

### Actual owner implementation follow-through

The owner handoff is now implemented in `machine.rs`: ModuleRun remains distinct
from every receiving invocation; each Catch allocates a checked fresh installation
and retains its installer. Normal return checks the original owner, request
inspection keeps the candidate delimiter live until forwarding commits, and the
saved boundary preserves the exact installation. Work/storage per Catch is
constant and no owner registry or scan was added. M1 implementation and fresh
proof-delta review by `runtime_semantic_review` are clean; the original note's
§3.7 derives checks from pending receiver frames rather than assuming them.
The same bounded full playground command passes all 55 tests after this delta.

The [positive receiving certificate](../theory/2026-10-15-runtime-receiving-view-construction.md)
also passed independent proof review. Genuine explicit RootComp entry, same-view
receipt/Observe, current original receiver/handler ownership and written family
permission construct Grant; unknown inherited protection cannot veto it. The
runtime constructor/consumer bridge remains the next separate packet. General
negative completeness cannot be inferred from an empty recorded profile set.

Actual typed receiving views, receipts/Observe and a sufficient eligibility
certificate precede matching operation selection. Raw continuation execution, Function/B transport,
complete hygiene, general source coverage, native inference soundness/principality
and F5/production cutover remain OPEN. No finite test or local theorem closes them.
