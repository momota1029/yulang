# Sprint R48 — temporal transport on the actual scoped-Apply helper route

Status: ACTIVE, revision 1
Proposed baseline: `ec1ba3ce2fa9553c821ac0ecb708adc9107ce136`
Branch: `research/simple-sub-intrusion`
Parent: unchanged full inference/evaluator theorem and original Simple-sub A/B,
quantifiers, source domain and accepted semantics; **OPEN, 0 → 0**.

## Fixed outcome proposal

Establish a bounded native temporal-transport result for the actual q helper
route, using R47's reviewed `FIXTURE_UNREACHABLE` result as an input. Preserve
the fact that each fresh helper preparation has no canonical-map hits. Do not
require or fabricate that event.

For the authentic q occurrence and its signed C/D extrusion pairs, retain enough
test-only owner evidence to connect:

```text
requested key -> capture representative -> reconstruction source/image
 -> ordered merge/compression/rollback transitions -> inspected route identity
```

The ledger must distinguish the two helper routes and each signed coordinate,
record committed and rolled-back transitions at their actual owners, and prove
the inspection edge for every accepted pair. A complete transition record with
no representative change is valid stability evidence. If the real fixture does
not reach q, does not retain enough ownership, or cannot authenticate a
transition, report the earliest exact obstruction and owner. Success is native
transport evidence only; it does not construct a source `Desc`, `D_q`, complete
Call rule or theorem gate.

## Parent scope and boundaries

No change to production behavior, source semantics, admission, allocation,
solver order, error behavior, expected outputs, public API or accepted source
domain. Every new observation field and event log is under `#[cfg(test)]`.
Preserve R47's no-hit invariant, the original negative substitutions and all
existing regression expectations. Do not infer identity from a final `rep`, a
generation alone, endpoint shape or a successful test. Do not build a different
fixture or substitute another consumer without a Luna revision.

The original theorem remains **OPEN 0 → 0**. In particular, source output
formation (`Desc`, exact ordered `D_q`), independent effect/result origins,
complete Call/effects, frame and alias obligations, evaluator correctness,
production authority and both original A/B claims remain separate.

## Baseline and direct dependencies

| Dependency | SHA-256 | Use |
| --- | --- | --- |
| `tasks/agent-loop/sprints/temporal-copy-evidence-20261019-r47.md` | `aba8009c8ec658af48ed2844e6a9c9b4554b4343ada19f8a7aae85b978574131` | Prior bounded witness and stop contract |
| `notes/theory/2026-10-19-r47-temporal-copy-refinement.md` | `2a8a076a2d245baf367a377a167de7ec6c1c499693934fb17610f69554c37d26` | Reviewed no-hit induction and missing-edge owner |
| `notes/progress/2026-10-19-r47-compiler-review.md` | `fd2e19217fcfa5394a84471b86aad0c4d55e163634439e6f6f48ba443fcd1460` | Independent compiler adjudication |
| `notes/progress/2026-10-19-r47-spec-review.md` | `2fa089b56d5f201e5e182cbc15cafab0508aac5d8fa00fb0d671f0942c867f46` | Independent specification adjudication |
| `crates/yu-solver/src/candidate_scheme.rs` | `8c370e47d5e8692a618fedf41be07d7ae3ac961f9070bfed6730e2b8e2f1137e` | Capture, reconstruction, helper route and consumers |
| `crates/yu-solver/src/candidate_intrusion.rs` | `7a57a93481095c6e7d4b8781810b1a5aa0d174e41ede29ac3f2b2b96bce10b0c` | Union, compression, transaction undo owners |
| `crates/yu-solver/src/candidate_source.rs` | `66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c` | Source actions and route scheduling |
| `crates/yu-solver/src/lib.rs` | `2300400e87d0a487225f207d414ac71fa4f21c6f80279fea4f793e43c7809aee` | Transaction journal, drain and rollback |
| `crates/yu-solver/src/shadow_apply.rs` | `d5e6b179fd4f6fbca579b0fa4d479d8bd11b520d774acbf27f414451c4691137` | Candidate Apply source/native ports; immutable input |
| `crates/yu-solver/tests/candidate_local_self_recursion.rs` | `47ced76fe8f0f136c42802b2376ca09f7cadec0fc8e5b1b3d4c6acc7bc613e55` | Existing actual-route fixture; immutable input |

All direct dependency hashes must be revalidated before activation. The grant
HEAD is `ec1ba3ce2`, pushed at R47 review integration; do not rewrite it if the
remote moves.

## Lanes and exact leases

### Luna — test-only owner ledger and consuming predicate

Inspect capture, reconstruction, `merge_candidate_rows`, compression, journal
rollback, route commit, `captured_source_matches` and the signed C/D join. Add
the smallest test-only ordered transition and route/allocation ownership data
that can authenticate the actual inspection. Keep raw historical source keys
separate from later representatives. Use the existing q fixture and preserve
its expectations.

Exact writes:

- `crates/yu-solver/src/candidate_scheme.rs`
- `crates/yu-solver/src/candidate_intrusion.rs` (test-only fields/hooks only)
- `notes/progress/2026-10-19-r48-actual-route-transport.md`
- `tasks/agent-loop/inbox/20261019-r48-implementation.md`

### Sol — independent temporal simulation and source/native application

Derive the owner transition relation from the pinned forest and journal
operations; cover successful merge, compression, route commit and rollback.
Identify what a retained event must prove about each captured key, copied
image, signed coordinate, route identity and inspection. Apply only the native
transport prerequisite to the original theorem. If a premise is absent, name
the exact owner and falsifier rather than infer stability.

Exact writes:

- `notes/theory/2026-10-19-r48-actual-route-transport.md`
- `tasks/agent-loop/inbox/20261019-r48-proof.md`

## Independent review and gated execution

After proof and implementation lanes freeze the same source snapshot, Luna
assigns fresh compiler and spec reviews. Review the event ordering, committed
and rolled-back transitions, actual q/C/D occurrence, both helper routes,
allocation and route ownership, the unchanged R47 no-hit condition, all negative
controls, and non-test byte behavior. A producer is not its own reviewer.

Only after both reviews find no BLOCKING or major issue may one owner run the
focused test:

```sh
RUSTC_WRAPPER= cargo test -q -p yu-solver --features shadow-apply-candidate --lib candidate_scheme::authentic_demand_capture_tests::active_outer_root_two_helper_uses -- --exact --nocapture
```

No other build or test process is authorized. A test pass is native execution
evidence, not a proof or source-semantic approval. Any changed review target
requires fresh review before execution.

## Resources and stop conditions

Total cap: **3000 seconds**, no carryover. Luna implementation 900; Sol proof
900; two fresh independent reviews 300 each; one gated test 180; Luna
integration 420. Astra zero. One verification owner and no parallel Cargo.
Reserve/charge grants on issuance; CPU/RSS stay UNKNOWN unless measured.

Stop at an independently reviewed and exercised temporal relation, or the
earliest exact execution/evidence obstruction, changed dependency/authority,
lease conflict or budget boundary. No test runs if the witness or reachability
premise is not supported. No new fixture, route substitution, source rule,
semantic change or budget expansion is implied.

## Primary grant

Luna revalidated the direct dependency hashes against the current worktree and
confirmed that all R47 writers and reviewers are STOPPED with no descendants.
The current-state record grants only the exact leases above and reserves the
3000-second cap with zero carryover. R48 is active at the stated baseline. Luna
owns reviews, adjudication, shared-state updates and all Git work.
