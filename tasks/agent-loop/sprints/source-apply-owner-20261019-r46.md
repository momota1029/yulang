# Sprint R46 — trace the source-owned Apply result for `q = loop y`

Status: ACTIVE; revision 2 supersedes revision 1 after adding direct pins for the original formation laws
Branch / baseline: `research/simple-sub-intrusion` / `55ed588e7`
Contract revision: 2
Parent: unchanged full inference/evaluator theorem and Simple-sub A/B, original
  quantifiers, accepted source domain and semantics; **OPEN, 0 → 0**.

## Fixed outcome

Establish an occurrence-specific correspondence from the actual source `q =
loop y` through HIR Apply construction, `ApplySourceInput`, native Apply
ports, and the typed Result consumer. Determine whether existing authoritative
formation rules, instantiated at those same occurrence/provenance identities,
construct the authentic output, effect, and result-port owners with the exact
ordered dependency telescope `D_q`. If the chain stops, name the first precise
unsupported judgment, its responsible source/rule owner, and the missing
premise. Apply any established evidence to the original parent without
weakening its scope or treating a bounded result as closure.

This changes the method after R45's independently reviewed bounded obstruction:
trace actual producer and consumer identities in both directions, then join
their provenance. It must not restate the conditional output reconstruction.

## Original scope, gates, and limits

The parent inference/evaluator theorem, original Simple-sub A/B claims,
quantifiers, accepted source domain and semantics remain unchanged and OPEN
0 → 0. The R45 finding is bounded to its pinned rules and does not establish
that no owner exists globally. The immutable-Name/Unit checked-result
constructor below is not presumed to apply to `loop y`; its audited scope is a
negative applicability boundary only.

This packet grants read-only source/native mapping and proof work. It grants no
Rust edits, tests, builds, Cargo, runtime probes, expected-output changes,
semantic adoption, production or parent-theorem promotion. Solver success,
endpoint equality, test output, matching names, or inferred free variables do
not establish an authentic source declaration or exact `D_q`. A proposed new
language rule, if needed, is a later separately reviewed and user-approved
gate; this packet does not draft or adopt one.

## Exact baseline and frozen dependencies

Baseline commit: `55ed588e7` (R45 research checkpoint is pushed). R45's
closeout and its bounded artifacts are direct dependencies. Source files below
are pinned to their current worktree bytes, including identified primary-owned
overlays; overlays are observations for this read-only map, not accepted
implementation behavior. Recompute hashes before accepting any result.

| Dependency | SHA-256 | Use |
|---|---|---|
| `notes/progress/2026-10-19-r45-closeout.md` | `6caf736e9d76ebc5c44080d0ad77a92b52b113703aa772c99315cb9a99dc8da5` | Prior bounded outcome and gate boundary |
| `notes/theory/2026-10-19-r45-contextual-output-core.md` | `d2982e9bd316f764c9e9709e5843062d5b02b7c5f6f5eea9231fe6a14dd10be0` | Core obstruction |
| `notes/theory/2026-10-19-r45-application-derivation.md` | `05530063f72b8df7f989d9c9483b05e56dc2591af9232cee1682900e524ce2c4` | Independent source/dependency attack |
| `notes/design/2026-10-16-source-application-checked-result.md` | `c9207625887d78aaccef988324e8505f6dd08fdfe076e0f564f8b7dca3c54076` | Existing constructor and exact applicability limit |
| `notes/theory/2026-10-16-first-call-checked-result-construction.md` | `89fb62b1fe9e10d6972a79f17399d4a0332cf57817bb06a07f5e054ecb4b9dfa` | Checked-result derivation |
| `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` | `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240` | Original Generalize formation and output telescope |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` | Typed result/effect judgments and consumers |
| `notes/theory/2026-10-07-call-input-construction-proof.md` | `f7c1b1eb23acb33ab98487097ab67617e1af84964b012874b1c951a8805dd9f6` | Code-Call input formation premises |
| `notes/theory/2026-10-08-call-source-interface-construction.md` | `278034197a90eab6e62a073545c09dd14415a0353f58aa3b3cc122a6af945d98` | Original Call source-interface construction |
| `notes/design/2026-10-02-source-computation-role-elaboration.md` | `9a230eb023698666f4c3e518a527009d6915e65f658b230e6da6a29914ca3abb` | Source-computation roles and endpoints |
| `crates/yu-hir/src/module/local_source.rs` | `ede8b845e1ad19bb1481d7e6337cefa1f117197512975f0f306dc6edb79672e5` | HIR source occurrence construction |
| `crates/yu-solver/src/candidate_source.rs` | `66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c` | `ApplySourceInput` source owner |
| `crates/yu-solver/src/candidate_call.rs` | `e038ad0dfc4b12bd0d513d6cd6b34cee6b2b062d8b33368bc1c0dcdef980d479` | Call observation and owner lineage |
| `crates/yu-solver/src/shadow_apply.rs` | `d5e6b179fd4f6fbca579b0fa4d479d8bd11b520d774acbf27f414451c4691137` | Native Apply ports; primary-owned overlay |
| `crates/yu-solver/src/candidate_context.rs` | `42f89dcf5fa6d7095db1e220c89308a2a35f4e74b05c3e8821d4fb2e3e32b0ca` | Context, dispatch, and typed consumers |
| `crates/yu-solver/src/lib.rs` | `2300400e87d0a487225f207d414ac71fa4f21c6f80279fea4f793e43c7809aee` | Module-level ownership and data flow |
| `crates/yu-solver/src/candidate_scheme.rs` | `8c370e47d5e8692a618fedf41be07d7ae3ac961f9070bfed6730e2b8e2f1137e` | Existing capture/copy owner path; primary-owned overlay |
| `crates/yu-solver/tests/candidate_local_self_recursion.rs` | `47ced76fe8f0f136c42802b2376ca09f7cadec0fc8e5b1b3d4c6acc7bc613e55` | Source fixture identity only; primary-owned overlay |

Do not infer new authority from the overlays or tests. The handoff must label
HEAD behavior separately from worktree-candidate behavior wherever they differ.

## Methods and exact output leases

### Luna — read-only source/native owner map

Follow the HIR occurrence forward through Apply source registration, operand and
result/effect fields, admission, native ports, typed Result/Preserve, Context
and Dispatch. Trace backward from the typed consumer to the owning source
occurrence and join only on authenticated occurrence/provenance identities.
Record the exact field maps and first missing owner, if any. Inspect the pinned
files above only; no mutation or verification command that writes generated
artifacts.

Exact paths:

- `notes/progress/2026-10-19-r46-source-native-owner-map.md`
- `tasks/agent-loop/inbox/20261019-r46-implementation.md`

### Sol — independent law instantiation and falsifier

Independently instantiate the existing source/formation laws at the pinned
`q = loop y` occurrence. Work backward from the typed Result demand and forward
from source registration; join operand identities, scopes, output/effect
records, result endpoints and `D_q` only through explicit premises. Return a
typed derivation or the first unsupported judgment and owning rule. Attack for
occurrence mismatch, missing/reordered dependencies, result/effect conflation,
unbacked provider/consumer fields, and reliance on solver success or a new
primitive. Do not self-certify or modify the primary lane's files.

Exact paths:

- `notes/theory/2026-10-19-r46-application-law-instantiation.md`
- `tasks/agent-loop/inbox/20261019-r46-proof.md`

### Fresh review after freeze

After both producer outputs and direct dependencies freeze, obtain independent
compiler and spec reviews. Review exact source bytes, law applicability,
occurrence/provenance joins, complete Call/effect/provider/pending/W/Z and
future/receiver/return obligations, exact `D_q`, two-frame/alias claim limits,
and honest parent status. Reviewers may not edit producer artifacts.

Exact paths:

- Compiler review: `notes/progress/2026-10-19-r46-compiler-review.md`
- Spec review: `notes/progress/2026-10-19-r46-spec-review.md`

Luna owns contract, compact state, shared task status, adjudication, closeout,
and all Git operations. All other exact output paths belong solely to the named
lane until an explicit completed-write handoff.

## Resource bound and stop conditions

Total ceiling 2400 seconds, no R45 carryover: Luna 600 read-only mapping; Sol
900 constructive/attack work; fresh compiler/spec reviews 300 each (600 total);
Luna integration 300. Record actual elapsed CPU/RSS only when observed. Astra
allocation is zero: the dispatcher found no specific mathematical risk that
requires it. No new workers may extend the budget or leases.

Stop at the fixed outcome, a source-qualified counterexample, the first
unsupported owner after the bounded bidirectional trace, a changed dependency,
authority or lease, budget exhaustion, or user STOP/session end. Keep the
parent OPEN absent a genuine proof/refutation and fresh proof review. Do not
repeat a conditional reconstruction. Any need for a new source rule returns
through its independent design review and explicit user-approval gate.

## Dispatcher decision and primary grant

Revision 2 adds the direct original formation-law pins after the proof lane
identified that summaries alone are insufficient to decide law applicability.
No claim was accepted from the R45 summaries in place of reading those exact
authorities. The 2026-10-19 boundary consultation proposed this source→Apply→native slice,
bidirectional occurrence join, Sol law-instantiation lane, read-only primary
map, fresh independent reviews and 2400-second ceiling. Luna adopts that
fixed outcome with the exact dependencies, worktree-overlay hashes, leases,
and no-code boundary above. The R45 residual 300 seconds are not carried over.
Primary grants these exact read-only/research leases only; parent and language
authority remain unchanged.
