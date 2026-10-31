# R113 existing Rust delta classification — revision 1

## Assignment and frozen comparison

- Sprint/contract: `EFFECT-PERMISSION-EXISTING-RUST-DIFF/20261101-R113`, contract SHA-256 `a52bfb6a5e9d6e92dd5543214ff6b442ecc8e70e09e2be6daa1662385fba71f4`.
- Assignment: R113 bounded read-only Rust delta classification; this file is the sole write lease. Revision 2 supersedes the factual classifications below where explicitly corrected. Revision 1 is frozen by SHA-256 `bcd5209e98e439b1dc7cbe4506817f04eabb7aa7525db68ba64d9e14dfa04df6` and is not rewritten in the history record.
- Parent: original Simple-sub/effect-hygiene claims, source/native correspondence, soundness, A/B, principality, termination and production remain OPEN.
- Baseline: current `HEAD` `b0f8b3be4fd745b358f63152ac42675e30ac1d75`. The six committed source blobs match the R111 baseline hashes from `d177c46ec61fcadd70a3d587c2f8934f6bc91f46` exactly.
- Requested/observed model and effort: UNKNOWN in this worker view. Worker identity: `/root/r113_impl`; current session `EFFECT-PERMISSION-EXISTING-RUST-DIFF/20261101-R113`. Actual active seconds were not instrumented; no resource measurement is claimed. No descendants.
- Outcome: **NO_SAFE_CODE_SLICE for Rust source integration or push under this packet.** Exact R111 compile candidate boundary is identified below; its compile gate remains closed.

## Frozen file and diff hashes

Complete live working-tree SHA-256 and `git diff HEAD` counts:

| Path | Working-tree SHA-256 | Diff (+ / −) | Unified diff SHA-256 |
|---|---|---:|---|
| `crates/yu-solver/src/lib.rs` | `429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be` | 28 / 5 | `4c20fd6bc23a4c7279253107b1fcd12703fcfcdf431b4850a9c6e69efc7d0bb9` |
| `crates/yu-solver/src/candidate_receiver.rs` | `3ec1a45f5cdcfa5f5f28c2ef433c37d03322150a3155228f898e6fc5b77725cf` | 4 / 7 | `a593c08bd5eed061b11fd4b8771e33dbf004fcc2202c9d732cb0998f3f4293ee` |
| `crates/yu-solver/src/candidate_effect.rs` | `4becefc07b81c1b298cafa190a3698e9e15e94656e1f17390eee13435dcb9b15` | 1,144 / 36 | `5275963ce1a8f9edaa07dd9768592aebf2427c7040e6a04ea5f9dfd8a4a9546c` |
| `crates/yu-solver/src/candidate_scheme.rs` | `4494ba879a05f90767779e12c9ca8e1364f2203f2f60eb63239a544c0d0da470` | 128 / 9 | `e9e167fccedc610ad50b046573ff14ade4b9584ea8f6ad95b58b24206a91a499` |
| `crates/yu-solver/src/candidate_source.rs` | `bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49` | 12 / 0 | `2c08cb9e1dd071986d7c3c887d1ad2205d79b34439ffaf261e6d495b5262bf50` |
| `crates/yu-solver/src/shadow_apply.rs` | `caeb837cd13b2e75e76fbed59dcc601e8c9d0a6a6a6f56f6959c0b0b9a98007f` | 9 / 0 | `4efbf71ca94041295b157e4b346514d1f359424d51d6840d23ecbb16b7704f27` |

Diff hashes are SHA-256 of `git diff --no-ext-diff --no-color --unified=3 HEAD -- <path>`. Aggregate: 1,325 insertions, 57 deletions. Candidate-scheme is read-only/FROZEN and Luna-owned. The source bytes and hunks are frozen by the hashes and locators in this handoff; any later byte change invalidates this classification.

## Delta classification and exact hunks

### R111-reviewed repair bytes

R111's independent reconstruction/review covers only these exact hunks:

- `lib.rs:11763,11770`: replace two `exhausted()` conversions with `SolveAvailabilityError::IdentityExhausted` in the registered formal entry path.
- `lib.rs:18372`: use the in-scope `SourceRootId::Definition` variant.
- `candidate_receiver.rs:4186,4385,4628`: dereference borrowed occurrence IDs for comparisons.
- `candidate_receiver.rs:4433`: use existing `HirModule::owns_source_root` so the existing Definition/Expression checks and Member ownership branch are honored.
- `candidate_effect.rs:3`: add the `candidate_scheme::RowKey` import.

The receiver working-tree hash exactly equals R111's reviewed four-repair target `3ec1a45f…`. The R111 `lib.rs` target is `6eb6b5df…`; current `lib.rs` does not match it because of additional instrumentation. R111's permitted `candidate_effect.rs` target is baseline plus only the import, `102d0c78…`; current `candidate_effect.rs` contains a further 1,143 additions and 36 deletions. Thus only the receiver file is byte-for-byte the full R111 target. R111 did not approve any of the additional hunks.

### Additional and previously recorded deltas

- `lib.rs:13812,13822,16654` adds test-only trace logging around live effect constraints, candidate effect propagation and diagnostic insertion. `lib.rs:18372` above is the separate R111 repair. No execution evidence comes from these logs.
- `candidate_effect.rs` is the R109/R110 unrecovered live candidate (`4becefc0…`, 1,144 additions/36 deletions versus the committed R107 blob). The current delta includes R104/R106-era test tracing and tests. The outer `FormalEntryPermission`/`FormalEntryPermissionUse` types, `State::bind_formal_entry_permission_use`, and `candidate_formal_entry_annotation` already exist in committed HEAD; they are baseline behavior, not R113 additions. Exact pre-R106 attribution for the live delta was not recovered; R109/R110 prohibit guessing reverse edits. R104's Rust final invocation had 47 passing and 4 protected test failures; the source candidate was explicitly left unintegrated.
- In that added test region, one old unconditional equality assertion was rewritten as an `if use_unequal_fixture` branch: the legacy fixture still requires equality, while the added falsifier requires inequality. This is a test-expectation/assertion delta, despite preserving the named legacy branch. Do not treat it as an accepted repair or include it in an implementation checkpoint. No golden/snapshot/diagnostic fixture edit was found in the six-file diff; this assertion change remains a protected-test concern.
- `candidate_scheme.rs:434–535` adds an explicitly partial adapter: it extracts one native Lambda argument-effect incidence from a retained module `FreshRoute` and calls `bind_formal_entry_permission_use`. Comments and `allow(dead_code)` state that it does not store a consumer or change constraints/inference; provider and Catch consumption remain open. The helper has no call site in the six inspected files. This file is FROZEN/Luna-owned, so it supplies read-only evidence only.
- Other `candidate_scheme.rs` changes thread `entry_effect` through captured/fresh incidence data and add test-only trace events and capture IDs. `candidate_source.rs:2453–2466` adds only test-only before/after action logs. `shadow_apply.rs:2703–2708` adds test-only export logging, with two test fixture initializers for new trace fields. These do not by themselves establish a consumer or execution behavior.

The committed-HEAD producer is `candidate_formal_annotation` and its recursive negative concrete-effect-port handling. It retains source owner, occurrence, parameter, annotation position, path, source row and concrete effects, and admits two Value links before retaining the formal domain/permissions. R112's immutable-source handoff establishes that this `FormalPermission` is local annotation permission only: it carries no incoming description-frame key, actual-event key/telescope, Shared witness or joint strategy. HEAD also already contains the separate outer entry-permission producer/type and `State::bind_formal_entry_permission_use` lookup, which matches a unique registration/owner/scope/occurrence/entry effect and nonempty concrete payload. Those existing APIs bind evidence only; they are not R113 delta.

The R113 delta adds `entry_effect` to candidate-scheme incidence/capture records and the unused `candidate_scheme::extract_native_lambda_argument_effect_incidence` → `bind_native_formal_entry_permission_use` adapter, which calls the preexisting `candidate_effect::State::bind_formal_entry_permission_use`. It checks exact retained graph node/row maps, native positive Function argument effect, registration/Lambda/use/context identities and source permission fields. It is read-only and does not generate a bound, feed `constrain_live`, establish propagation, or reach a provider/Catch/evaluator consumer. Existing candidate source scheduling and `candidate_apply_effect` are present in the source, but these added adapter/logs do not demonstrate a route from this source permission through those stages to execution.

### Exact R111 boundary and disposition

The only coherent compile-repair candidate remains the exact three-file R111 candidate: `lib.rs` target `6eb6b5df…`, `candidate_receiver.rs` target `3ec1a45f…`, and committed-baseline `candidate_effect.rs` with only the `RowKey` import target `102d0c78…`. It excludes the other 1,143 effect additions/36 deletions and all instrumentation/assertion changes. R111's final outcome says the independent review passed source reconstruction, but compilation remains blocked solely by the unenforceable hard aggregate storage/isolation cap and absence of a configured remote verifier; Cargo allowance remains 0/1. Therefore this is a candidate for that gate, not a source commit boundary authorized now. Do not stage Rust source from R113.

## Source/native correspondence, expectations, and unresolved premises

Parent/source relation remains conditional and incomplete. R112's actual producer trace is immutable-baseline evidence, not evidence that the dirty entry adapter closes its missing law. R112 identifies the first missing premise as source-owned payload normalization/admission and derivation transport at original App/Lambda telescopes, preserving selected descriptors/interfaces, actual operands, checking evidence, Shared correlation and one lawful strategy. No R113 hunk establishes that law.

The trace instrumentation is a **provisional source-evidence instrument only**. Its falsifier must preserve the actual source row/path and entry/arrival/effect correlation while distinguishing a missing producer payload from loss at propagation, fresh-use remapping, or the provider/Catch consumer. R104's four protected failures and its failed final gate are contrary evidence to treating the current tests as closure. Cleanup owner: Luna, after independent adjudication of whether any instrument remains useful; no production cutover follows from green tests or this handoff.

No semantic choice, source domain, diagnostic, expected-output fixture or original quantifier is approved to change here. The R104 assertion rewrite described above must be excluded from any compile candidate or separately adjudicated under the existing protected-test contract. The A/B premise and source/native/production gates remain OPEN.

## Evidence, limits, and handoff

Prior evidence reused: R111 handoff/outcome for exact patch hashes and closed compile gate; R112 source correspondence for the actual nested permission producer, consumer boundary and missing admission/transport law; R104 outcome for four failing protected tests and rejected source promotion; R107–R110 outcomes for baseline reconstruction and the explicitly unrecovered `candidate_effect.rs` provenance. Rejected: treating the full live effect file as the R111 baseline-derived candidate; treating R104's passing tests or logs as a theorem; treating the dead-code binding adapter as connected propagation/execution; treating any withdrawn Simple-sub bypass as reusable.

Read-only checks: exact `HEAD`; six complete working-tree hashes; six `HEAD` blob hashes; six path-specific diffs/counts/diff hashes; scoped source reads and prior-record hash reads. No Cargo/build/compiler/test/cache/worktree/environment command, Git mutation, source write, expected-output edit, or read of runtime `machine.rs`/`receiving.rs`, quarantined or isolated source. Source coverage is static and bounded to the six leased files and the cited R111/R112/R104–R110 records; no run or theorem is claimed.

- Exact changed path: `tasks/agent-loop/inbox/effect-permission-existing-rust-diff-r113.md` only.
- Known scratch/generated paths: none.
- Worker cessation: writes stop with this frozen revision. This packet did not observe a separate runtime cessation receipt for other historical authors; no live dirty-source authorship or cessation is inferred from blame-free working-tree bytes.
- Next related in-envelope step: none. Luna may send this frozen diff classification for the contract's fresh independent compiler-referee review. Any source compilation/integration still requires the unchanged R111 gate and primary-controlled authorization.
- Mutual TODO `R112-SOURCE-ADMISSION-TRANSPORT-1` (original R112 parent; source owner Luna/source-proof intake): first missing evidence is a source-derived admission/transport law from the actual App/Lambda constructor and full event telescope to selected descriptor/interface, checking evidence, once-Shared correlation and a lawful joint strategy. Inputs: original App/Lambda source derivations and the actual source-owned producer/consumer; output: a reviewed constructor-to-payload/transport correspondence, or an exact obstruction at the owning source rule. Falsifier: a supported source case whose arbitrary admission fails to preserve descriptor/interface or consumer evidence at the original telescope. This repeats R112's stable TODO and does not assign a write lease.

Writes stopped after revision 2. No self-certification is claimed.

## Revision 2 correction and freeze

This sequential revision corrects the baseline-versus-delta attribution identified in independent review. In committed HEAD, `FormalEntryPermission`, `FormalEntryPermissionUse`, `State::bind_formal_entry_permission_use`, and `candidate_formal_entry_annotation` are preexisting. R113 adds the candidate-scheme `entry_effect` threading and native-incidence/binding adapter; it does not add those effect-state producer/lookup APIs. All diff hashes, NO_SAFE_CODE_SLICE disposition, protected-assertion finding, source-closure limits, and gates above remain unchanged. Revision 2 is frozen at the hash reported after this edit; no further writes are authorized.
