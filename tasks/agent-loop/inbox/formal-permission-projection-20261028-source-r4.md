# Formal permission projection r4: lifecycle owner boundary

Status: INCOMPLETE, FROZEN on submission, producer-authored and UNREVIEWED. Technical investigation STOPPED at the first unadmitted source owner. No successful permission-projection counterexample or unconditional r2-B theorem was established. The endpoint-image, parent theorem, native and production gates remain OPEN.

## Objective, method and pins

Trace r2 B: the owner-matching permission record, parameter domain and original term association across publication, checkpoint, commit/rollback, capture and export. Method: bounded static source inspection, consuming the frozen r2/r3 evidence and r3 independent review. No checker, executable experiment, language decision or main constructive theorem proof.

Primary-supplied baseline: `3cc8a897fe08980576b1582952a95acab55f09d2`; not independently resolved with Git, which was prohibited. R4 contract SHA-256: `d158c2e14e44d6f6c5bc3e76af7a1ec94cf24c090ba266de9ad93ce958b0b1cc`.

All admitted dependency hashes matched:

| Input | SHA-256 |
| --- | --- |
| `crates/yu-solver/src/candidate_effect.rs` | `70c42056a1041d54f88f16d7712875e3acf9ef7649b99a34bc990ff19f04936f` |
| `crates/yu-solver/src/candidate_scheme.rs` | `02349de1a2d69289eb348f7ff807a9e36faa2e2028cf61d10c1af9cd364409c5` |
| `crates/yu-solver/src/shadow_apply.rs` | `f8d92f2d59353e5b9cda014545b352c8d6356cc0aff3b4eeae0e81893e78202d` |
| `crates/yu-solver/src/lib.rs` | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` |
| `crates/yu-solver/src/term.rs` | `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1` |
| `tools/inference-playground/src/scheme.rs` | `82019fd22ad565c753461d8962934fcfe8e6663f8a7971b4fcbc5f5067026be0` |
| Annotation integration policy | `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18` |
| r2 contract | `34cd037c944d067b94b3ab89aadbf7cdeb2153bb3afcd48fbd2d497f58ef0877` |
| r2 handoff | `f4a3ca3491d36e35e1d066aeafbe0e17f672e90014eeeb063b0cc6ca8a42b8d2` |
| r3 contract | `f3f81eead20bf7f9229844894fa4e71ae2eb19d2a39acf14200f1f8bd452ee5e` |
| r3 handoff | `104720837d86a40efafe1676bf23d756042ce78355d0bfc84c69918aa7676956` |
| r3 independent review | `db0da175cd0ed87fa17806c7482cb0a7982fcad8b83a432536198d667d9a8a1d` |

The semantic authority remains the policy's §§1, 1.1, 1.2 and 4, with the withdrawn example in §6, as recorded in frozen r2. Composed polarity, local permission, actual inflow and residual remain distinct; no row equality is promoted to annotation authority. Required root/rule instructions were read; no scheduling or shared authority file was edited.

## First exact remaining premise and STOP boundary

The visible transaction delegates the decisive connection to a source owner outside the admitted union:

```
lib.rs:9424: journal.intrusion = candidate_graph.map(|state| state.intrusion.begin())
lib.rs:9681: state.intrusion.rollback(undo, &mut self.typed_pairs)
```

The missing owner is `candidate_intrusion::State::{begin, rollback}` and its `Undo::effect_algebra` field, declared through `mod candidate_intrusion` at `lib.rs:225`. The expected implementation owner is `crates/yu-solver/src/candidate_intrusion.rs`; that file was not opened or hashed. Its hash and actual implementation remain UNKNOWN in this packet.

The first missing equation is: the `undo.effect_algebra` consumed on this route's rollback must be the pre-publication `effect_algebra.checkpoint()` for the same state, and outer rollback must actually call `effect_algebra.rollback` with it while restoring the associated row/term epoch. The admitted callers expose delegation but do not establish that equation. A field name and a later successful lookup do not prove it. The contract requires stopping here; no new owner was added and no claim about the uninspected implementation follows.

## Lifecycle map supported by the inspected owners

| Boundary | Represented association and disposition | Qualification |
| --- | --- | --- |
| Construction | `FormalPermission` holds parameter, occurrence, source owner, scope, full path, source row and concrete operands (`candidate_effect.rs:237–245`). Frozen r2 identifies the single fresh effect port supplied to both term signs; r3 proves exact immediate read-back. | The permission does not itself retain the original port or term certificate. R3 equations require live terms in the same branch. |
| Publication | Existing parameter-domain keys are rejected before construction (`:1638`). After building the pair and linking both parameter edges (`:1658–1677`), permission records are drained into state, and `formal_domains[parameter]` receives this pair's negative term (`:1687–1691`). | This inspected producer rejects replacement of an existing key. It is not an audit of every possible writer or state replacement. |
| Journal insertion | On insertion of a new key, the active `journal.intrusion`, when present, records that parameter in `undo.effect_algebra.formal_domains` (`:1690–1691`); reservation occurs at `:1671`. | Absence of the relevant outer undo is not rejected by these optional branches. The actual route-to-undo invariant is the missing premise above. |
| Local checkpoint | `State::checkpoint` saves the current permission length and byte accounting and initializes an empty added-domain-key journal (`:313–335`). | It does not copy domain values. Correct rollback depends on the no-replacement discipline and journaling of every new key. |
| Local rollback | `State::rollback` removes the journaled domain keys, truncates permission records to the saved length and restores permission byte accounting (`:338–342`). | Given the correct checkpoint, newly published domain/permission associations are removed together; older unmodified associations remain. Outer invocation is unproved here. |
| Route success/commit | `finish_route_transaction_with_candidate_accounting` takes the successful operation result, commits context replay bookkeeping, drops `journal.intrusion`, then calls `store.commit_route` and returns the value (`lib.rs:9501–9533`). | This visible branch retains the published algebra data. The frozen r3 term result supports commit preserving term nodes; no proof of all other state owners is inferred. |
| Route failure/rollback | Operation error invokes `rollback_route_transaction` (`lib.rs:9535–9547`). That function first calls `store.rollback_route`, then delegates intrusion rollback (`:9678–9681`). | Store retirement and algebra cleanup have distinct owners. R3 establishes term retirement/offset reuse, but the outer algebra checkpoint connection is uninspected. |
| Capture | Frozen r2 and admitted search locations identify current `formal_domains` values as the inputs to `negative_formal_roots`: only lookup-valid negative Function/Tuple terms already present in capture endpoints receive retained roots (`candidate_scheme.rs:2787–2799`). | A retained root is keyed by `Term`, not the original annotation occurrence. Capture alone does not authenticate the provenance of that term after rollback/replacement. Missing roots produce unavailability at export. |
| Export | Owner filtering uses `SourceRootId::Definition(root) == self.source_root`; each matching permission then selects the current domain by parameter and exact retained root by that term (`shadow_apply.rs:2643–2652`). Its original path walks graph children and returns the terminal Effect row node while borrowing the original occurrence/source row/concrete operands (`:2653–2693`). | The lookup/path/shape/kind checks validate the present graph route. They do not independently certify that a stale domain still denotes the originating construction. Scope is retained metadata, not an additional export association check in this body. |
| First consumer | Frozen r2 traces playground projection to the exact returned graph handle and Effect row (`scheme.rs:185–196`). | This is successful graph projection conditional on the previous associations; it adds no annotation provenance certificate or permission activation. |

The `RouteCheckpoint` found at `lib.rs:8561` has a test-only capture implementation (`:8641` onward in the inspected output); it was not used as production rollback evidence. The actual route mechanism above is the mutation journal, not that snapshot helper.

## Conditional derivation and falsification limit

Local claim class: conditional source derivation. Assume ordinary Rust/std semantics and successful required allocations; a pre-publication checkpoint `c = algebra.checkpoint()`; a new parameter key absent before construction; every newly published key recorded in `c.formal_domains`; no intervening replacement or removal of older associations; and actual invocation of `algebra.rollback(c)` on failure. Then publication appends this construction's permissions and associates its exact negative term with the parameter. Rollback removes that new key and truncates the appended records. Therefore this newly rolled-back association cannot subsequently be selected by `formal_effect_permissions` from that algebra state, even if the retired term's brand/index is later reused. If the key/record are absent, export cannot recover them merely through a successful term lookup.

The removal/truncation conclusion follows directly from `candidate_effect.rs:340–342`; the missing outer checkpoint equation remains an explicit hypothesis, not a proved source rule. This is neither a whole-lifecycle theorem nor a checker assuming its own transitions. An older association survives the local rollback only as its unchanged stored values; that statement does not prove its original term/row epoch survives every external operation.

For a successful, unrolled-back construction, r3's read-back laws apply while its term nodes remain live. Composing those laws with frozen r2's path trace still requires B's outer lifecycle equation, C's canonicalization/store association and D's successful capture/export. R4 does not discharge B universally or merge B with C/D.

No minimized successful projection witness was obtained. R3's three-node, one-rollback same-page reuse trace remains a hazard only: it does not establish survival of a permission/domain association, capture of the replacement endpoint, or successful export with different original provenance. The visible local cleanup provides a reason that such survival must be proved rather than assumed. Conversely, absence of a witness in this bounded inspection is not an absence theorem.

## Commands, coverage and resources

Commands run: `sha256sum` for all seven admitted owners and five frozen r2/r3 inputs plus the r4 contract; bounded `rg -n`, `cat`, `sed -n`, and `nl -ba ... | sed -n ...` source/document reads; one `apply_patch` creating this exact leased handoff. All checked hashes matched. Some early combined output was truncated; the local publication/checkpoint/rollback and transaction error/commit passages used above were subsequently obtained in bounded outputs. Frozen r2 supplied the earlier capture/consumer derivation; it was not presented as a newly independent audit. Technical source search stopped on the missing intrusion owner.

Oracle independence: no Oracle or separate implementation ran. Shared assumptions are the frozen source evidence, ordinary Rust/std behavior and the explicit lifecycle hypotheses. No transition checker was authored. Seeds/ranges/mutations: none. No tests, probes, Cargo, Lean/Lake, network, Git commands, descendants, compiler edits or runtime-path reads/writes. Only this Markdown path changed; shared records were left to the primary.

Coverage is partial static lifecycle evidence from the admitted union, not exhaustive caller/state-replacement analysis. Unverified: the missing outer undo equation and row epoch restoration; capture artifact publication/disposal across every rollback; other mutation owners; complete canonicalization/store association; original source/native and executor correspondence; Lean verification. CPU time and peak RSS are UNKNOWN, not instrumented. No heavyweight process ran. The first clock observation was `2026-10-27 22:06:03 UTC`; the packet budget was 200 seconds, one CPU and 1 GiB RSS. Final elapsed time is reported separately with the frozen handoff hash.

Recommended next action: primary admit the exact `candidate_intrusion::State::{begin, rollback}` / `Undo::effect_algebra` owner with its pinned hash to establish or refute the outer checkpoint equation, after fresh non-author review of this frozen result; keep all theorem/native/production gates OPEN.

## Commit packet

- Exact leased path: `tasks/agent-loop/inbox/formal-permission-projection-20261028-source-r4.md`.
- Baseline SHA: `3cc8a897fe08980576b1582952a95acab55f09d2` (primary-supplied).
- Dependency hashes changed: none observed; all admitted hashes matched at inspection. No final source rehash after STOP.
- Review status: UNREVIEWED, producer-authored; frozen on submission. No independent review of this artifact claimed.
- Checks already run: admitted dependency/contract SHA-256 checks and bounded static inspection only; no executable checks.
- Proposed one-line message: `research: record permission lifecycle checkpoint owner boundary`.
- Shared-record deltas intentionally left for primary/curator: record r4 as INCOMPLETE conditional local rollback evidence; preserve r2 B as OPEN with the exact outer intrusion checkpoint equation; retain r2 C/D separately and the r3 validity window; record no projection counterexample; assign a fresh non-author `compiler_referee` before any new Lean bridge or promotion. No shared record edited.

STOP. No further technical investigation or artifact writes after freeze.
