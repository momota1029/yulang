# Formal permission projection r5: outer checkpoint correspondence

Status: FROZEN on submission; producer-authored, UNREVIEWED. Technical investigation STOPPED at the source-action caller boundary. The same-state outer checkpoint equation is established as qualified static source evidence. Universal r2 B, r2 C/D, the original endpoint-image obligation, full inference/executor soundness, source/native and production gates remain OPEN. No actual permission-projection counterexample was established.

## Objective, method and baseline

Trace the newly admitted `candidate_intrusion::State::{begin, rollback}` and connect it to the already admitted publication, route transaction and term-store owners. Method: bounded static source derivation, with frozen r2–r4 evidence; no main constructive theorem, executable checker or experiment. Apply the `yulang-proofs` source-premise distinction. The primary retains proof dispatch, review, authority and Git; no descendants were started.

Primary-supplied baseline: `3cc8a897fe08980576b1582952a95acab55f09d2`; not independently resolved using Git, which this packet forbids. Governing semantic sections remain annotation policy §§1, 1.1, 1.2 and 4, with §6's retracted result excluded. Composed polarity, source-local permission, actual inflow and residual remain distinct. No selected language meaning was reopened. R1's unchecked Lean repair remains unchecked.

All eight source/policy pins matched:

| Input | SHA-256 |
| --- | --- |
| `crates/yu-solver/src/candidate_intrusion.rs` | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` |
| `crates/yu-solver/src/candidate_effect.rs` | `70c42056a1041d54f88f16d7712875e3acf9ef7649b99a34bc990ff19f04936f` |
| `crates/yu-solver/src/candidate_scheme.rs` | `02349de1a2d69289eb348f7ff807a9e36faa2e2028cf61d10c1af9cd364409c5` |
| `crates/yu-solver/src/shadow_apply.rs` | `f8d92f2d59353e5b9cda014545b352c8d6356cc0aff3b4eeae0e81893e78202d` |
| `crates/yu-solver/src/lib.rs` | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` |
| `crates/yu-solver/src/term.rs` | `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1` |
| `tools/inference-playground/src/scheme.rs` | `82019fd22ad565c753461d8962934fcfe8e6663f8a7971b4fcbc5f5067026be0` |
| Annotation policy | `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18` |

Frozen input authentication also matched: r2 contract `34cd037c944d067b94b3ab89aadbf7cdeb2153bb3afcd48fbd2d497f58ef0877`; r2 handoff `f4a3ca3491d36e35e1d066aeafbe0e17f672e90014eeeb063b0cc6ca8a42b8d2`; r3 contract `f3f81eead20bf7f9229844894fa4e71ae2eb19d2a39acf14200f1f8bd452ee5e`; r3 handoff `104720837d86a40efafe1676bf23d756042ce78355d0bfc84c69918aa7676956`; r3 review `db0da175cd0ed87fa17806c7482cb0a7982fcad8b83a432536198d667d9a8a1d`; r4 contract `d158c2e14e44d6f6c5bc3e76af7a1ec94cf24c090ba266de9ad93ce958b0b1cc`; r4 handoff `92fc0eb406ad0b7b82801ed86c33723bdc9483aee997421563dac2d12154d8a7`; r4 review `1511ef47588a0b754743c812c7c77ef2b75c9dbe1b5d746bace031f9b8c7e757`.

## Exact local derivation

Assume ordinary Rust/std semantics, successful necessary allocations, an initialized candidate graph G present when the route begins, and no replacement of G or its active journal before publication/disposition. Assume this formal publication is executed inside the begun transaction, and no uninspected operation mutates/replaces its parameter-domain association. These route/lifecycle hypotheses are explicit; the first missing one is identified below.

1. `lib.rs:9271–9272` rejects a nested active route with `assert!(self.route_journal.is_none())`. The store route begins at `:9284–9286`. At `:9424`, the current G supplies `G.intrusion.begin()` directly into the new journal. `candidate_intrusion.rs:177–179` constructs `Undo { effect_algebra: self.effect_algebra.checkpoint(), ... }`. `Undo::effect_algebra` has the actual `candidate_effect::Checkpoint` type (`:66–67`). Thus, for this same G, `journal.intrusion.effect_algebra = checkpoint(G.intrusion.effect_algebra)` at begin, rather than an unrelated checkpoint inferred from field naming. The journal becomes active at `lib.rs:9477`; `with_route_transaction` begins before invoking the operation (`:9485–9486`, `:9503`).

2. The effect checkpoint saves permission length/accounting and starts an empty new-domain-key list (`candidate_effect.rs:313–335`). Formal annotation publication rejects a preexisting key (`:1638`), reserves storage including that active undo's domain list (`:1667–1671`), then appends permissions and inserts the exact constructed negative term under the parameter (`:1687–1690`). A new insertion pushes the parameter into this same active `route_journal.intrusion.effect_algebra.formal_domains` (`:1691`). The insertion and journal push have no intervening fallible source operation. Later resource sampling can fail (`:1696`), so the abort path matters after publication. Under the stated active-undo hypothesis the new key cannot be silently omitted from this list. The optional `if let Some` itself does not enforce that hypothesis.

3. Abort takes that journal (`lib.rs:9664–9667`), rolls back the store (`:9678`), then consumes `journal.intrusion` with the current G (`:9680–9681`). `candidate_intrusion.rs:201–202` passes precisely `undo.effect_algebra` to `self.effect_algebra.rollback`. The algebra removes each journaled domain key and truncates permissions to the saved length, restoring permission accounting (`candidate_effect.rs:338–342`). This discharges r4's first missing same-state checkpoint equation. It does not require a copy of every old domain value.

4. Store rollback reaches term rollback through `lib.rs:3558`; term rollback removes new interner keys/page-directory entries and truncates the old last page to its checkpoint length (`term.rs:803–821`). Intrusion rollback restores journaled forest parents, truncates newly born forest entries, and resets generation/occurrence state (`candidate_intrusion.rs:203–236`). Session rollback restores recorded preexisting row bounds/metadata and truncates newly born rows (`lib.rs:9740–9794`; the specifically inspected tail covers value restoration at `:9750–9760`, effect restoration at `:9764–9782`, and row truncation at `:9786–9794`). These are distinct owners of the row/term epoch.

5. The actual abort order is **term retirement first, new permission/domain removal second**, then remaining session-row restoration. This is not a claim that the association disappears before term retirement. In the inspected synchronous production bodies there is no intervening term allocation or capture/export call between store rollback and intrusion cleanup (`lib.rs:9678–9681`), and local algebra cleanup is infallible after its context rollback call. Therefore the local trace supplies no window in which a new allocation reuses the offset before this new association is removed. `state.refresh_bytes()?` can return early later (`:9702`), after permission/domain cleanup but before full session-row restoration. A theorem of complete restoration for every rollback error therefore needs additional error/disposal evidence; it is not established here.

6. Commit takes the active journal, drops its intrusion undo, then commits the store and returns the operation value (`lib.rs:9506–9532`). `ConstraintStore::commit_route` calls term commit (`:3518–3521`), whose body drops the journal without truncating nodes or interner entries (`term.rs:789–800`). No inspected commit statement erases formal permissions/domains. Under the same-state hypothesis, the originating new association and live terms therefore survive this commit.

Local conclusion: for this unchanged state and completed matching transaction, a newly published association is retained on commit and removed on abort; r3's same-page offset reuse cannot by itself recover that removed permission/domain pair. This is a conditional source derivation, not a machine-checked theorem or all-path r2-B closure.

## State identity, older associations and capture survival

`candidate_scheme.rs:2263–2285` constructs a fresh default GraphState, initializes its algebra brand, then assigns `self.candidate_graph = Some(state)`. It does not migrate old formal permissions/domains. The visible production initialization path is `lib.rs:10435–10440`, immediately after `Self::try_new`. Within the inspected owner-union searches, this is the only explicit candidate-graph assignment; the session graph is later moved into solved state at `lib.rs:20064`. This bounded search does not prove that callers outside the union never invoke initialization during an active route. Neither the checkpoint nor rollback authenticates G with an identity comparison: rollback uses the *current* option and skips absent state/undo (`lib.rs:9680–9681`). Replacing G during a route could therefore invalidate the derivation's same-state premise; no reachable such route was established.

Preexisting domains are not copied by checkpoint and are not removed unless their keys are journaled. The three visible producer insertions all reject existing parameter keys: record (`candidate_effect.rs:1576,1608–1609`), unit (`:1615,1626–1628`), annotated formal (`:1638,1690–1691`). Thus these inspected writers do not overwrite an older association; their successful insertions journal new keys when the outer undo exists. Older permission records survive truncation to the pre-route length. Terms already live at the term checkpoint are preserved by its prefix truncation. Consequently an already-valid old association survives this local rollback unchanged under the stated no-other-mutation assumptions. This does not reconstruct an old association's original provenance or prove canonicalization C.

Capture reads current domains into term-keyed negative formal roots (`candidate_scheme.rs:2787–2799`) and returns an owned graph after its final sample (`:2824–2827`). Definition capture stages member graphs, then stores them in `state.graphs[position]` (`:2892–2909,2929–2951`); another visible recapture writes graph slots at `:3850–3855`. Abort explicitly cleans local slots/routes and truncates candidate routes (`lib.rs:9687–9701`), but this inspected rollback passage does not restore definition graph slots. This is a coverage distinction, not a discovered bug: whether these publication sites can execute inside the failing transaction, whether captured artifacts escape such a transaction, and which artifact the successful export consumes require caller reachability. Retained capture artifacts do not by themselves establish a surviving stale permission/domain record. Frozen r2 supplies export owner/domain/root/path lookup and the first consumer; no new independent audit of those endpoints is claimed.

## First missing owner/equation and STOP

The universal active-undo and same-state requirement is still unproved: every reachable production call of `candidate_formal_annotation` must occur after begin has captured the current G, before its matching finish/abort, with neither candidate-state nor journal replacement and with failure disposing of captures that could escape. The publication body allows absent `route_journal` or absent `journal.intrusion` without rejection. No production caller of this function appears in the admitted union search; the matches there are definition and embedded-test calls. `execute_candidate_graph_plan` delegates source execution at `candidate_scheme.rs:2875` to `execute_candidate_source_root`, whose body is outside this packet.

The next proposed owner is `crates/yu-solver/src/candidate_source.rs`, specifically the source-action executor reaching formal annotation and its transaction wrapper/initialization lifecycle. Its actual contents and SHA-256 remain UNKNOWN: the file was not opened or hashed. Primary must confirm and pin that exact owner before inspection. Required equation: the formal-action dispatch is enclosed by the same G's begin/finish transaction, or an explicitly justified nontransactional lifetime/disposal path; capture publication cannot export a failed route's stale association. If that function delegates further, stop again at the first additional owner. No new owner was admitted here.

This is a precise caller-premise blocker, not another reuse probe. No minimized originating-construction → surviving stale association → successful wrong-image export witness was obtained. The r3 symbolic three-node offset-reuse witness remains only a hazard. Missing roots, stale lookup alone or a checkpoint equation are not counterexamples and do not close B, C or D.

## Commands, coverage and resources

Checks run: SHA-256 authentication for all eight owners/policy and eight frozen r2–r4 artifacts; bounded `rg -n`, `cat`, and `nl -ba ... | sed -n ...` reads; one shell heredoc writing only this leased note. Some broad outputs were truncated; the checkpoint, publication, commit, rollback, initialization, term epoch and selected capture passages were reread in bounded output. No exhaustive source-wide caller search was authorized or performed. Source investigation stopped at the missing caller owner.

Oracle independence: no Oracle or independent reference implementation ran. Shared assumptions are ordinary Rust/std behavior, pinned source and frozen r2–r4 evidence, plus the explicit route identity/lifetime hypotheses. No transition checker or experiment was authored. Seeds/ranges/mutations: none. No tests, probes, Cargo, Lean/Lake, network, Git, compiler edits, other outputs or descendants. No heavyweight process ran; one small command process at a time. Budget: 200 seconds, one CPU, 1 GiB RSS. CPU time, peak RSS and exact total elapsed time were not instrumented and are UNKNOWN. The clock observation during investigation was `2026-10-27 22:10:50 UTC`; it is not a start-time measurement.

Unverified: full caller reachability and active-undo presence; absence of candidate-state replacement outside the admitted union; complete rollback-error disposal/restoration; every capture publication/escape path; canonicalization/store association C; successful capture/export D; original source/native/executor correspondence; Lean verification. No theorem or production promotion follows.

Recommended next action: primary obtain fresh non-author `compiler_referee` review of this frozen note, then admit the exact source-action caller owner with a pinned hash to discharge or refute the active-undo/state-identity premise.

## Commit packet

- Exact leased path: `tasks/agent-loop/inbox/formal-permission-projection-20261028-source-r5.md`.
- Baseline SHA: `3cc8a897fe08980576b1582952a95acab55f09d2` (primary supplied).
- Dependency hashes changed: none observed; every checked pin matched. No final source rehash after STOP.
- Review status: UNREVIEWED, producer-authored; frozen upon submission. No independent review of this output claimed.
- Checks already run: dependency authentication and bounded static source inspection only; no executable checks.
- Proposed one-line research-checkpoint message: `research: derive same-state formal permission checkpoint correspondence`.
- Shared-record deltas intentionally left for primary/curator: record r4's local outer checkpoint equation as source-supported under unchanged-state transaction hypotheses; retain r2 B OPEN for production caller/active-undo/state identity and capture/error disposal; retain C/D separately; preserve r1 unchecked Lean blocker and all parent/native/production gates OPEN; record no actual projection counterexample; appoint fresh non-author review. No shared record changed.

STOP. Technical investigation and artifact writes ended before frozen submission.
