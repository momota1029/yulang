# Formal permission projection r8-r2: forest inventory and interference boundary

Status: FROZEN revision 1 on submission; producer-authored, NOT_REVIEWED.
Outcome class: incomplete static source evidence with conditional local lemmas.
No reachable counterexample or source preservation theorem is claimed. STOP at
an unsupported source equation, before opening another owner.

## Assignment and authentication

Actual assignment/session identity: `/root/formal_permission_projection_source_r8_r2`,
observed in runtime NEW_TASK delivery. ACK and active-work receipt sent to the
primary at startup. Active work first clocked at 2026-10-27 22:36:23 UTC;
model/effort UNKNOWN. Sole author is this session, with no descendants.
Primary-pinned baseline: `3cc8a897fe08980576b1582952a95acab55f09d2`;
no Git command independently resolved it.

Effective authority is the sequential contract pair, not a replacement of r8:

| Authenticated input | SHA-256 |
| --- | --- |
| `tasks/agent-loop/sprints/formal-permission-projection-20261028-r8.md` | `99835a8d22b3b61c90500706245fd5e28aeee238905cca1eb217d8c2f274cd46` |
| `tasks/agent-loop/sprints/formal-permission-projection-20261028-r8-addendum-01.md` | `3c2782ff6e375b4f22278ead3d7f5834b4d2d291f83ab6b9b7b68624c2b040d1` |
| `tasks/agent-loop/inbox/formal-permission-projection-20261028-source-r8.md` | `e9926aaf56c8ea35b1227b7c27693f7c14eb872a46b8b6826ca6cda46951a4c8` |
| `tasks/agent-loop/history/formal-permission-projection-20261028-r7-outcome.md` | `7fab9c3f7bbe4c6072702b30973e44c705122aa244877addd1ff4d2a9a65eef8` |
| `tasks/agent-loop/sprints/formal-permission-projection-20261028-r7.md` | `40035df185bb2266f395264a137babf9b433e875922ff86f453836fba278a767` |
| `tasks/agent-loop/inbox/formal-permission-projection-20261028-source-r7.md` | `98cf92059d11ea1efd875c7af9d84c86be236f9c52b7b07acadfcac082c8b79d` |
| `tasks/agent-loop/inbox/formal-permission-projection-20261028-review-r7.md` | `635e94a1eec04348fdd87b7c1802101bca10a6fa8631e3e82d0eb39f26a12c7c` |
| `crates/yu-solver/src/candidate_source.rs` | `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` |
| `crates/yu-solver/src/candidate_effect.rs` | `70c42056a1041d54f88f16d7712875e3acf9ef7649b99a34bc990ff19f04936f` |
| `crates/yu-solver/src/candidate_scheme.rs` | `02349de1a2d69289eb348f7ff807a9e36faa2e2028cf61d10c1af9cd364409c5` |
| `crates/yu-solver/src/shadow_apply.rs` | `f8d92f2d59353e5b9cda014545b352c8d6356cc0aff3b4eeae0e81893e78202d` |
| `crates/yu-solver/src/lib.rs` | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` |
| `crates/yu-solver/src/term.rs` | `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1` |
| `tools/inference-playground/src/scheme.rs` | `82019fd22ad565c753461d8962934fcfe8e6663f8a7971b4fcbc5f5067026be0` |
| `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` | `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18` |

All listed hashes MATCH; none changed by this worker. The amended outcome pin
authenticates successfully. The review pin was checked before source-body
analysis; a preliminary source locator search had already occurred.
The prior r8 STOP and its full 200-second charge are preserved.

Read repository/root/base instructions, research/design/Git rules, current state,
README and sprint child-scope instructions. Applied `yulang-proofs`' separation
of conditional derivation and actual source correspondence; no prover or child
was launched. Governing selected meaning remains annotation policy §§1, 1.1,
1.2 and 4, with §6 retracted, and inference principles §§4–5. No semantic
reinterpretation or new rollback requirement follows from this audit.

## Local production writer inventory

`candidate_intrusion.rs:12–13` declares private `values: Vec<u32>` and
`effects: Vec<u32>`. Searching every occurrence of these fields in that module
gives the following complete local production content-write inventory.
The cfg(test) event/snapshot code is excluded from production reasoning.

| Operation | Actual write and location | Qualification |
| --- | --- | --- |
| Initialization | `State` derives Default (`:9`); empty vectors | `GraphState` derives Default (`candidate_scheme.rs:5`); `start_candidate_graph` creates it and installs `Some(state)` at `:2264–2285` |
| Births | `retain_extrusion_parent`, `:342–352`: append each checked `u32` ordinal as its own parent | Extends to current `bounds.len()` / `effect_bounds.len()` only when this method runs; no universal dense coverage or row-lifetime conclusion |
| Value merge | `merge_candidate_rows`, `:691`: `values[from] = to as u32` | Roots selected at `:613–619`; intervening calls require inspection |
| Effect merge | Same method, `:679`: `effects[from] = to as u32` | Same qualification |
| Compression | `compress_candidate_forests`, `:536–565`: mutable selected vector, `forest[row] = root` | Representative root computed before each path rewrite; old value recorded before write if intrusion Undo exists |
| Restoration | `State::rollback`, `:203–215`: reverse `undo.forests`, assign recorded parent | Depends on actual journal completeness, ordering and checkpoint association |
| Truncation | Same rollback, `:222–223`: truncate to saved lengths | Only after restoration; safety requires restored prefix has no dangling links into removed suffix |

`try_reserve` changes capacity without changing the parent function. `begin`
(`:177–200`) records lengths and an empty inverse-write log. `value_rep`,
`effect_rep`, `rep` (`:165–175`) read the selected forest, preserving the
RowKey kind. `representative` (`:119–127`) is read-only and performs no implicit
compression. Test snapshots copy vectors and add no production writer.

This is an inventory of local content-write sites, not a certification of all
transitive callers, whole-State replacements or valid invocation lifetimes.
The admitted code also installs/moves larger graph/session state; privacy of
the two vector fields alone does not prove every caller preserves provenance.

## Conditional derivation from those writes

Define a **closed finite forest** F of length n: every stored parent is below
n; every parent chain reaches a self-parent; n is representable by the indices
used by the loops. This is a candidate induction invariant, not an established
global source fact. Apply it separately to Value and Effect; RowKey dispatch
does not cross their storage.

1. Empty vectors satisfy it. Appending a fresh checked ordinal i with
   F(i)=i preserves it: old chains remain in the old prefix, the new chain has
   length zero. Repeating gives the actual birth-loop local preservation law.
   This establishes neither that every live row has already been appended nor
   that an ordinal still denotes the originating row after rollback/reuse.
2. In such a forest, lookup of an in-range row terminates along a finite chain
   at its unique self-parent. An out-of-range query immediately exits the
   `get` loop and returns that same ordinal. Therefore lookup is idempotent
   on every u32 query under this invariant. The missing-entry fallback supplies
   termination and syntactic idempotence, not proof of a valid live row.
3. If distinct in-range roots r and s remain self-roots immediately before
   F(r):=s, the write preserves the forest: r's class now ends at s; s's class
   previously had no path to r because s was a distinct root. Other classes
   retain their roots. This is the required merge lemma. Same-kind matching
   is explicit in `:619–623`. Root selection alone does not discharge the
   immediate-before-write hypothesis.
4. Compression computes a root r then replaces edges on its existing path by
   edges to r. Every replacement shortens that path and preserves its root;
   the walk through saved old parents terminates. Other classes are unchanged.
   This proves the local compression law under the closed-forest premise,
   with representable indices. It is not a proof that the premise always holds
   when compression is invoked.
5. A complete correctly ordered inverse log, replayed in reverse on its own
   checkpoint descendant state, reconstructs the checkpoint prefix. Because
   that prefix was closed, truncating appended births then preserves closure.
   Actual rollback has exactly this reverse-write-then-truncate form. However,
   this packet does not establish that every effective mutation is represented
   in the correct temporal order, or that a checkpoint remains paired with
   its original forest. Consequently this is conditional rollback evidence.

Stable canonicalization during r7's immutable capture follows if its source
forest premise holds; these lemmas do not establish that premise on all reachable
successful sessions. In particular, no equality of representatives creates an
annotation permission or identifies an originating occurrence.

## Exact unsupported equation and STOP

Merge selects `copy=state.rep(copy)` and `parent=state.rep(parent)` at
`candidate_intrusion.rs:613–614`. It saves a prospective inverse entry at
`:624–630`, then journals the destination bounds at `:631–635`. Before its
actual forest write it calls, among others:

- `candidate_opposite_count` at `:639`;
- `candidate_opposite_bound` at `:648`;
- `candidate_insert_copied_bound` at `:657`;
- `candidate_transfer_bound_origins` at `:660`;
- for Effect, `candidate_splice_capture_incidence` at `:668`.

The first three method declarations/bodies are absent from all eight admitted
source files. The exact static search was restricted to the original admitted
union; its matches for those names were only these callsites (and the later
count/read calls at `:700–702`). Their receiver signatures are also unobserved.
Thus their names cannot establish purity, lack of reentrant merging, absence
of graph replacement, preserved row coverage, or preserved journal order.

The first unresolved direct body on the visible bound-copy path is therefore
`candidate_opposite_count` at `candidate_intrusion.rs:639`. The decisive missing
interval equation is:

    If merge selected distinct roots r,s from F at :613–619, then immediately
    before :679/:691 both entries still exist, F(r)=r and F(s)=s; all effective
    intervening forest writes, if any, have correctly ordered inverse entries.

The stronger sufficient equation that this interval leaves both forests
unchanged is also unproved. `&mut self` at the enclosing merge does not make
this interval atomic against its own helper calls. A prospective inverse
entry recorded before helpers particularly requires ordering evidence if a
helper can itself write a forest.

The admitted journal row bodies are in `lib.rs:9548,9597`; rollback invokes
the intrusion Undo in `lib.rs:9681`. Those locators do not supply the missing
helper bodies. The admitted effect metadata methods at
`candidate_effect.rs:651,685` do not resolve the preceding unknown calls;
the latter additionally calls context transport whose full effect contract
has not been established here.

No additional source owner was opened or searched. The exact declaration-owner
path for the first missing method is UNRESOLVED within the permitted union;
guessing a module filename would not authenticate ownership. This report pins
the exact known caller path and equation for primary owner resolution. Semantic
investigation stopped at this boundary; no second equivalent toy probe was run.

## Application, checks and limits

Applied to r7: no reachable-session forest premise is removed. R7's conditional
C derivation remains usable under its existing forest, B and D premises; local
birth/link/compression/rollback lemmas identify the source equation still needed
to lift it. B's transitive construction/parameter/domain/store/export association,
D's successful capture/export, r1 Lean verification, original parent A/B,
source/native, full inference/executor and production gates all remain OPEN.

There is no minimized source witness: no reachable cycle, successful invalid
association or successful wrong-image export was established. A synthetic cycle
would not satisfy this contract's reachability and capture requirements. Source
acceptance, row lifetime, complete journal ownership and transitive helper
coverage remain unverified.

Commands/results: read-only `cat`, `sed`, targeted `rg`/`rg --files`, `sha256sum`
and clock calls; all required dependency hashes MATCH. One `apply_patch` writes
this exact note, followed by output hashing. No checker, tests, probes, builds,
Rust edits, Cargo, Lean/Lake, network, Git, descendants or quarantined paths.
No executable oracle, seeds/ranges or mutations apply. The derivation shares
ordinary Rust/std semantics with the inspected implementation and is not an
independently checked proof. Hash equality authenticates bytes only.

Resource limit: separate fresh grant of 200 seconds, one CPU, 1 GiB; deadline
22:39:43 UTC from first recorded active-work clock. Only short sequential shell
reads/hashes ran; peak RSS and total CPU are UNKNOWN, so charge the full
200-second grant. This does not reset the previous r8 charge. Stop/writes-ceased
receipt and frozen byte hash are returned to primary after creation.

Recommended next action: primary resolves the actual declaration owner of
`candidate_opposite_count` / `candidate_insert_copied_bound`, then adjudicates
whether to admit the minimum dependency needed to prove the interval equation.
This is a proposed authority change, not permission to open it in this packet.

## Commit packet

- Exact leased/changed path: `tasks/agent-loop/inbox/formal-permission-projection-20261028-source-r8-r2.md` only.
- Baseline SHA: `3cc8a897fe08980576b1582952a95acab55f09d2` (primary pin).
- Changed dependency hashes: none; authenticated dependency table above.
- Review status: NOT_REVIEWED; frozen producer evidence, no closure claim.
- Checks already run: required byte authentication PASS; local field/write inventory and admitted-union method locator searches; no executable verification.
- Proposed commit message: `research: identify formal permission forest merge interference boundary`.
- Shared-record deltas left for primary/curator: record STOP and full fresh-grant charge; preserve prior charges and all OPEN gates; retain local lemmas as conditional; resolve missing helper owner before any new lease or authority amendment. No shared record edited.
- Worker state: STOP on submission; writes end with this revision's creation. No descendants or unresolved descendant leases. This revision is frozen.
