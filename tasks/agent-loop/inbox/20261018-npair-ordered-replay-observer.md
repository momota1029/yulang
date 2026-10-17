Sprint-ID / contract revision and SHA-256:
npair-original-c-compatibility-20261018, rev2, a48ee14722783e6598e782e405e880f9efe14ae8f5558bb0369834ea01d4affd

Assignment-ID / handoff revision:
npair-ordered-replay-observer / 1

Parent gate / original theorem and scope locator:
CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017; original conditions unchanged, parent OPEN, closure 0.

Baseline / direct dependency hashes:
Baseline 29a7ace306cca2b3959ed752c859125b01f89543.
candidate_context base pin 72da8a6e7b3f04ed3f7054b6151410c7d2b35f9f91b756ade1f6f008244c1ce6.
shadow_apply base pin bb1e63c2ea33bf0b6e7408bd015d2498a9aed4dd45e250a85433169c9da334bf.
Harness base pin f5c61bd5a4515545fad49bfc24158ef235c6ac2ebc6f00e15daabade394e79ad.
All frozen direct contract dependencies and all three implementation source pins were verified.

Role / actual worker / session / launch:
Luna typed Replay observer, /root/npair_native_demand_children, current-session. Start 2026-10-17 21:28:39 UTC; cap420s.

Requested model/effort / observed:
Luna/high / UNKNOWN/UNKNOWN.

Exact leased paths / authors:
crates/yu-solver/src/candidate_context.rs; crates/yu-solver/src/shadow_apply.rs; crates/yu-solver/examples/research_source_registration.rs; notes/progress/2026-10-18-npair-ordered-replay-observer.md; tasks/agent-loop/inbox/20261018-npair-ordered-replay-observer.md. Sole author /root/npair_native_demand_children; descendants0.

Outcome:
Provisional typed observer prototype, independently compiler-reviewed CLEAN on exact code hashes. Private allocation-free iterator scans each retained Dependency::Replay once and yields one row per Replay child resolving to ScopedDemand. The row joins ScopedDemand.original_call to indexed candidate_calls and checks native demand root; reports exact child/lower/upper RelationIds and ordered lower_input/upper_input BoundKeys, with actual bound_pair checks for both endpoint relations. Rows stream under YU_CALL_REPLAY_OBSERVER; no first/aggregate selection, Debug parsing, new public API/storage, or solver/admission change.

Coverage boundary:
Observer output is complete only over Replay dependencies whose child resolves to typed ScopedDemand. No-demand Replays are omitted and not counted. Stderr truncation means absence of a row cannot establish absence/completeness. No semantic Replay/T_rho/At/original-c/N-Transport/F1/FK1 or parent claim.

Source -> constraints -> propagation -> consumer/native:
Existing exact source_call authentication remains in harness (owner, Apply occurrence/source keys, scope, checking occurrence/cause). Internal scoped demand carries call index; Replay child and ordered bound inputs are retained typed data. This observer reports structural identities only.

Frozen exact code hashes:
candidate_context.rs 46f0b74c8aa942c629a456272c3ae601827f1794b25d7034479edee62bc13e4f
shadow_apply.rs d29d5f6488b5824eef5dc7902b70351b5bfae1ae3d7d014ec3629267443dbc83
research_source_registration.rs d76cbae29f5f095ffdb5068a49556149fe4a0fcc0f5d0702ff17ad71aed35f28

Review:
Fresh independent compiler review CLEAN against the exact hashes above. It confirmed the typed join, O(dependency-count) scan with constant extra storage, opt-in output, no API or solver semantic changes; stderr truncation caveat retained.

Checks / runtime:
No Cargo/build/test/probe. The one command was not started because the measured cap remaining was below the contract's 120s minimum. No command receipt exists. No fixture edit, no scratch.

Parent application / remaining premise:
This gives implementation-level structural observation only. Original fixed-c compatibility proof remains independent and open; no parent conditions close.

Next in-envelope step:
If a later assignment permits runtime evidence and enough measured resources, run the single contract-authorized focused harness command with YU_CALL_REPLAY_OBSERVER=1 after exact-byte review remains current. A missing stderr row is not a falsifier due truncation; do not claim completeness across no-demand Replays.

Worker stop:
Writes stopped after freezing this handoff and progress note. No descendants, scratch or pending process.
