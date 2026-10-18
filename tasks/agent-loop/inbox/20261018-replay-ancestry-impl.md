Sprint-ID / contract revision and SHA-256: `npair-replay-ancestry-authentication-20261018`, rev1, `23181fbb4511e1cc7c36fa3f28bfd6996027b04aa86bdd2f15bdda5758f7dae1`
Assignment-ID / handoff revision: replay-ancestry-impl / 1
Parent gate / original theorem and scope locator: `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`; original scope unchanged, OPEN.
Baseline / direct dependency hashes: baseline `f423047fa`; contract pins as listed in sprint rev1; conditional proof `notes/theory/2026-10-18-demand-root-transport-correspondence.md` SHA `426b1bf969eb9628b73f5bcddec38b2f169d41341479dda4019965b34fad1244`; prior implementation finding in `notes/progress/2026-10-18-demand-root-transport-closeout.md`.
Role / actual worker ID / session / launch receipt: Luna/implementer assignment; `/root/replay_ancestry_impl`; current session; launch/resume receipt from primary runtime. No descendants.
Requested model and effort / observed model and effort: Luna/high requested by pinned role. Effective runtime model/effort UNKNOWN to this worker.
Exact leased paths / authors: `crates/yu-solver/src/candidate_context.rs`, `crates/yu-solver/src/candidate_scheme.rs`, `crates/yu-solver/src/shadow_apply.rs`, `crates/yu-solver/src/tests/candidate_graph_call.rs`, `crates/yu-solver/examples/research_scoped_formal_replay.rs`, this progress note, this handoff. Author: `/root/replay_ancestry_impl`.
Outcome class: candidate; provisional source-evidence instrumentation.
Parent application: observer now authenticates exact Replay relation IDs/keys, source route and FreshUse witness, supported typed ancestry, current upper/root and ordered FunctionPort dependencies. Parent theorem closure remains 0. Remaining premise: source owner input binding the original fixed-c to the exact native source demand; see sprint's proof TODO.
Source constructors -> constraints -> propagation -> consumer/native path: accepted `invoke/id/received` HIR fixture remains intact; existing omitted-formal FreshUse and integer propagation behavior are asserted for two source uses. Instrumentation only observes ancestry and does not alter source admission or consumer behavior.
Artifact locators and byte hashes / frozen review snapshot:
- `crates/yu-solver/src/candidate_context.rs` `cde5c7368a038d77793d2d8b07e0beb400c33b83d4dd0cd689076d641ee788fb`
- `crates/yu-solver/src/candidate_scheme.rs` `1b5da9c8b34a53db04875294e03b5d03997abd78fc43145cce0742ad4a72ef03`
- `crates/yu-solver/src/shadow_apply.rs` `683928cc71f828b3536950911b8d20d5c141415300555c2271d4b790ac8d7e65`
- `crates/yu-solver/src/tests/candidate_graph_call.rs` `01dbaef3b6d6b8f7a943fe627b64ad7fa7822e5ea7f04437b9ef390f4e8eec7e`
- `crates/yu-solver/examples/research_scoped_formal_replay.rs` `e4c1bec2a41accfe09f664d5992b2575ce78b855c3ff622f08eeb6de8765e3d3`
- `notes/progress/2026-10-18-replay-ancestry-authentication.md` `4889d6318f1286af52ef6aeae24e5f0cb92c053eb30b89412916b8cf1241b92a`
Checks, coverage and budget: `git diff --check` passed. No Cargo/test/build/example command ran. Added falsifiers for sibling/mismatched Replay IDs and keys, source call/snapshot, use, root, missing route relation, and pairwise port swaps; integer propagation asserts both sibling results. Authoring consumed approximately 600 seconds of 720; 360 seconds remain protected for the exact primary runtime set. No persistent storage added; traversal scratch is allocation-free and bounded by relation count.
Next related step: fresh independent proof/compiler reviews of these exact hashes. If both are CLEAN and capacity is recorded, primary runs each of the three sprint commands once in sequence; stop on any failure or falsifier.
Mutual TODOs: proof TODO remains original native source-demand/fixed-c association; compiler reviewer should check exact Replay/FreshUse ancestry, root transitions, field parent/operation/kind correspondence, falsifiers, and observer noninterference.
Worker state / writes stopped receipt / unresolved descendant leases: STOPPED writing after this frozen handoff; no descendants or generated scratch paths.
Commit-ready milestone or pending review/integration: pending fresh independent proof/compiler review; no commit or runtime by this worker.
