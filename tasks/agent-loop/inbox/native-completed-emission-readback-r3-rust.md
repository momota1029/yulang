# Frozen Rust handoff — NATIVE-COMPLETED-EMISSION-READBACK/r3

Sprint / contract revision and SHA-256: NATIVE-COMPLETED-EMISSION-READBACK/r3; `tasks/agent-loop/sprints/native-completed-emission-readback-20261028-r3.md`; `d1c194c85c54d7ea2016c64e60d51d7805e480ae7c824b167f0bc86fee94d71e`.

Assignment / handoff: `NATIVE-COMPLETED-EMISSION-READBACK/r3-RUST`; revision 1 (frozen on write; handoff SHA is reported by the author message after hashing).

Parent gate: original `YulangClosure.SourceProblem.InferenceSoundness`, all quantifiers and supported-source domain preserved; whole-language parent remains OPEN. This is provisional source/native evidence only.

Baseline / direct dependencies: research workspace base `bc2a0836ec8fc9dee6a1094552a3dd34cfbcfd0d`; source overlays remain contract-pinned. Relevant direct context source is unchanged at SHA-256 `57114491a4b1333f30e3ad68cb6e1c8a5c735e2d142c1456745eaef8ed56f30e`. No dependency or lockfile changes.

Role / worker / session / active-work receipt: registered Rust implementation packet worker `/root/native_completed_emission_readback_r3_rust`; current agent session. ACK and active-work receipt sent to Luna before reading source/artifact bodies. Requested model/effort Luna/high; observed model/effort UNKNOWN because runtime metadata is not exposed to this worker.

Exact write leases: `isolated/native-completed-emission-readback-r3/crates/yu-solver/src/candidate_scheme.rs`; `isolated/native-completed-emission-readback-r3/crates/yu-solver/src/candidate_extrusion.rs`; this handoff file only. No descendants, generated files or scratch paths created.

Outcome class: provisional source-native evidence / implementation candidate.

Changes frozen:

- `candidate_scheme.rs` SHA-256 `75242b9bdf8aad67938501bd4a06f5202a65675da694ab77a80b77592076c83c`: test-only `GraphState` recorder stores the restoration `ReplayOperationId` and exact `BoundEmissionId` returned by the completed driver. The scoped duplicate-use test now joins selected FreshUse emissions to those driver returns and checks distinct invocation/emission ownership, mapped/admitted relation equality, completed flow and transformer lookup, and a post-driver addressed-slot reread. The same existing test includes antecedent, route/use/root/relation, emission reassociation, flow and slot-address mutation assertions.
- `candidate_extrusion.rs` SHA-256 `abf8ffd0624f7553acc186e232c42623ba99a9cce49102e54bc7e2d3d8ea1817`: added a `#[cfg(test)]` wrapper around the existing private physical-slot reader, plus test-only native-slot corruption/readback/restoration. The actual driver return is recorded only under `cfg(test)`; production behavior and API are untouched.
- Added an unscoped duplicate-call fixture requiring logical identity transformer root `0`, absence of scoped demand, actual driver-returned emission IDs, current admissions/relations and physical slot readback. Its assertions are source artifacts only until the fresh review and authorized focused check.

Source → native correspondence: source fixture creates repeated `f`/`invoke` uses; candidate collection creates FreshUse constraints and relation IDs; the candidate driver returns emission identity; completed context resolves emission → admission → mapped/admitted relation → current flow and raw transformer; the test wrapper calls the existing reader on the addressed physical value/effect bound vector. The test corruption helper changes one actual vector element, reads through that same private reader, then restores it. Root `0` is handled as identity without indexing the raw transformer table.

Authentic witness / mutation status: source code now requires scoped duplicate module/local FreshUse routes and unscoped duplicate calls. The scoped test has explicit baseline joins and assertions for antecedent alteration, emission reassociation, mapped/admitted pairing, duplicate ownership, flow transformer/root, and slot address. The unscoped test explicitly checks actual slot corruption changes the reader output and is restored, and requires a mapped FreshUse admission. These are unexecuted assertions, not observed passing witnesses. No required case is intentionally skipped in the new assertions. Root-cause coverage is provisional because the existing authentication mutations still exercise the pre-existing constructor evidence consumer; the newly added completed-reader assertions have not yet been run against mutations at the new join seam.

Prior evidence reused / rejected: reused the R2 scoped duplicate-use fixture and its route, admission and mutation hooks. Rejected R2's constructor-after-append `PhysicalBoundReadback` alone as proof of completed readback: the new test code records actual driver returns and rereads current native vectors afterward. R1/R2 remain CLOSED_INCOMPLETE; no provisional output was restored as source input.

Checks / resources: none run, by the contract review gate and Luna's non-waivable R3 disposition. No Cargo, Lean, tests, builds, static checks or Git commands. Grant: 1,200 active seconds; actual elapsed and remaining seconds are UNKNOWN (no active-time meter observed). Astra allocation 0 by contract. No runtime output retained. No resource renewal requested.

Unresolved premises / TODOs: (1) Fresh independent source review and, only after acceptance, focused Cargo evidence remain required. (2) Validate whether the new completed-readback join itself rejects every named mutation, especially mutation at the mapped/admitted relation join; no passing test evidence exists. (3) Lean lane's source-read deviation is non-waivable, so no source-to-Lean preservation theorem or parent application is claimed. Stable request `NATIVE-COMPLETED-EMISSION-READBACK-R3-RUST-TODO-1`: owner Luna / future authorized Rust packet; first missing evidence is reviewed and executed mutation coverage at the completed driver-return/readback join, with no semantic changes; falsifier is any altered antecedent, emission, mapped/admitted pair, duplicate association, flow root or addressed slot accepted by that join.

Provisional boundary / cleanup owner: all new instrumentation is `cfg(test)` and unreviewed. Luna owns any later cutover or cleanup decision; no cutover, production readiness, theorem closure, semantic approval or expected-output change is claimed.

Next related in-envelope step: none for this worker after this freeze. Luna may close R3 incomplete as directed and preserve the bytes as provisional evidence; fresh review/checks are not authorized by this handoff.

Worker state / writes-stopped receipt: STOPPED after writing and hashing this one frozen handoff; no source reads or writes after the primary's stop direction. No descendants or unresolved writer leases. Primary-only hygiene: only the two exact Rust artifacts and this handoff path changed; no disposable scratch remains.
