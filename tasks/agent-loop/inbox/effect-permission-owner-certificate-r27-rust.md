Sprint-ID / contract revision and SHA-256:
EFFECT-PERMISSION-OWNER-CERTIFICATE/20261030-R27; contract r1 `2cc9c8ae08a6fcbf98f237e6a1640ceb042a456a6beaadc448fa0a0308b431f0`; amendment 01 `a4a21111570cb70bfaefdef034accd84bc969b33c4edf4835749a546fdc93edb`; amendment 02 `b625cb42fc9f7e365c0df738bb8b7a269775acdd34f9cc4e1d6e8155a6400bad`; schema r2 `84187379d1a81b1965c34c027e7532198bebc4c4110eaa1c05808bada6bf6d8c`; inputs r3 `06fcdb4292b3364b9a40b75dcb9b57419ff0bfb50628d422cd5ec69ad0e5c6bc`.

Assignment-ID / handoff revision:
effect-permission-owner-certificate-r27-rust / revision 1.

Parent gate / original theorem and scope locator:
`SourceProblem.InferenceSoundness` and source-preservation claims in `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` §§1, 3, 5. This handoff is test-only source-native evidence construction, not theorem closure, native closure, or production authorization. R26 remains `CLOSED_INCOMPLETE — PREFLIGHT_REJECTED`.

Baseline / direct dependency hashes:
Detached isolated project base: `68dd3616e6b3b31cae67bd855c14d919beedde0b`; clean baseline recorded by contract: `9a74a70a32ebda716a00c7203d8e606343cf442a`. Inputs r3 hash is above; all pinned clean runtime sources were authenticated before baseline and matched their exact input pins.

Baseline command outcomes, serially executed in leased `build-target`:
- Preserved r1 callback CLI failure: status 101, elapsed 0.121s; Cargo reported ambiguous binaries (`inline_authentic_extraction`, `name_entry_trace`, `yu-playground`).
- Preserved r1 companion CLI failure: status 101, elapsed 0.019s; same binary ambiguity.
- Corrected r2 callback ordinary-entry command including `--bin yu-playground`: status 0, stdout `1`, elapsed 25.426s. The primary receipt committed in `b1a377d8c` is the durable record; callback raw stderr/resource capture and capture hash were not preserved. Primary verified only `r27-companion-baseline-r2.json` and `r27-companion-run-main-baseline-r3.json` in `build-target`, so this missing callback capture cannot be recovered there. Do not rerun against modified candidate sources.
- Corrected r2 companion `--run-module` attempt: status 0, empty stdout, elapsed 0.626s; explicitly non-result evidence, not used for the expected observation.
- Amendment-02 / inputs-r3 companion ordinary `--run main` command: status 0, stdout `23\n`, elapsed 0.645s; stderr compiler warnings (12,145 bytes); child CPU 0.595s, parent CPU 0.020s, max RSS 33,440 KiB. Full capture `build-target/r27-companion-run-main-baseline-r3.json`, SHA-256 `952606f7edca1b436ccf051d43d2afdc9d0acc85c38f2c62b1c42882be7f3ca7`.
- Earlier companion non-result full capture `build-target/r27-companion-baseline-r2.json`, SHA-256 `a1d4406c811cbd79b67fbbd4b133586d291a0d118dd089f8c6cf5be394ac1c37`.
Aggregate observed Cargo elapsed across these five invocations: 26.837s / 360s maximum. All baseline Cargo/rustc processes ended. No candidate check, test, build, or runtime was run.

Role / actual worker ID / current session / launch or resume receipt:
Implementation worker `/root/effect_permission_owner_certificate_r27_rust`; continuation was active under parent receipt commit `9a720ce4ca9f094783c7a8452090ae8658d06f93`. Current worker writes are stopped at this handoff. Requested model/effort: Luna/high. Observed model/effort: UNKNOWN (no runtime model metadata available).

Exact leased paths / authors:
Only the two Rust source files below were edited. Exact remaining leased output paths are the certificate JSON, build-target and this handoff; candidate execution gate prevented writing a runtime snapshot. No other author or descendant contributed to the Rust files.
- `isolated/ep-owner-certificate-r27/project/tools/inference-playground/src/runtime/machine.rs`, SHA-256 `24d68fa0f54e9f338188da49a96e72f413238dd70f72537da8040b6c1ee73078`.
- `isolated/ep-owner-certificate-r27/project/tools/inference-playground/src/runtime/receiving.rs`, SHA-256 `7a8eeab787f127064d5689b1ee5fbbfc409b4a307905d0f42d538f5d3d628f25`.
- `isolated/ep-owner-certificate-r27/project/receipts/owner-certificate.json`: not created. The only honest writer is the focused runtime test, which is candidate execution and remains prohibited until a fresh independent exact-hash reviewer ACCEPT and Luna's separate stage authorization.
- `isolated/ep-owner-certificate-r27/project/build-target`: baseline captures listed above; no candidate execution artifact. Files observed at depth <=2: `.rustc_info.json`, `CACHEDIR.TAG`, `debug/.cargo-lock`, `debug/yu-playground` (baseline executable), `debug/yu-playground.d`, the two companion capture JSON files. These are task-local generated scratch for primary-only hygiene.
- This handoff is the sole Rust handoff path.

Outcome class:
Provisional test-only source-native evidence instrumentation and validator construction. No claim that validators or mutations pass at runtime.

Parent application / source constructors -> generated constraints -> propagation -> consumer/native path:
The source constructor `capture_template` builds immutable `ResumeTemplate.nodes` from Hole through saved Bind/Owner/ForwardHandler/View nodes and appends the final Owner whose `inner` is the immediately preceding root; the immutable `root` is the final node index. Test-only capture evidence records the actual published handle/root, request event, source location and containing owner. `enter_template` records the actual node index supplied to immutable template lookup, pre-resolution control map, actual resolved/chosen owner, borrowed/fresh branch, prior owner, and fields of the pushed `OwnerReturn`. The test validator requires exact `(template_handle,node_index)` lookup, `node_index == capture root == nodes.len()-1`, final Owner variant, its preceding-root edge, source containing owner, real control-map resolution and exact `OwnerReturn` correspondence.

For a successful request/Catch selection, `propagate_request` records the actual operation, source, request owner, handler/arm source identity and owner, prior replayed template handles, complete live outer frame stack before CatchReturn removal, and receiving observations projected from authentic actual `(execution,view,receipt)` coordinates. `receiving.rs` projects actual observer/event, occurrence, view/receipt/value, receipt owner/slot/formal, view kind, inherited-coverage flag and request-local Grant result. The focused test runs both fixed source snippets in the test harness (callback result 1 and companion result 23), then selects the companion capture and distinct `write::ping` Catch consumer; the consumer evidence asserts exact HIR family spelling `write`, operation spelling `ping`, captured template was replayed, request/consumer owners join, and receiving observations are present.

Saved template suffix and retained outer runtime frames remain separate projections. Validators require the saved chain to match the full immutable template and terminate at the final Owner; the outer projection must exactly equal the live frame snapshot, have connected absolute indices/endpoints, and include CatchReturn, ReceiverReturn and OwnerReturn. Five mutation cases are implemented with target-present, applicable-record-changed and validator-rejected assertions: wrong positive index; deletion of required capture Owner boundary; borrowed/fresh disposition alteration; disconnected write request/consumer owner lineage; and an endpoint mutation guarding the former no-op target case.

Prior evidence reused/rejected:
R26 preflight demonstrated three defects: wrong positive node index could pass; connected ReceiverReturn/OwnerReturn boundaries could be omitted; and a purported no-op mutation could pass without changing a target. R27 addresses these at the test-only validator/mutation level. The earlier `--run-module` companion status 0/empty output is rejected as result evidence. No prior source semantics or fixtures were changed.

Artifacts / candidate status:
The test-only JSON generator emits the schema-r2 certificate only when the focused test executes. It was not executed, so the leased JSON receipt does not yet exist and no runtime claim is made for node replay, frame projection, receiving observation capture or mutation rejection. Do not manufacture this immutable-runtime snapshot from source inspection or baseline stdout. The generated `frame_projection` keeps `saved_template_suffix` and nested `retained_outer_projection` as distinct origins. The schema-required record fields are represented in the generator; runtime execution and actual JSON review remain outstanding.

Checks / coverage / omitted cases / resource budget:
Checks performed: exact baseline commands above; source inspection of constructors/consumers; review of authored test-only extraction and validators by reading the changed source; current Rust source byte hashes recorded here. No `cargo check`, `cargo test`, candidate run, formatter, or other compiler/test command was run after source edits. No Lean/Lake process overlapped baseline Cargo.
Resource charge: Rust active wall is estimated, not runtime-metered; approximately 300s spent since the 1,040s resumption receipt, with approximately 700s conservatively remaining within the 1,040s remaining assignment envelope. Cargo aggregate 26.837s / 360s. No Astra charge. Do not exceed the remaining assignment envelope. No active Cargo/rustc process is known.

Known procedural deviation:
One read-only `git diff -- tools/inference-playground/src/runtime/machine.rs tools/inference-playground/src/runtime/receiving.rs` was inadvertently run in the isolated project to inspect the already leased edits. It had no Git mutation effects; no Git mutating command was run. I stopped all further Git use and disclosed the invocation to Luna.

Open premises / review gate:
Fresh independent compiler_referee review of exact source hashes above is still required. Candidate compile/runtime/tests remain prohibited until that reviewer returns exact-hash ACCEPT and Luna records a separate explicit stage authorization. A subsequent authorized focused test must establish that the extractor runs, JSON parses and conforms to schema r2, all five mutation cases actually reject, fixed test outcomes remain 1/23, and complete projections/receiving observations are present. Raw callback r2 stderr/resource capture is unavailable; the primary receipt's stdout/status/elapsed record remains the only evidence for that route. Lean model proof and snapshot application, original source/native parent, Native Grant, RootComp reachability, conversion to earlier History, effect hygiene, soundness, principality, termination, and production remain OPEN.

Mutual TODOs:
- Rust artifact TODO (owner: Luna after exact-hash reviewer ACCEPT and separate stage authorization): authorize only the focused R27 test invocation, then preserve the generated JSON/hash and actual test status/resource evidence. Falsifier: compilation/test failure, a missing required boundary/observation, any mutation target unchanged, or schema mismatch.
- Proof/source-owner TODO (owner: Lean proof lane / primary): prove exact immutable-node lookup and complete connected-chain validation for the declared constructor model, report theorem types and full axiom audit, and apply only to authenticated snapshots after the JSON exists. Falsifier: model omits a represented constructor or proof premise cannot be tied to actual snapshot data.
- Independent review TODO (owner: fresh compiler_referee): inspect exact source hashes, schema mapping, all five mutation code paths and gate boundary; ACCEPT only if evidence claims match available runtime artifacts and missing receipt is explicitly treated as pending.

Next related in-envelope step:
Freeze the two source hashes above for fresh read-only independent review. If ACCEPT and Luna separately authorizes execution, resume only within remaining Rust envelope for the focused test and schema JSON artifact, then freeze its exact hash and resource receipt. Otherwise remain WAITING; no candidate process.

Worker state / writes stopped receipt / unresolved descendant leases:
STOPPED_WRITES at this frozen handoff. No descendants were launched. No Cargo/rustc process is known active. Exact Rust source files are frozen for review. `build-target` remains leased task-local scratch; no candidate execution occurred.

Commit-ready milestone or pending review/integration:
Frozen review target, pending exact-hash independent review. No candidate test result, JSON certificate, acceptance, integration, or Git action is claimed.
