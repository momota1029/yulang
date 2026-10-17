# Durable capture of receive-applied Replay observation

Sprint `npair-replay-durable-capture-20261018`, contract SHA-256 `ec72f581fd6e3857bb3181996da605d0638c3d739960d976093872e2ea77e76b`, baseline `551773b8692540a55f69014c2194ff081331b2cb`.

After fresh independent preflight review returned CLEAN and Luna explicitly released the run, the unchanged reviewed harness was invoked exactly once with the contract command and direct stdout/stderr redirection. No retry, pipeline, filtering, compiler edit, fixture edit or expected-output edit occurred.

- Command: `timeout 120s env YU_CALL_REPLAY_OBSERVER=1 cargo run --offline --manifest-path crates/yu-solver/Cargo.toml --example research_source_registration --features shadow-apply-candidate`
- Working directory: `/home/momota1029/rust/yulang`
- Environment: `YU_CALL_REPLAY_OBSERVER=1`
- Start/end: `2026-10-17 23:20:14 UTC` / `2026-10-17 23:20:20 UTC`
- Exit: `0`
- stdout: 79,315 bytes; SHA-256 `5bb1dd3bcbabd97bb94fca9a12fdc17a882d1c9a916c692fe55f1a302984d311`
- stderr: 1,986 bytes; SHA-256 `9a56194c1d4734309880847cd18ee2a9a0dab194815b0a40aad2378a5448f7e9`
- metadata: `tasks/agent-loop/runtime/20261018-receive-applied-durable.meta.json`; SHA-256 `142edef3b35d58279421013c44e81ac96ac8123be50ab4e75186824f583ca2ad`

The complete capture is frozen. This runtime packet does not classify any observer row. Attribution is delegated to the proof lane, which must join the Replay `call` index to authenticated `candidate.source_call[index]`, match the native root, and verify ordered endpoint flags. Fresh independent final review is pending. The parent `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` remains OPEN; original theorem conditions closed: 0.
