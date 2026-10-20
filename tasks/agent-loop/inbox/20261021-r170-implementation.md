# R170 bounded native tuple observation — Luna implementation assignment candidate

Status: frozen implementation/source/probe result revision 3 under contract revision 6; revision 2 SHA-256 `c6b78f8725492849fe70f2e4f1286c442ab5be8a8aeb4f852dbeda85b0a0e39c` is preserved as the prior result draft, and revisions 1–5 are preserved at `20cfd4ccd`, `e9d3a1367`, `74d11fa38`, `4ff7114bd` and `4288e277c`. Rev5 returned with a minor finding that `ps` pads PGID with whitespace; rev6 strips whitespace before numeric validation. The rev6 contract and both activation handoffs received prospective CLEAN review, Luna recorded activation, and the single authorized probe completed; this outcome is frozen for independent delta review.

Contract: `tasks/agent-loop/sprints/provider-capture-incidence-20261021-r170.md`; revision 6 candidate. Revision 1 contract hash `57b517516c524839ff174f0aaf08aaa163e2a6055bb84fd61c03246522fb5234`; revision 2 hash `45092451735aea21006c46f3b1e479a2a8405b7a1a98c6ab04eec39f99409394`; revision 3 hash `9aee566e2275d065d2c85986bd78ab040bba7aaf34998ee0478a082bcfd1e3b6`.

Goal: extend R169's borrowed observation to already-retained Capture bounds/snapshots and provider-owned maps in the exact contract owners, then consume it from one Rust example over the existing `tools/inference-playground/examples/entry-computation-argument.yu` fixture. This is provisional source evidence, not a semantic consumer, inference certificate or Yulang2 coverage.

Proposed exact code leases:

- `crates/yu-solver/src/candidate_scheme.rs`
- `crates/yu-solver/src/shadow_apply.rs`
- `tools/inference-playground/examples/r170_provider_incidence.rs`

Read-only source fixture: `tools/inference-playground/examples/entry-computation-argument.yu`, SHA-256 `a81a52d582067e9d76ca41bfb946cd539cd98cc369b9b2c2a01fb0b3e0e239fd`.

Exact evidence receipts: `notes/theory/2026-10-21-r170-native-tuple.md`, this handoff, and `tasks/agent-loop/probes/20261021-r170-provider.{stdout,stderr,status}`. The single authorized in-repository Cargo run completed with probe status 0, process-group status 0 and marker-scan status 0. Stdout SHA-256 `966303fac00a6f369eeb5ee92f0049e41f7b26dc3ab2e79994fb5d1c651188bc`; stderr `53fe0c22ed791aed2a6ec369e5fe32ca70b762d433537b2c764e6586859e956a`; status `68c10920ac9b4b082ad35849d64232dd27adbe99c2c22f108f9104548d052cad`. Provider q=36/54 and captured-bound q=14/3/4/11 are observed without proving source-fact/provider/Capture/map/q incidence. No Yulang2 execution, web sample, test suite, retry, external runtime, `/tmp`, alternate checkout, nested CLI, network or background service.

Implementation result revision 3: `notes/theory/2026-10-21-r170-native-tuple.md`; revision 2 is preserved under SHA-256 `412337428fcc956523e46c970cb3800aa77c88a0dd0fb6758a77ce6f66ba2984`. Code SHA-256s are `candidate_scheme.rs` 9569e7cc2ba7152cafe1273fba279a8511fe56aa39358798f3e4586c10ede225, `shadow_apply.rs` 46959cf65e447f4c1dc3db34f1969cfa5746e8d7b86227b1b8b456ac2701ddbb, and example `r170_provider_incidence.rs` d6392dde7fc2aedd4e5c860e75f89df0217bb621598558bf99817d9cc1d5d3a4. Exact fixture pin matched. Independent code review and source/native fixture-membership review are CLEAN for the scoped §1 ignored-input/ground-return case. The fixture remains outside §6's direct formal-Name subcase, which limits the parent application.

Required implementation behavior: borrow existing retained structures only; preserve order and alternatives; expose unavailable joins explicitly; cap output; do not create solver state or alter inference. If the association requires a new owner or persistent record, stop and return the missing owner. Never label the observation a unique historical event or source-fact join unless the records establish it.

Proposed Luna allocation 1500 seconds plus one 300-second build/probe ceiling within 4800 total, no carryover. The contract's one-time invocation uses `/usr/bin/bwrap --unshare-net` with host root read-only and writes only to `target/r170/` plus exact receipts; GNU `timeout` bounds the command group and the exact managed process group is checked separately from the bounded `/proc` marker scan, and PGID whitespace is stripped before validation. Cargo runs offline and locked from the repository root. Fresh independent source/code review must CLEAN exact code and example hashes before the probe; final review remains independent of Luna. Exact source/artifact hashes, diff, command, stdout/stderr/status, noninterference limits, review and writer stop belong in the frozen result. Luna alone owns Git.
