# R22 suffix-provenance trace handoff

Sprint-ID / contract revision and SHA-256: `R22 / fixed-source-result-map-existing-semantics`; `85236a281bd8abaa90bf2b3d1a88163bfe1ad2d64a3a4113b64cd0c269eae56f`.

Assignment-ID / handoff revision: `R22-C-SUFFIX-TRACE / 1`.
Parent gate / original theorem and scope locator: `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`, still OPEN / closure 0; R22 fixed-source ResultMap remains OPEN.

Baseline / direct dependency hashes: contract pins `machine.rs fa8dab7f...`, `continuation.rs 194e925c...`, `program.rs 484967c2...`, `runtime_resume.rs 3902e507...`, R21 option `f97d6ca8...`, soundness `1e85ae26...`, falsifiers `a8814220...`. Reused R20 reviewed proof `1ab75dd2...` and R20 exact fixed-source 18/18 runtime result as recorded in the contract. R21 A/B options remain unadopted.

Role / actual worker / session / launch: Luna/high implementation assignment; worker `/root/r22_suffix_trace_impl`; active session. Exact requested model/effort: Luna/high. Observed effective model/effort: UNKNOWN (not supplied by runtime metadata).

Exact leased paths and all authors: this assignment only; authored by `/root/r22_suffix_trace_impl`:
- `tools/inference-playground/src/runtime/machine.rs` — SHA-256 `d3da831eaccd259c3ca70bf45e2731fa9ac9da21aecc3414111222e4eeeada74`
- `tools/inference-playground/src/runtime/continuation.rs` — SHA-256 `3ee284870e86761d8ac8d773baca2a28227899561db5a74eafa6616d6d524c5e`
- `tools/inference-playground/tests/runtime_resume.rs` — SHA-256 `22a710531f5f898cb4014471ec16be10642f70ba551d148033c379ed02738c6f`
- `tasks/agent-loop/inbox/20261018-fixed-source-suffix-provenance.md` — SHA-256 recorded after freeze below.

Outcome class: provisional observational implementation.

Behavior added: `Machine::suffix_provenance_debug()` exposes only bounded debug strings. Event storage is capped at 128 events and 24 KiB per event; both dropped-event and text-truncation counts are rendered. The continuation renderer records the actual template node order and retained frame kinds/source sites. Runtime observations include template/hole substitution with response handle/site, owner transitions, view entry/exit occurrence (view and receipt identities explicitly UNKNOWN because their handles are private to `Receiving`), resumed `ResumeReturn` value/site, selected operation/value Catch arm node plus body site, arm-body final value/site, exact local-g install/use handle/site where the existing runtime plan exposes them, and final completion handle/site. Unknown values/sites are emitted as UNKNOWN.

A focused `runtime_resume` case keeps the fixed local-g source and callback bodies, replaces only `k response` with `my ignored = k response; other_response`, then asserts parse/HIR-owner/candidate/static-evidence admission and records actual Machine outcome, receipt presence, and trace. It makes no runtime-outcome or receipt-success assertion and changes no acceptance policy. Existing R20 fixed-source static receipt and runtime assertions are unchanged.

Parent/source/native correspondence: no source inference, typed endpoint equation, capture rule, handler choice, runtime transition, receipt predicate, admission rule, or completed outcome was changed. This trace can expose execution facts but proves no source/native or parent theorem leg. Existing runtime code and R20 evidence were reused; no R22 variant has been executed, so its admission/outcome remain unobserved until reviewed verification.

Checks and budget: `git diff --check` passed. No tests, build, formatter, or diagnostics run, per freeze-before-review contract. Assignment cap 600s; exact active seconds are UNKNOWN. No generated/scratch outputs created by this assignment.

Provisional boundary / falsifier / cleanup owner: instrumentation remains provisional pending independent compiler review. Falsify by any changed runtime outcome, handler/owner selection, source admission, receipt result, or unbounded event storage relative to the uninstrumented execution. Luna owns any cleanup or integration decision. This worker does not self-certify.

Next related in-envelope step: freeze these four paths and submit to independent compiler review. After CLEAN, Luna may run the one exact target `cargo test -p yu-playground --test runtime_resume`; report the variant's candidate admission and actual trace/result separately from theorem status.

Mutual TODOs: proof and falsifier lanes should compare source static occurrence/arm identity with the trace's dynamic value handles/sites, preserving endpoint distinctions. The trace worker requests no lease expansion or semantic adoption.

Worker state: writes stopped; no descendants or scratch leases. Frozen review snapshot; pending independent compiler review and primary integration.
