# R306 signed source remap — frozen handoff revision 3

Revision 3 supersedes frozen revision 2 (`2c9fe57e764e7b48a75bdc25e8b0caa9d973b4c8bc75369413907c7fa8fc398a`) after review requested an in-closure assertion that sibling events actually appear before abort. Revisions 1 and 2 remain immutable evidence.

Sprint: `R306`, `tasks/agent-loop/sprints/call-phase-descriptor-r306.md`, SHA-256 `6d469cfa40b59d33c36c2e1caaf438b15a759a0284285e5f016c08b58dbf09f5`.
Assignment: `source-signed-remap-r306`; parent `/root`; baseline `959b72274`. Requested role/model/effort: Luna implementation / `gpt-6-luna` / high. Observed model, effort and session ID: UNKNOWN in this worker's runtime metadata. No descendants. No production authority.

Outcome: **provisional, test-only source/native route evidence**. No production solver semantics changed. The instrumentation lives behind `#[cfg(test)]`, is dormant unless explicitly enabled, and is truncated by transaction rollback. It does not establish R306's parent theorem or authorize cutover.

## End-to-end behavior observed

The R305 source fixture is parsed and executed through the candidate source pipeline:

```text
act E
act tick:
    our next: ('a -> ['e] 'a) -> ('a -> [E, 'e] 'a)

my provider = tick::next
my left = provider
my right = provider
```

The retained source operation trace identifies the actual nested result `SourceEffectRow`, its HIR position, source owner and operation declaration/occurrence. Its cached Support view has the declared concrete payload `[E]`, and its tail is the actual `'e` variable row in that same operation trace.

The new test-only observation is emitted only after `Work::EffectView` itself has looked up the signed child and `candidate_remapped_effect_view` has returned successfully. Its one event for this fixture records:

```text
full source key: Key(Support(0), Positive, target=1)
source view tail: EffectRow(3)         // actual operation 'e variable
full child key:   Key(EffectRow(3), Positive, target=1)
child lookup:     EffectRow(9)          // actual rows/structure result
view_remap:       miss for (0, Some(9))
copy:             Support(2), tail EffectRow(9)
```

This same copied Support view 2 is selected by the exact slot-42 captured positive Bound under the nested result Function. Its captured tail node resolves to captured Effect row 9; the copied view's own tail is row 9. Each of the two actual `provider` FreshUse routes retains that same bound and Support operand, maps the exact tail node to its own route row, and has `Support(mapped_view)` physically present in the same mapped owner row's exact lower-bound list. Thus the evidence joins source owner/position/payload/origin and actual source tail to signed child key, actual child lookup, cache miss, exact copied view, captured bound and both retained routes. This is causal evidence from the code path, not a same-shaped-row match.

This fixture produces one real Work event and that event is a miss. There is no natural second identical `(view, copied-tail)` Work lookup in this fixture, so no cache-hit Work event is claimed. A separate test-only probe passes the authenticated source view and copied tail through the real local remap function twice, observes the same copy on reuse, and asserts that this probe adds no signed Work event. It checks cache-hit behavior without fabricating an execution event.

The signed trace is enabled for the committed `lookup` operation, and its nonempty event prefix is frozen in the test. Inside the aborting route-transaction closure, after executing `sibling`, the test asserts the trace length exceeds that committed prefix. After the closure aborts, rollback preserves the committed prefix exactly and removes the transient sibling events. A retry then appends fresh signed events while keeping that same prefix. A dormant session leaves the signed trace `None` before and after source execution, so no trace allocation or cross-session state is retained.

The existing injected `fail_after_view` failure occurs during source view construction, before a signed `Work::EffectView` event can be emitted; its empty trace proves only that this pre-event failure fabricates no event. No injected late failure after signed-event publication is available or claimed. Outer transaction abort does prove truncation after real events were observed, as above. The successful source constructor continues to publish its normal operation trace. Production semantics, diagnostics, source domains, and inference rules are unchanged.

## Parent/source/native correspondence and limits

This advances R305's missing owner edge from the source effect row through `candidate_extrude::Work::EffectView` to its full signed child `Key`, actual row/structure lookup, local remap miss and copied Support that enters slot-42 capture and both FreshUse maps. It follows the source-to-generated-constraint-to-propagation-to-capture/use path for this concrete fixture.

It is not a proof of R159 or of EI-Form/EI-All/EI-Intro. It does not instantiate the R304 NativeContextTables, encode arbitrary independent W/Z arms or laws, prove source/native semantic correspondence for the full source domain, or close Checking/logical admission. R305's constructor-disjointness theorem remains only its narrow checked lemma. The production/native parent edge and independent source review remain open.

## Prior evidence reused and rejected

Reused the R305 operation emission/capture/FreshUse test and its exact source-owner joins: actual HIR row position, `'e` constructor variable, operation provenance, slot-42 rewritten Function path, captured Support bound, and each route's effect-operand/rows maps plus physical lower-bound membership.

Rejected raw tail equality, guessed declaration root positions, node-index joins, and shape-only matching from prior attempts. Here `3 -> 9` is asserted only because the new event records the actual signed child lookup result and the exact copied Support subsequently appears in the captured Bound and retained routes. No Simple-sub bypass was restored.

## Artifacts, hashes and checks

Changed leased source files:

- `crates/yu-solver/src/candidate_extrusion.rs` — SHA-256 `57e8c5de11f60172351ec8e4bdf2343e79571343e5e8132adcdd2c0175bbd83b`.
- `crates/yu-solver/src/candidate_effect.rs` — SHA-256 `aeea54f55922cc6f15837a4533e63d21523ef88abfcd604b503b80cfd11bc20b`.

Read-only direct inputs rechecked:

- sprint contract `call-phase-descriptor-r306.md`: `6d469cfa40b59d33c36c2e1caaf438b15a759a0284285e5f016c08b58dbf09f5`.
- governing design `2026-10-24-computed-call-result-constructor.md`: `2f3a5461b6dacaa29e881ba8b3003120b912e441dd5e4c47fc4ccaa27d3b31a6`.
- `candidate_scheme.rs`: `6072c73bc1a1629f025dcaf61fcbed98c738d93f8993bd81182a391d1ad4d89e` (matches R305 dependency).
- `lib.rs`: `429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be` (matches R305 dependency).

Focused offline locked checks, isolated target directory:

```text
CARGO_TARGET_DIR=/tmp/yulang-r306-cargo cargo test -p yu-solver --lib --features shadow-apply-candidate operation_ --locked --offline
CARGO_TARGET_DIR=/tmp/yulang-r306-cargo cargo test -p yu-solver --lib --features shadow-apply-candidate operation_constructor_trace_is_session_owned_transactional_and_provisional --locked --offline
```

Both exit 0. The `operation_` check runs 11 unit tests (822 filtered), including source/capture/FreshUse propagation. The transactional test was rerun after adding the in-closure `len() > committed_prefix.len()` assertion; it runs 1 test (832 filtered) and confirms an event is transiently present before abort, rollback restores the prefix, retry appends, dormant state remains `None`, and the pre-event injected failure limitation stated above. Existing repository warnings remain; no full suite was run.

During implementation, the first compile exposed a `usize`/`u64` trace-field mismatch, corrected to `usize`. The first isolated cache probe hit the method's caller-reserved-capacity invariant; explicitly reserving one map entry made the probe obey the production caller contract. Neither issue altered solver behavior.

## Boundary, resources and stop

The instrumentation is explicitly provisional; Luna owns independent review and cleanup/adjudication. Passing checks do not prove a theorem or authorize cutover. Exact handoff output is this file only; its hash is to be computed after write. Known disposable scratch: `/tmp/yulang-r306-cargo/` (Cargo target artifacts). No other generated paths are known. No Git command, child process, manifest/lockfile edit or unleased path write was used. No whole-workspace formatter or full-suite run.

Reserved bound: 1500 seconds; observed elapsed/peak RSS are UNKNOWN, so report no fabricated measurement. Worker state: WRITES STOPPED; no Cargo process remains. This worker does not self-certify.

Next related in-envelope step: Luna's fresh implementation review should verify the frozen signed event against the exact `Work::EffectView` branch and adjudicate the provisional instrument. The only missing hit-side evidence is a naturally repeated identical local view/tail lookup within this same source-to-route execution; this handoff claims the actual miss plus a clearly separate real-method reuse probe, not such a source event. Preserve the R306 proof lane's open independent-arm/source-native premises.
