# Sprint R315 — parser-associated multi-infix member source carrier

Status: OPEN_CONTINUATION evidence checkpoint; parent R149 remains OPEN.
Branch / baseline: `research/simple-sub-intrusion` at the R314 evidence checkpoint `ed2c517d9aa0800687279fe85c91b8f56f4c0fca`.
Authority: persistent unchanged-Yulang2-samples goal; R149; unified design §§4.1–4.5, 5.1, 6, stages 4 and 10; proof companion §§3.1–3.2, 4.5, 7.1–7.4; R308 operator owner bridge; R314 rev6.
Dispatch: serial primary because the user prohibits subagents. The next-action selector is not callable here; this degraded dispatch is recorded. No independent proof or review is claimed.

## Original outcome and this bounded step

Original outcome remains unchanged: the Yulang2 playground samples must pass ordinary tests, and their implementation plus source/native proofs must close. The immediate source obligation is the unchanged ordered-pair `Display.show` member body:

```yu
our value.show = case value:
    (a, b) -> "(" + a.show + ", " + b.show + ")"
```

R314 proved that its tuple case pattern is already represented, while its four-use infix chain is rejected because `Builder::expression` admits exactly one `InfixOperatorUse` per `OperatorChain`. Retain the exact parser-associated operator tree, operand order, source keys and imported operator provenance in a supported member `LocalSource` carrier. Do not infer an operator target from spelling, rewrite the source, type the body, select the member, or claim sample execution.

Success evidence: the exact pinned `Display.show` carrier is `Supported`; each of its four infix applications and all operands have parse-owned source identities; its tree agrees with the parser's `associate_operator_chains` result; tuple binders remain ordered; unsupported/recovered or ambiguous operator routes still fail closed. Candidate source collection currently rejects `InfixOperator`, so candidate admission, where-bound discharge, selection, runtime and proof closure remain explicit later gates.

## Lanes, premises and falsifiers

Proof/source bridge is solo primary: construct the structural correspondence from `HirExpr::Apply` to nested `LocalSourceForm::InfixOperator`, with exact owner and operand identities; compare operator node, fixity, arity, ranges and ordered operands against the parser result. Keep the bridge conditional until all nested constructors and consumers preserve it.

Implementation is solo primary: use only the exact parser association already retained by HIR and the existing R308 operator source receipt. Owners are `crates/yu-hir/src/module.rs`, `crates/yu-hir/src/module/local_source.rs`, and the focused pinned-member test in `tools/inference-playground/src/lib.rs`. Preserve current semantics and ordinary non-member lowering.

Falsifiers: any reordered operand, missing/duplicated operator use, source key outside the pinned parse, tree mismatch, changed source bytes, an operator target inferred only from its spelling, or a previously unsupported malformed/recovered chain becoming supported. Tests are focused source-formation regressions only; no full workspace suite.

## Exact write leases and limits

- `crates/yu-hir/src/module/local_source.rs`
- `crates/yu-hir/src/module.rs`
- `tools/inference-playground/src/lib.rs`
- `tasks/agent-loop/sprints/r314-display-where-bound-discharge-20261022.md` (carried attribution correction)
- `notes/theory/2026-10-22-r314-display-where-bound-discharge.md` (carried attribution correction)
- `tasks/agent-loop/current.json`
- this contract and `notes/theory/2026-10-22-r315-multi-infix-member-source-carrier.md`

Baseline hashes: `module.rs` `85ed21b065f6e608ee5ba3e5d0ae6f4a1915d699cb13493df02d9e4dc1dbe72e`; `local_source.rs` `0c59f2cc02ddf7333cd30319f50441fee68bf10307ef2367102af1cecd1cbe0d`; playground `lib.rs` `e91fc47672fd973d587ff18e97a3ba7b199c80a3bb2c0efa03ef1664252d1d5c`.

Pinned source bytes, parser crate, solver collector and all other paths are read-only. No subagents or concurrent writers. Solo cap: 1800 seconds, no carryover; at most one Cargo process and focused checks only. Stop on a genuine source-association ambiguity, missing authenticated operator identity, or exact cap. Keep global selection deferred.

## Outcome

The exact pinned ordered-pair `Display.show` member is now `Supported`. Its four nested `InfixOperator` nodes structurally match the parser-associated `HirExpr` tree, in operand order; each operator retains the exact `HirOperator` and parse-owned operator source key, and every local node retains a parse-owned source key. The regression checks exactly four applications. The earlier R314 revision 5 attribution to tuple-pattern support was corrected: the flat tuple case pattern was already supported; the actual boundary was the four-use chain.

Focused checks passed: `cargo test -p yu-hir --lib pinned_generic_say_header_and_operator_body_form_a_source_carrier`; `cargo test -p yu-playground --lib pinned_fmt_role_and_tuple_impl_keep_exact_module_and_parse_positions -- --nocapture`; `cargo test -p yu-hir --lib` (164 passed); `cargo test -p yu-playground --lib` (41 passed); and `cargo test -p yu-playground --lib unchanged_types_sample_reads_receiver_bounds_from_its_pinned_module_session -- --nocapture`. The Types sample remains `DeferredSelectionUnavailable`; `Display.say` remains unsupported, and this probe did not isolate its constructor.

This closes only source-carrier formation. Candidate collection still rejects `LocalSourceForm::InfixOperator`; no candidate scheme is assigned from operator spelling, and there is no body typing, where-bound discharge through this body, selection, runtime success, or proof closure. The next exact seam is the solver candidate-source preflight/consumer, beginning with `crates/yu-solver/src/candidate_source.rs`; lease that path only in a subsequent sprint after inspecting its exact rejection and authenticated operator receipt route.

Checkpoint this source constructor separately from candidate admission. R149, source/native proof, A/B, principality, termination, independent review and production remain OPEN.
