# LEAN-CALL-STEP-TYPING-20261025/r1 outcome

Status: **FAILED_VERIFICATION / UNACCEPTED**. Baseline: `12a081b82e2a84678aab7f5d0f301cd724c72542`. Frozen contract SHA-256: `677671916d8c628ba45e2492bd799dd69436d1a9ac2ee726ed1139cf11eff8f2`.

## Candidate and first obstruction

The author froze candidate `notes/theory/lean/YulangClosure/CallStepTyping.lean` (SHA-256 `4b3b40ae3c295666470c1cda73ac38f0abdc62ea86626be58f10249092d3c3ab`) and handoff `tasks/agent-loop/inbox/20261025-call-step-typing-r1.md` (SHA-256 `cf43cda1c1d741dd0d6a02cb354af92c42a1721defb0ecc6d59d3d23ea591906`). The candidate states the exact frozen one-step preservation proposition and case-splits all 28 existing transition constructors. The author stopped before running Lean; the candidate was a proposal, not a checked proof.

Luna verified the candidate, contract, handoff, current Control outputs, accepted entry/peeling outputs, and toolchain pins before the third serialized Lean invocation. The invocation used `lake env lean -j1 -M1024`, exited 1, and produced no `CallStepTyping.olean` or `.ilean`. The complete command, input hashes, timings, and empty stdout are recorded in `tasks/agent-loop/inbox/20261025-call-step-typing-r1-verification.jsonl`.

First compiler diagnostics:

- `CallStepTyping.lean:89:70`: unknown identifier `consumer`.
- `CallStepTyping.lean:94:76`: unknown identifier `consumer`.
- `CallStepTyping.lean:131:47` and `:131:58`: unknown identifiers `effectView` and `resultView`.
- `CallStepTyping.lean:208:25` and `:208:36`: unknown identifiers `effectView` and `resultView`.

Per the frozen stop rule, Luna did not run the signature/axiom query, modify the candidate, or start a repair loop. Independent review was **NOT RUN** because the candidate did not compile. The author remains STOPPED; its candidate and handoff are frozen and unaccepted.

## Evidence and accounting

The exact-source `ControlSyntax` and `ControlTyping` preflight modules compiled successfully and their output hashes are preserved in the verification JSONL. The failed candidate invocation consumed the third of four allowed Lean invocations; the fourth was not run. No tests or Rust checks were run. The static agent-sprint checker is only tooling evidence.

Commit checkpoints: contract/state `d3a3c2819`; successful dependency preflight receipt `be623b6b5`; author lease state `d4675d980`; frozen candidate/handoff `cb997a7b3`. This outcome and the failed invocation receipt require Luna integration.

## Interpretation and remaining scope

This failure means only that this candidate does not elaborate as written against the pinned sources. It does not refute the proposition. The proposition has no accepted Lean proof in r1. The successful syntax-only `completeCallEntry_typed` result remains accepted independently.

The theorem would establish only conditional preservation for existing `CallControlStep` transitions and the existing `CallStateTyped` judgment. It would not establish progress or successor coverage; the typed `.force (.view (.delay body) occurrence)` gap remains. World, effect, receipt, source/native, original Call A/B, inference A/B, and production claims remain OPEN. r9 remains `SOURCE_INPUT_BLOCKED / UNACCEPTED`.

## Next action

Luna consults the dispatcher on the exact elaboration obstruction and a fresh bounded continuation. No repair is authorized under r1. A later packet requires its own source-pinned proposition, budget, leases, serialized verification plan, and review boundary.
